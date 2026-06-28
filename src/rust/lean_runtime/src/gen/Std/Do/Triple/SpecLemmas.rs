// Lean compiler output
// Module: Std.Do.Triple.SpecLemmas
// Imports: Std.Do.Triple.Basic Init.Data.Range.Polymorphic.Iterators Init.Data.Range.Polymorphic Init.Data.Slice.Array Init.While Init.Internal.Order.While Init.Data.Iterators.Lemmas.Combinators.FilterMap Init.Data.Range Init.Data.Iterators.Lemmas Init.Data.List.Nat.Range Init.Data.List.Nat.TakeDrop Init.Data.List.Range Init.Data.List.TakeDrop Init.Data.Nat.Mod Init.Data.Slice.Lemmas Init.Omega Init.Data.String.Defs Init.Data.String.Iterate Init.Data.String.Lemmas.Splits Init.Data.String.Termination Init.Data.String.Lemmas.Iterate
use crate::r#gen::Init::Data::Iterators::Lemmas::Combinators::FilterMap::{
    initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap,
    runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::{
    initialize_Init_Data_Iterators_Lemmas, runtime_initialize_Init_Data_Iterators_Lemmas,
};
use crate::r#gen::Init::Data::List::Basic::{
    l_List_appendTR___redArg, l_List_drop___redArg, l_List_range_x27TR_go, l_List_take___redArg,
};
use crate::r#gen::Init::Data::List::Nat::Range::{
    initialize_Init_Data_List_Nat_Range, runtime_initialize_Init_Data_List_Nat_Range,
};
use crate::r#gen::Init::Data::List::Nat::TakeDrop::{
    initialize_Init_Data_List_Nat_TakeDrop, runtime_initialize_Init_Data_List_Nat_TakeDrop,
};
use crate::r#gen::Init::Data::List::Range::{
    initialize_Init_Data_List_Range, runtime_initialize_Init_Data_List_Range,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Data::Nat::Mod::{
    initialize_Init_Data_Nat_Mod, runtime_initialize_Init_Data_Nat_Mod,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Data::Range::Polymorphic::{
    initialize_Init_Data_Range_Polymorphic, runtime_initialize_Init_Data_Range_Polymorphic,
};
use crate::r#gen::Init::Data::Range::{
    initialize_Init_Data_Range, runtime_initialize_Init_Data_Range,
};
use crate::r#gen::Init::Data::Slice::Array::{
    initialize_Init_Data_Slice_Array, runtime_initialize_Init_Data_Slice_Array,
};
use crate::r#gen::Init::Data::Slice::Lemmas::{
    initialize_Init_Data_Slice_Lemmas, runtime_initialize_Init_Data_Slice_Lemmas,
};
use crate::r#gen::Init::Data::String::Defs::{
    initialize_Init_Data_String_Defs, runtime_initialize_Init_Data_String_Defs,
};
use crate::r#gen::Init::Data::String::Iterate::{
    initialize_Init_Data_String_Iterate, runtime_initialize_Init_Data_String_Iterate,
};
use crate::r#gen::Init::Data::String::Lemmas::Iterate::{
    initialize_Init_Data_String_Lemmas_Iterate, runtime_initialize_Init_Data_String_Lemmas_Iterate,
};
use crate::r#gen::Init::Data::String::Lemmas::Splits::{
    initialize_Init_Data_String_Lemmas_Splits, runtime_initialize_Init_Data_String_Lemmas_Splits,
};
use crate::r#gen::Init::Data::String::Termination::{
    initialize_Init_Data_String_Termination, runtime_initialize_Init_Data_String_Termination,
};
use crate::r#gen::Init::Internal::Order::While::{
    initialize_Init_Internal_Order_While, runtime_initialize_Init_Internal_Order_While,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom, l_List_get___redArg,
    l_List_lengthTR___redArg,
};
use crate::r#gen::Init::While::{initialize_Init_While, runtime_initialize_Init_While};
use crate::r#gen::Std::Do::PostCond::l_Std_Do_PostShape_args;
use crate::r#gen::Std::Do::SPred::Laws::l_Std_Do_SVal_evalsTo___redArg;
use crate::r#gen::Std::Do::SPred::SPred::{
    l_Std_Do_SPred_and, l_Std_Do_SPred_exists___redArg, l_Std_Do_SPred_or,
    l_Std_Do_SPred_pure___redArg,
};
use crate::r#gen::Std::Do::Triple::Basic::{
    initialize_Std_Do_Triple_Basic, runtime_initialize_Std_Do_Triple_Basic,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_div, lean_nat_mul,
    lean_nat_sub,
};
pub static l_List_Cursor_current___auto__1___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_List_Cursor_current___auto__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_Cursor_current___auto__1___closed__1_value: crate::leanh::LeanStringObject<7> =
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
static mut l_List_Cursor_current___auto__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_Cursor_current___auto__1___closed__2_value: crate::leanh::LeanStringObject<7> =
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
static mut l_List_Cursor_current___auto__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_Cursor_current___auto__1___closed__3_value: crate::leanh::LeanStringObject<10> =
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
static mut l_List_Cursor_current___auto__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_List_Cursor_current___auto__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_Cursor_current___auto__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_Cursor_current___auto__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_List_Cursor_current___auto__1___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__3_value)
                as *mut crate::leanh::LeanObject,
            8504843326314613972 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_Cursor_current___auto__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_Cursor_current___auto__1___closed__5_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_List_Cursor_current___auto__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_Cursor_current___auto__1___closed__6_value: crate::leanh::LeanStringObject<19> =
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
static mut l_List_Cursor_current___auto__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_List_Cursor_current___auto__1___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_Cursor_current___auto__1___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__7_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_List_Cursor_current___auto__1___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__7_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_List_Cursor_current___auto__1___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__7_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__6_value)
                as *mut crate::leanh::LeanObject,
            17228437386856258271 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_Cursor_current___auto__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_Cursor_current___auto__1___closed__8_value: crate::leanh::LeanStringObject<5> =
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
static mut l_List_Cursor_current___auto__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_Cursor_current___auto__1___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__8_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_Cursor_current___auto__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_Cursor_current___auto__1___closed__10_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            116, 97, 99, 116, 105, 99, 71, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116,
            105, 99, 0,
        ],
    };
static mut l_List_Cursor_current___auto__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_Cursor_current___auto__1___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__10_value)
                as *mut crate::leanh::LeanObject,
            3731765604234633101 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_List_Cursor_current___auto__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_Cursor_current___auto__1___closed__12_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            103, 101, 116, 95, 101, 108, 101, 109, 95, 116, 97, 99, 116, 105, 99, 0,
        ],
    };
static mut l_List_Cursor_current___auto__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_Cursor_current___auto__1___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_List_Cursor_current___auto__1___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_Cursor_current___auto__1___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_Cursor_current___auto__1___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_Cursor_current___auto__1___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_Cursor_current___auto__1___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_Cursor_current___auto__1___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_Cursor_current___auto__1___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_Cursor_current___auto__1___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_Cursor_current___auto__1___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_Cursor_current___auto__1___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_Cursor_current___auto__1___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_Cursor_current___auto__1___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_Cursor_current___auto__1___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_Cursor_current___auto__1___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_Cursor_current___auto__1___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_Cursor_current___auto__1___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_Cursor_current___auto__1___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_Cursor_current___auto__1___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_List_Cursor_current___auto__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_List_Cursor_tail___auto__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_Legacy_Range_toList(
    mut v_r_464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_start_465_ = crate::leanh::lean_ctor_get(v_r_464_, 0);
    v_stop_466_ = crate::leanh::lean_ctor_get(v_r_464_, 1);
    v_step_467_ = crate::leanh::lean_ctor_get(v_r_464_, 2);
    v___x_468_ = lean_nat_sub(v_stop_466_, v_start_465_);
    v___x_469_ = lean_nat_add(v___x_468_, v_step_467_);
    crate::leanh::lean_dec(v___x_468_);
    v___x_470_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_471_ = lean_nat_sub(v___x_469_, v___x_470_);
    crate::leanh::lean_dec(v___x_469_);
    v___x_472_ = lean_nat_div(v___x_471_, v_step_467_);
    crate::leanh::lean_dec(v___x_471_);
    v___x_473_ = lean_nat_mul(v_step_467_, v___x_472_);
    v___x_474_ = lean_nat_add(v_start_465_, v___x_473_);
    crate::leanh::lean_dec(v___x_473_);
    v___x_475_ = crate::leanh::lean_box(0);
    v___x_476_ = l_List_range_x27TR_go(v_step_467_, v___x_472_, v___x_474_, v___x_475_);
    return v___x_476_;
}
pub unsafe fn l_Std_Legacy_Range_toList___boxed(
    mut v_r_477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_478_ = l_Std_Legacy_Range_toList(v_r_477_);
    crate::leanh::lean_dec_ref(v_r_477_);
    return v_res_478_;
}
pub unsafe fn l_List_Cursor_at___redArg(
    mut v_l_479_: *mut crate::leanh::LeanObject,
    mut v_n_480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_l_479_);
    v___x_481_ = l_List_take___redArg(v_n_480_, v_l_479_);
    v___x_482_ = l_List_drop___redArg(v_n_480_, v_l_479_);
    crate::leanh::lean_dec(v_l_479_);
    v___x_483_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_483_, 0, v___x_481_);
    crate::leanh::lean_ctor_set(v___x_483_, 1, v___x_482_);
    return v___x_483_;
}
pub unsafe fn l_List_Cursor_at(
    mut v_00_u03b1_484_: *mut crate::leanh::LeanObject,
    mut v_l_485_: *mut crate::leanh::LeanObject,
    mut v_n_486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_487_ = l_List_Cursor_at___redArg(v_l_485_, v_n_486_);
    return v___x_487_;
}
pub unsafe fn l_List_Cursor_begin___redArg(
    mut v_l_488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_489_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_490_ = l_List_Cursor_at___redArg(v_l_488_, v___x_489_);
    return v___x_490_;
}
pub unsafe fn l_List_Cursor_begin(
    mut v_00_u03b1_491_: *mut crate::leanh::LeanObject,
    mut v_l_492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_493_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_494_ = l_List_Cursor_at___redArg(v_l_492_, v___x_493_);
    return v___x_494_;
}
pub unsafe fn l_List_Cursor_end___redArg(
    mut v_l_495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_496_ = l_List_lengthTR___redArg(v_l_495_);
    v___x_497_ = l_List_Cursor_at___redArg(v_l_495_, v___x_496_);
    return v___x_497_;
}
pub unsafe fn l_List_Cursor_end(
    mut v_00_u03b1_498_: *mut crate::leanh::LeanObject,
    mut v_l_499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_500_ = l_List_lengthTR___redArg(v_l_499_);
    v___x_501_ = l_List_Cursor_at___redArg(v_l_499_, v___x_500_);
    return v___x_501_;
}
pub unsafe fn _init_l_List_Cursor_current___auto__1___closed__13() -> *mut crate::leanh::LeanObject
{
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_526_ = l_List_Cursor_current___auto__1___closed__12;
    v___x_527_ = l_Lean_mkAtom(v___x_526_);
    return v___x_527_;
}
pub unsafe fn _init_l_List_Cursor_current___auto__1___closed__14() -> *mut crate::leanh::LeanObject
{
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_528_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_Cursor_current___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_List_Cursor_current___auto__1___closed__13_once),
        _init_l_List_Cursor_current___auto__1___closed__13,
    );
    v___x_529_ = l_List_Cursor_current___auto__1___closed__5;
    v___x_530_ = lean_array_push(v___x_529_, v___x_528_);
    return v___x_530_;
}
pub unsafe fn _init_l_List_Cursor_current___auto__1___closed__15() -> *mut crate::leanh::LeanObject
{
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_531_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_Cursor_current___auto__1___closed__14),
        core::ptr::addr_of_mut!(l_List_Cursor_current___auto__1___closed__14_once),
        _init_l_List_Cursor_current___auto__1___closed__14,
    );
    v___x_532_ = l_List_Cursor_current___auto__1___closed__11;
    v___x_533_ = crate::leanh::lean_box(2);
    v___x_534_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_534_, 0, v___x_533_);
    crate::leanh::lean_ctor_set(v___x_534_, 1, v___x_532_);
    crate::leanh::lean_ctor_set(v___x_534_, 2, v___x_531_);
    return v___x_534_;
}
pub unsafe fn _init_l_List_Cursor_current___auto__1___closed__16() -> *mut crate::leanh::LeanObject
{
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_535_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_Cursor_current___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_List_Cursor_current___auto__1___closed__15_once),
        _init_l_List_Cursor_current___auto__1___closed__15,
    );
    v___x_536_ = l_List_Cursor_current___auto__1___closed__5;
    v___x_537_ = lean_array_push(v___x_536_, v___x_535_);
    return v___x_537_;
}
pub unsafe fn _init_l_List_Cursor_current___auto__1___closed__17() -> *mut crate::leanh::LeanObject
{
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_538_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_Cursor_current___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_List_Cursor_current___auto__1___closed__16_once),
        _init_l_List_Cursor_current___auto__1___closed__16,
    );
    v___x_539_ = l_List_Cursor_current___auto__1___closed__9;
    v___x_540_ = crate::leanh::lean_box(2);
    v___x_541_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_541_, 0, v___x_540_);
    crate::leanh::lean_ctor_set(v___x_541_, 1, v___x_539_);
    crate::leanh::lean_ctor_set(v___x_541_, 2, v___x_538_);
    return v___x_541_;
}
pub unsafe fn _init_l_List_Cursor_current___auto__1___closed__18() -> *mut crate::leanh::LeanObject
{
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_542_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_Cursor_current___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_List_Cursor_current___auto__1___closed__17_once),
        _init_l_List_Cursor_current___auto__1___closed__17,
    );
    v___x_543_ = l_List_Cursor_current___auto__1___closed__5;
    v___x_544_ = lean_array_push(v___x_543_, v___x_542_);
    return v___x_544_;
}
pub unsafe fn _init_l_List_Cursor_current___auto__1___closed__19() -> *mut crate::leanh::LeanObject
{
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_545_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_Cursor_current___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_List_Cursor_current___auto__1___closed__18_once),
        _init_l_List_Cursor_current___auto__1___closed__18,
    );
    v___x_546_ = l_List_Cursor_current___auto__1___closed__7;
    v___x_547_ = crate::leanh::lean_box(2);
    v___x_548_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_548_, 0, v___x_547_);
    crate::leanh::lean_ctor_set(v___x_548_, 1, v___x_546_);
    crate::leanh::lean_ctor_set(v___x_548_, 2, v___x_545_);
    return v___x_548_;
}
pub unsafe fn _init_l_List_Cursor_current___auto__1___closed__20() -> *mut crate::leanh::LeanObject
{
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_549_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_Cursor_current___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_List_Cursor_current___auto__1___closed__19_once),
        _init_l_List_Cursor_current___auto__1___closed__19,
    );
    v___x_550_ = l_List_Cursor_current___auto__1___closed__5;
    v___x_551_ = lean_array_push(v___x_550_, v___x_549_);
    return v___x_551_;
}
pub unsafe fn _init_l_List_Cursor_current___auto__1___closed__21() -> *mut crate::leanh::LeanObject
{
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_552_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_Cursor_current___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_List_Cursor_current___auto__1___closed__20_once),
        _init_l_List_Cursor_current___auto__1___closed__20,
    );
    v___x_553_ = l_List_Cursor_current___auto__1___closed__4;
    v___x_554_ = crate::leanh::lean_box(2);
    v___x_555_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_555_, 0, v___x_554_);
    crate::leanh::lean_ctor_set(v___x_555_, 1, v___x_553_);
    crate::leanh::lean_ctor_set(v___x_555_, 2, v___x_552_);
    return v___x_555_;
}
pub unsafe fn _init_l_List_Cursor_current___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_556_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_Cursor_current___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_List_Cursor_current___auto__1___closed__21_once),
        _init_l_List_Cursor_current___auto__1___closed__21,
    );
    return v___x_556_;
}
pub unsafe fn l_List_Cursor_current___redArg(
    mut v_c_557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_suffix_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_suffix_558_ = crate::leanh::lean_ctor_get(v_c_557_, 1);
    v___x_559_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_560_ = l_List_get___redArg(v_suffix_558_, v___x_559_);
    return v___x_560_;
}
pub unsafe fn l_List_Cursor_current___redArg___boxed(
    mut v_c_561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_562_ = l_List_Cursor_current___redArg(v_c_561_);
    crate::leanh::lean_dec_ref(v_c_561_);
    return v_res_562_;
}
pub unsafe fn l_List_Cursor_current(
    mut v_00_u03b1_563_: *mut crate::leanh::LeanObject,
    mut v_l_564_: *mut crate::leanh::LeanObject,
    mut v_c_565_: *mut crate::leanh::LeanObject,
    mut v_h_566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_567_ = l_List_Cursor_current___redArg(v_c_565_);
    return v___x_567_;
}
pub unsafe fn l_List_Cursor_current___boxed(
    mut v_00_u03b1_568_: *mut crate::leanh::LeanObject,
    mut v_l_569_: *mut crate::leanh::LeanObject,
    mut v_c_570_: *mut crate::leanh::LeanObject,
    mut v_h_571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_572_ = l_List_Cursor_current(v_00_u03b1_568_, v_l_569_, v_c_570_, v_h_571_);
    crate::leanh::lean_dec_ref(v_c_570_);
    crate::leanh::lean_dec(v_l_569_);
    return v_res_572_;
}
pub unsafe fn _init_l_List_Cursor_tail___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_573_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_Cursor_current___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_List_Cursor_current___auto__1___closed__21_once),
        _init_l_List_Cursor_current___auto__1___closed__21,
    );
    return v___x_573_;
}
pub unsafe fn l_List_Cursor_tail___redArg(
    mut v_s_574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_prefix_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suffix_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_580_: u8 = 0;
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_591_: u8 = 0;
    let mut v_unused_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_prefix_575_ = crate::leanh::lean_ctor_get(v_s_574_, 0);
                crate::leanh::lean_inc(v_prefix_575_);
                v_suffix_576_ = crate::leanh::lean_ctor_get(v_s_574_, 1);
                crate::leanh::lean_inc(v_suffix_576_);
                v___x_577_ = l_List_Cursor_current___redArg(v_s_574_);
                v_isSharedCheck_591_ = (!crate::leanh::lean_is_exclusive(v_s_574_)) as u8;
                if v_isSharedCheck_591_ == 0 {
                    v_unused_592_ = crate::leanh::lean_ctor_get(v_s_574_, 1);
                    crate::leanh::lean_dec(v_unused_592_);
                    v_unused_593_ = crate::leanh::lean_ctor_get(v_s_574_, 0);
                    crate::leanh::lean_dec(v_unused_593_);
                    v___x_579_ = v_s_574_;
                    v_isShared_580_ = v_isSharedCheck_591_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_s_574_);
                    v___x_579_ = crate::leanh::lean_box(0);
                    v_isShared_580_ = v_isSharedCheck_591_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_581_ = crate::leanh::lean_box(0);
                v___x_582_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_582_, 0, v___x_577_);
                crate::leanh::lean_ctor_set(v___x_582_, 1, v___x_581_);
                v___x_583_ = l_List_appendTR___redArg(v_prefix_575_, v___x_582_);
                if crate::leanh::lean_obj_tag(v_suffix_576_) == 0 {
                    if v_isShared_580_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_579_, 0, v___x_583_);
                        v___x_585_ = v___x_579_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_586_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_586_, 1, v_suffix_576_);
                        v___x_585_ = v_reuseFailAlloc_586_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_tail_587_ = crate::leanh::lean_ctor_get(v_suffix_576_, 1);
                    crate::leanh::lean_inc(v_tail_587_);
                    crate::leanh::lean_dec_ref_known(v_suffix_576_, 2);
                    if v_isShared_580_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_579_, 1, v_tail_587_);
                        crate::leanh::lean_ctor_set(v___x_579_, 0, v___x_583_);
                        v___x_589_ = v___x_579_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_590_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_583_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_590_, 1, v_tail_587_);
                        v___x_589_ = v_reuseFailAlloc_590_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_585_;
            }
            3 => {
                return v___x_589_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_Cursor_tail(
    mut v_00_u03b1_594_: *mut crate::leanh::LeanObject,
    mut v_l_595_: *mut crate::leanh::LeanObject,
    mut v_s_596_: *mut crate::leanh::LeanObject,
    mut v_h_597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_598_ = l_List_Cursor_tail___redArg(v_s_596_);
    return v___x_598_;
}
pub unsafe fn l_List_Cursor_tail___boxed(
    mut v_00_u03b1_599_: *mut crate::leanh::LeanObject,
    mut v_l_600_: *mut crate::leanh::LeanObject,
    mut v_s_601_: *mut crate::leanh::LeanObject,
    mut v_h_602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_603_ = l_List_Cursor_tail(v_00_u03b1_599_, v_l_600_, v_s_601_, v_h_602_);
    crate::leanh::lean_dec(v_l_600_);
    return v_res_603_;
}
pub unsafe fn l_List_Cursor_pos___redArg(
    mut v_c_604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_prefix_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_prefix_605_ = crate::leanh::lean_ctor_get(v_c_604_, 0);
    v___x_606_ = l_List_lengthTR___redArg(v_prefix_605_);
    return v___x_606_;
}
pub unsafe fn l_List_Cursor_pos___redArg___boxed(
    mut v_c_607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_608_ = l_List_Cursor_pos___redArg(v_c_607_);
    crate::leanh::lean_dec_ref(v_c_607_);
    return v_res_608_;
}
pub unsafe fn l_List_Cursor_pos(
    mut v_00_u03b1_609_: *mut crate::leanh::LeanObject,
    mut v_l_610_: *mut crate::leanh::LeanObject,
    mut v_c_611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_prefix_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_prefix_612_ = crate::leanh::lean_ctor_get(v_c_611_, 0);
    v___x_613_ = l_List_lengthTR___redArg(v_prefix_612_);
    return v___x_613_;
}
pub unsafe fn l_List_Cursor_pos___boxed(
    mut v_00_u03b1_614_: *mut crate::leanh::LeanObject,
    mut v_l_615_: *mut crate::leanh::LeanObject,
    mut v_c_616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_617_ = l_List_Cursor_pos(v_00_u03b1_614_, v_l_615_, v_c_616_);
    crate::leanh::lean_dec_ref(v_c_616_);
    crate::leanh::lean_dec(v_l_615_);
    return v_res_617_;
}
pub unsafe fn l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushExcept_match__1_splitter___redArg(
    mut v_x_618_: *mut crate::leanh::LeanObject,
    mut v_h__1_619_: *mut crate::leanh::LeanObject,
    mut v_h__2_620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_618_) == 0 {
        let mut v_a_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_619_);
        v_a_621_ = crate::leanh::lean_ctor_get(v_x_618_, 0);
        crate::leanh::lean_inc(v_a_621_);
        crate::leanh::lean_dec_ref_known(v_x_618_, 1);
        v___x_622_ = crate::leanh::lean_apply_1(v_h__2_620_, v_a_621_);
        return v___x_622_;
    } else {
        let mut v_a_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_620_);
        v_a_623_ = crate::leanh::lean_ctor_get(v_x_618_, 0);
        crate::leanh::lean_inc(v_a_623_);
        crate::leanh::lean_dec_ref_known(v_x_618_, 1);
        v___x_624_ = crate::leanh::lean_apply_1(v_h__1_619_, v_a_623_);
        return v___x_624_;
    }
}
pub unsafe fn l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushExcept_match__1_splitter(
    mut v_00_u03b1_625_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_626_: *mut crate::leanh::LeanObject,
    mut v_motive_627_: *mut crate::leanh::LeanObject,
    mut v_x_628_: *mut crate::leanh::LeanObject,
    mut v_h__1_629_: *mut crate::leanh::LeanObject,
    mut v_h__2_630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_628_) == 0 {
        let mut v_a_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_629_);
        v_a_631_ = crate::leanh::lean_ctor_get(v_x_628_, 0);
        crate::leanh::lean_inc(v_a_631_);
        crate::leanh::lean_dec_ref_known(v_x_628_, 1);
        v___x_632_ = crate::leanh::lean_apply_1(v_h__2_630_, v_a_631_);
        return v___x_632_;
    } else {
        let mut v_a_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_630_);
        v_a_633_ = crate::leanh::lean_ctor_get(v_x_628_, 0);
        crate::leanh::lean_inc(v_a_633_);
        crate::leanh::lean_dec_ref_known(v_x_628_, 1);
        v___x_634_ = crate::leanh::lean_apply_1(v_h__1_629_, v_a_633_);
        return v___x_634_;
    }
}
pub unsafe fn l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(
    mut v_x_635_: *mut crate::leanh::LeanObject,
    mut v_h__1_636_: *mut crate::leanh::LeanObject,
    mut v_h__2_637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_635_) == 0 {
        let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_636_);
        v___x_638_ = crate::leanh::lean_box(0);
        v___x_639_ = crate::leanh::lean_apply_1(v_h__2_637_, v___x_638_);
        return v___x_639_;
    } else {
        let mut v_val_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_637_);
        v_val_640_ = crate::leanh::lean_ctor_get(v_x_635_, 0);
        crate::leanh::lean_inc(v_val_640_);
        crate::leanh::lean_dec_ref_known(v_x_635_, 1);
        v___x_641_ = crate::leanh::lean_apply_1(v_h__1_636_, v_val_640_);
        return v___x_641_;
    }
}
pub unsafe fn l___private_Std_Do_Triple_SpecLemmas_0__Std_Do_PredTrans_pushOption_match__1_splitter(
    mut v_00_u03b1_642_: *mut crate::leanh::LeanObject,
    mut v_motive_643_: *mut crate::leanh::LeanObject,
    mut v_x_644_: *mut crate::leanh::LeanObject,
    mut v_h__1_645_: *mut crate::leanh::LeanObject,
    mut v_h__2_646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_644_) == 0 {
        let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_645_);
        v___x_647_ = crate::leanh::lean_box(0);
        v___x_648_ = crate::leanh::lean_apply_1(v_h__2_646_, v___x_647_);
        return v___x_648_;
    } else {
        let mut v_val_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_646_);
        v_val_649_ = crate::leanh::lean_ctor_get(v_x_644_, 0);
        crate::leanh::lean_inc(v_val_649_);
        crate::leanh::lean_dec_ref_known(v_x_644_, 1);
        v___x_650_ = crate::leanh::lean_apply_1(v_h__1_645_, v_val_649_);
        return v___x_650_;
    }
}
pub unsafe fn l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0(
    mut v_onReturn_651_: *mut crate::leanh::LeanObject,
    mut v_snd_652_: *mut crate::leanh::LeanObject,
    mut v___x_653_: *mut crate::leanh::LeanObject,
    mut v___x_654_: *mut crate::leanh::LeanObject,
    mut v_r_655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_656_ = crate::leanh::lean_apply_2(v_onReturn_651_, v_r_655_, v_snd_652_);
    crate::leanh::lean_inc(v___x_654_);
    crate::leanh::lean_inc(v___x_653_);
    v___x_657_ = l_Std_Do_SPred_and(v___x_653_, v___x_654_, v___x_656_);
    v___x_658_ = l_Std_Do_SPred_and(v___x_653_, v___x_654_, v___x_657_);
    return v___x_658_;
}
pub unsafe fn l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1(
    mut v_ps_659_: *mut crate::leanh::LeanObject,
    mut v_onReturn_660_: *mut crate::leanh::LeanObject,
    mut v_onContinue_661_: *mut crate::leanh::LeanObject,
    mut v_x_662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_663_ = crate::leanh::lean_ctor_get(v_x_662_, 1);
    crate::leanh::lean_inc(v_snd_663_);
    v_fst_664_ = crate::leanh::lean_ctor_get(v_x_662_, 0);
    crate::leanh::lean_inc(v_fst_664_);
    crate::leanh::lean_dec_ref(v_x_662_);
    v_snd_665_ = crate::leanh::lean_ctor_get(v_snd_663_, 1);
    crate::leanh::lean_inc_n(v_snd_665_, 2);
    crate::leanh::lean_dec(v_snd_663_);
    v___x_666_ = l_Std_Do_PostShape_args(v_ps_659_);
    crate::leanh::lean_inc_n(v___x_666_, 4);
    v___x_667_ = l_Std_Do_SPred_pure___redArg(v___x_666_);
    crate::leanh::lean_inc(v___x_667_);
    v___f_668_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_668_, 0, v_onReturn_660_);
    crate::leanh::lean_closure_set(v___f_668_, 1, v_snd_665_);
    crate::leanh::lean_closure_set(v___f_668_, 2, v___x_666_);
    crate::leanh::lean_closure_set(v___f_668_, 3, v___x_667_);
    v___x_669_ = crate::leanh::lean_apply_2(v_onContinue_661_, v_fst_664_, v_snd_665_);
    v___x_670_ = l_Std_Do_SPred_and(v___x_666_, v___x_667_, v___x_669_);
    v___x_671_ = l_Std_Do_SPred_exists___redArg(v___x_666_, v___f_668_);
    v___x_672_ = l_Std_Do_SPred_or(v___x_666_, v___x_670_, v___x_671_);
    return v___x_672_;
}
pub unsafe fn l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1___boxed(
    mut v_ps_673_: *mut crate::leanh::LeanObject,
    mut v_onReturn_674_: *mut crate::leanh::LeanObject,
    mut v_onContinue_675_: *mut crate::leanh::LeanObject,
    mut v_x_676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_677_ = l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1(
        v_ps_673_,
        v_onReturn_674_,
        v_onContinue_675_,
        v_x_676_,
    );
    crate::leanh::lean_dec(v_ps_673_);
    return v_res_677_;
}
pub unsafe fn l_Std_Do_Invariant_withEarlyReturn___redArg(
    mut v_ps_678_: *mut crate::leanh::LeanObject,
    mut v_onContinue_679_: *mut crate::leanh::LeanObject,
    mut v_onReturn_680_: *mut crate::leanh::LeanObject,
    mut v_onExcept_681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_682_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_682_, 0, v_ps_678_);
    crate::leanh::lean_closure_set(v___f_682_, 1, v_onReturn_680_);
    crate::leanh::lean_closure_set(v___f_682_, 2, v_onContinue_679_);
    v___x_683_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_683_, 0, v___f_682_);
    crate::leanh::lean_ctor_set(v___x_683_, 1, v_onExcept_681_);
    return v___x_683_;
}
pub unsafe fn l_Std_Do_Invariant_withEarlyReturn(
    mut v_00_u03b2_684_: *mut crate::leanh::LeanObject,
    mut v_ps_685_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_686_: *mut crate::leanh::LeanObject,
    mut v_xs_687_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_688_: *mut crate::leanh::LeanObject,
    mut v_onContinue_689_: *mut crate::leanh::LeanObject,
    mut v_onReturn_690_: *mut crate::leanh::LeanObject,
    mut v_onExcept_691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_692_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_Invariant_withEarlyReturn___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_692_, 0, v_ps_685_);
    crate::leanh::lean_closure_set(v___f_692_, 1, v_onReturn_690_);
    crate::leanh::lean_closure_set(v___f_692_, 2, v_onContinue_689_);
    v___x_693_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_693_, 0, v___f_692_);
    crate::leanh::lean_ctor_set(v___x_693_, 1, v_onExcept_691_);
    return v___x_693_;
}
pub unsafe fn l_Std_Do_Invariant_withEarlyReturn___boxed(
    mut v_00_u03b2_694_: *mut crate::leanh::LeanObject,
    mut v_ps_695_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_696_: *mut crate::leanh::LeanObject,
    mut v_xs_697_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_698_: *mut crate::leanh::LeanObject,
    mut v_onContinue_699_: *mut crate::leanh::LeanObject,
    mut v_onReturn_700_: *mut crate::leanh::LeanObject,
    mut v_onExcept_701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_702_ = l_Std_Do_Invariant_withEarlyReturn(
        v_00_u03b2_694_,
        v_ps_695_,
        v_00_u03b1_696_,
        v_xs_697_,
        v_00_u03b3_698_,
        v_onContinue_699_,
        v_onReturn_700_,
        v_onExcept_701_,
    );
    crate::leanh::lean_dec(v_xs_697_);
    return v_res_702_;
}
pub unsafe fn l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1(
    mut v_ps_703_: *mut crate::leanh::LeanObject,
    mut v_onReturn_704_: *mut crate::leanh::LeanObject,
    mut v_onContinue_705_: *mut crate::leanh::LeanObject,
    mut v_x_706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_707_ = crate::leanh::lean_ctor_get(v_x_706_, 1);
    crate::leanh::lean_inc(v_snd_707_);
    v_fst_708_ = crate::leanh::lean_ctor_get(v_x_706_, 0);
    crate::leanh::lean_inc(v_fst_708_);
    crate::leanh::lean_dec_ref(v_x_706_);
    v_snd_709_ = crate::leanh::lean_ctor_get(v_snd_707_, 1);
    crate::leanh::lean_inc_n(v_snd_709_, 2);
    crate::leanh::lean_dec(v_snd_707_);
    v___x_710_ = l_Std_Do_PostShape_args(v_ps_703_);
    crate::leanh::lean_inc_n(v___x_710_, 4);
    v___x_711_ = l_Std_Do_SPred_pure___redArg(v___x_710_);
    crate::leanh::lean_inc(v___x_711_);
    v___f_712_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_712_, 0, v_onReturn_704_);
    crate::leanh::lean_closure_set(v___f_712_, 1, v_snd_709_);
    crate::leanh::lean_closure_set(v___f_712_, 2, v___x_710_);
    crate::leanh::lean_closure_set(v___f_712_, 3, v___x_711_);
    v___x_713_ = crate::leanh::lean_apply_2(v_onContinue_705_, v_fst_708_, v_snd_709_);
    v___x_714_ = l_Std_Do_SPred_and(v___x_710_, v___x_711_, v___x_713_);
    v___x_715_ = l_Std_Do_SPred_exists___redArg(v___x_710_, v___f_712_);
    v___x_716_ = l_Std_Do_SPred_or(v___x_710_, v___x_714_, v___x_715_);
    return v___x_716_;
}
pub unsafe fn l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1___boxed(
    mut v_ps_717_: *mut crate::leanh::LeanObject,
    mut v_onReturn_718_: *mut crate::leanh::LeanObject,
    mut v_onContinue_719_: *mut crate::leanh::LeanObject,
    mut v_x_720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_721_ = l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1(
        v_ps_717_,
        v_onReturn_718_,
        v_onContinue_719_,
        v_x_720_,
    );
    crate::leanh::lean_dec(v_ps_717_);
    return v_res_721_;
}
pub unsafe fn l_Std_Do_Invariant_withEarlyReturnNewDo___redArg(
    mut v_ps_722_: *mut crate::leanh::LeanObject,
    mut v_onContinue_723_: *mut crate::leanh::LeanObject,
    mut v_onReturn_724_: *mut crate::leanh::LeanObject,
    mut v_onExcept_725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_726_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_726_, 0, v_ps_722_);
    crate::leanh::lean_closure_set(v___f_726_, 1, v_onReturn_724_);
    crate::leanh::lean_closure_set(v___f_726_, 2, v_onContinue_723_);
    v___x_727_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_727_, 0, v___f_726_);
    crate::leanh::lean_ctor_set(v___x_727_, 1, v_onExcept_725_);
    return v___x_727_;
}
pub unsafe fn l_Std_Do_Invariant_withEarlyReturnNewDo(
    mut v_00_u03b2_728_: *mut crate::leanh::LeanObject,
    mut v_ps_729_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_730_: *mut crate::leanh::LeanObject,
    mut v_xs_731_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_732_: *mut crate::leanh::LeanObject,
    mut v_onContinue_733_: *mut crate::leanh::LeanObject,
    mut v_onReturn_734_: *mut crate::leanh::LeanObject,
    mut v_onExcept_735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_736_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_Invariant_withEarlyReturnNewDo___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_736_, 0, v_ps_729_);
    crate::leanh::lean_closure_set(v___f_736_, 1, v_onReturn_734_);
    crate::leanh::lean_closure_set(v___f_736_, 2, v_onContinue_733_);
    v___x_737_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_737_, 0, v___f_736_);
    crate::leanh::lean_ctor_set(v___x_737_, 1, v_onExcept_735_);
    return v___x_737_;
}
pub unsafe fn l_Std_Do_Invariant_withEarlyReturnNewDo___boxed(
    mut v_00_u03b2_738_: *mut crate::leanh::LeanObject,
    mut v_ps_739_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_740_: *mut crate::leanh::LeanObject,
    mut v_xs_741_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_742_: *mut crate::leanh::LeanObject,
    mut v_onContinue_743_: *mut crate::leanh::LeanObject,
    mut v_onReturn_744_: *mut crate::leanh::LeanObject,
    mut v_onExcept_745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_746_ = l_Std_Do_Invariant_withEarlyReturnNewDo(
        v_00_u03b2_738_,
        v_ps_739_,
        v_00_u03b1_740_,
        v_xs_741_,
        v_00_u03b3_742_,
        v_onContinue_743_,
        v_onReturn_744_,
        v_onExcept_745_,
    );
    crate::leanh::lean_dec(v_xs_741_);
    return v_res_746_;
}
pub unsafe fn l___private_Std_Do_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter___redArg(
    mut v_x_747_: *mut crate::leanh::LeanObject,
    mut v_h__1_748_: *mut crate::leanh::LeanObject,
    mut v_h__2_749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_747_) == 0 {
        let mut v_a_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_749_);
        v_a_750_ = crate::leanh::lean_ctor_get(v_x_747_, 0);
        crate::leanh::lean_inc(v_a_750_);
        crate::leanh::lean_dec_ref_known(v_x_747_, 1);
        v___x_751_ = crate::leanh::lean_apply_1(v_h__1_748_, v_a_750_);
        return v___x_751_;
    } else {
        let mut v_a_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_748_);
        v_a_752_ = crate::leanh::lean_ctor_get(v_x_747_, 0);
        crate::leanh::lean_inc(v_a_752_);
        crate::leanh::lean_dec_ref_known(v_x_747_, 1);
        v___x_753_ = crate::leanh::lean_apply_1(v_h__2_749_, v_a_752_);
        return v___x_753_;
    }
}
pub unsafe fn l___private_Std_Do_Triple_SpecLemmas_0__List_forIn_x27__cons_match__1_splitter(
    mut v_00_u03b2_754_: *mut crate::leanh::LeanObject,
    mut v_motive_755_: *mut crate::leanh::LeanObject,
    mut v_x_756_: *mut crate::leanh::LeanObject,
    mut v_h__1_757_: *mut crate::leanh::LeanObject,
    mut v_h__2_758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_756_) == 0 {
        let mut v_a_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_758_);
        v_a_759_ = crate::leanh::lean_ctor_get(v_x_756_, 0);
        crate::leanh::lean_inc(v_a_759_);
        crate::leanh::lean_dec_ref_known(v_x_756_, 1);
        v___x_760_ = crate::leanh::lean_apply_1(v_h__1_757_, v_a_759_);
        return v___x_760_;
    } else {
        let mut v_a_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_757_);
        v_a_761_ = crate::leanh::lean_ctor_get(v_x_756_, 0);
        crate::leanh::lean_inc(v_a_761_);
        crate::leanh::lean_dec_ref_known(v_x_756_, 1);
        v___x_762_ = crate::leanh::lean_apply_1(v_h__2_758_, v_a_761_);
        return v___x_762_;
    }
}
pub unsafe fn l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1(
    mut v_ps_763_: *mut crate::leanh::LeanObject,
    mut v_onReturn_764_: *mut crate::leanh::LeanObject,
    mut v_onContinue_765_: *mut crate::leanh::LeanObject,
    mut v_x_766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_767_ = crate::leanh::lean_ctor_get(v_x_766_, 1);
    crate::leanh::lean_inc(v_snd_767_);
    v_fst_768_ = crate::leanh::lean_ctor_get(v_x_766_, 0);
    crate::leanh::lean_inc(v_fst_768_);
    crate::leanh::lean_dec_ref(v_x_766_);
    v_snd_769_ = crate::leanh::lean_ctor_get(v_snd_767_, 1);
    crate::leanh::lean_inc_n(v_snd_769_, 2);
    crate::leanh::lean_dec(v_snd_767_);
    v___x_770_ = l_Std_Do_PostShape_args(v_ps_763_);
    crate::leanh::lean_inc_n(v___x_770_, 4);
    v___x_771_ = l_Std_Do_SPred_pure___redArg(v___x_770_);
    crate::leanh::lean_inc(v___x_771_);
    v___f_772_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_772_, 0, v_onReturn_764_);
    crate::leanh::lean_closure_set(v___f_772_, 1, v_snd_769_);
    crate::leanh::lean_closure_set(v___f_772_, 2, v___x_770_);
    crate::leanh::lean_closure_set(v___f_772_, 3, v___x_771_);
    v___x_773_ = crate::leanh::lean_apply_2(v_onContinue_765_, v_fst_768_, v_snd_769_);
    v___x_774_ = l_Std_Do_SPred_and(v___x_770_, v___x_771_, v___x_773_);
    v___x_775_ = l_Std_Do_SPred_exists___redArg(v___x_770_, v___f_772_);
    v___x_776_ = l_Std_Do_SPred_or(v___x_770_, v___x_774_, v___x_775_);
    return v___x_776_;
}
pub unsafe fn l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed(
    mut v_ps_777_: *mut crate::leanh::LeanObject,
    mut v_onReturn_778_: *mut crate::leanh::LeanObject,
    mut v_onContinue_779_: *mut crate::leanh::LeanObject,
    mut v_x_780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_781_ = l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1(
        v_ps_777_,
        v_onReturn_778_,
        v_onContinue_779_,
        v_x_780_,
    );
    crate::leanh::lean_dec(v_ps_777_);
    return v_res_781_;
}
pub unsafe fn l_Std_Do_StringInvariant_withEarlyReturn___redArg(
    mut v_ps_782_: *mut crate::leanh::LeanObject,
    mut v_onContinue_783_: *mut crate::leanh::LeanObject,
    mut v_onReturn_784_: *mut crate::leanh::LeanObject,
    mut v_onExcept_785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_786_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_786_, 0, v_ps_782_);
    crate::leanh::lean_closure_set(v___f_786_, 1, v_onReturn_784_);
    crate::leanh::lean_closure_set(v___f_786_, 2, v_onContinue_783_);
    v___x_787_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_787_, 0, v___f_786_);
    crate::leanh::lean_ctor_set(v___x_787_, 1, v_onExcept_785_);
    return v___x_787_;
}
pub unsafe fn l_Std_Do_StringInvariant_withEarlyReturn(
    mut v_00_u03b2_788_: *mut crate::leanh::LeanObject,
    mut v_ps_789_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_790_: *mut crate::leanh::LeanObject,
    mut v_s_791_: *mut crate::leanh::LeanObject,
    mut v_onContinue_792_: *mut crate::leanh::LeanObject,
    mut v_onReturn_793_: *mut crate::leanh::LeanObject,
    mut v_onExcept_794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_795_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_795_, 0, v_ps_789_);
    crate::leanh::lean_closure_set(v___f_795_, 1, v_onReturn_793_);
    crate::leanh::lean_closure_set(v___f_795_, 2, v_onContinue_792_);
    v___x_796_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_796_, 0, v___f_795_);
    crate::leanh::lean_ctor_set(v___x_796_, 1, v_onExcept_794_);
    return v___x_796_;
}
pub unsafe fn l_Std_Do_StringInvariant_withEarlyReturn___boxed(
    mut v_00_u03b2_797_: *mut crate::leanh::LeanObject,
    mut v_ps_798_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_799_: *mut crate::leanh::LeanObject,
    mut v_s_800_: *mut crate::leanh::LeanObject,
    mut v_onContinue_801_: *mut crate::leanh::LeanObject,
    mut v_onReturn_802_: *mut crate::leanh::LeanObject,
    mut v_onExcept_803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_804_ = l_Std_Do_StringInvariant_withEarlyReturn(
        v_00_u03b2_797_,
        v_ps_798_,
        v_00_u03b3_799_,
        v_s_800_,
        v_onContinue_801_,
        v_onReturn_802_,
        v_onExcept_803_,
    );
    crate::leanh::lean_dec_ref(v_s_800_);
    return v_res_804_;
}
pub unsafe fn l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1(
    mut v_ps_805_: *mut crate::leanh::LeanObject,
    mut v_onReturn_806_: *mut crate::leanh::LeanObject,
    mut v_onContinue_807_: *mut crate::leanh::LeanObject,
    mut v_x_808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_809_ = crate::leanh::lean_ctor_get(v_x_808_, 1);
    crate::leanh::lean_inc(v_snd_809_);
    v_fst_810_ = crate::leanh::lean_ctor_get(v_x_808_, 0);
    crate::leanh::lean_inc(v_fst_810_);
    crate::leanh::lean_dec_ref(v_x_808_);
    v_snd_811_ = crate::leanh::lean_ctor_get(v_snd_809_, 1);
    crate::leanh::lean_inc_n(v_snd_811_, 2);
    crate::leanh::lean_dec(v_snd_809_);
    v___x_812_ = l_Std_Do_PostShape_args(v_ps_805_);
    crate::leanh::lean_inc_n(v___x_812_, 4);
    v___x_813_ = l_Std_Do_SPred_pure___redArg(v___x_812_);
    crate::leanh::lean_inc(v___x_813_);
    v___f_814_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_Invariant_withEarlyReturn___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_814_, 0, v_onReturn_806_);
    crate::leanh::lean_closure_set(v___f_814_, 1, v_snd_811_);
    crate::leanh::lean_closure_set(v___f_814_, 2, v___x_812_);
    crate::leanh::lean_closure_set(v___f_814_, 3, v___x_813_);
    v___x_815_ = crate::leanh::lean_apply_2(v_onContinue_807_, v_fst_810_, v_snd_811_);
    v___x_816_ = l_Std_Do_SPred_and(v___x_812_, v___x_813_, v___x_815_);
    v___x_817_ = l_Std_Do_SPred_exists___redArg(v___x_812_, v___f_814_);
    v___x_818_ = l_Std_Do_SPred_or(v___x_812_, v___x_816_, v___x_817_);
    return v___x_818_;
}
pub unsafe fn l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed(
    mut v_ps_819_: *mut crate::leanh::LeanObject,
    mut v_onReturn_820_: *mut crate::leanh::LeanObject,
    mut v_onContinue_821_: *mut crate::leanh::LeanObject,
    mut v_x_822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_823_ = l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1(
        v_ps_819_,
        v_onReturn_820_,
        v_onContinue_821_,
        v_x_822_,
    );
    crate::leanh::lean_dec(v_ps_819_);
    return v_res_823_;
}
pub unsafe fn l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg(
    mut v_ps_824_: *mut crate::leanh::LeanObject,
    mut v_onContinue_825_: *mut crate::leanh::LeanObject,
    mut v_onReturn_826_: *mut crate::leanh::LeanObject,
    mut v_onExcept_827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_828_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_828_, 0, v_ps_824_);
    crate::leanh::lean_closure_set(v___f_828_, 1, v_onReturn_826_);
    crate::leanh::lean_closure_set(v___f_828_, 2, v_onContinue_825_);
    v___x_829_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_829_, 0, v___f_828_);
    crate::leanh::lean_ctor_set(v___x_829_, 1, v_onExcept_827_);
    return v___x_829_;
}
pub unsafe fn l_Std_Do_StringInvariant_withEarlyReturnNewDo(
    mut v_00_u03b2_830_: *mut crate::leanh::LeanObject,
    mut v_ps_831_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_832_: *mut crate::leanh::LeanObject,
    mut v_s_833_: *mut crate::leanh::LeanObject,
    mut v_onContinue_834_: *mut crate::leanh::LeanObject,
    mut v_onReturn_835_: *mut crate::leanh::LeanObject,
    mut v_onExcept_836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_837_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_837_, 0, v_ps_831_);
    crate::leanh::lean_closure_set(v___f_837_, 1, v_onReturn_835_);
    crate::leanh::lean_closure_set(v___f_837_, 2, v_onContinue_834_);
    v___x_838_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_838_, 0, v___f_837_);
    crate::leanh::lean_ctor_set(v___x_838_, 1, v_onExcept_836_);
    return v___x_838_;
}
pub unsafe fn l_Std_Do_StringInvariant_withEarlyReturnNewDo___boxed(
    mut v_00_u03b2_839_: *mut crate::leanh::LeanObject,
    mut v_ps_840_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_841_: *mut crate::leanh::LeanObject,
    mut v_s_842_: *mut crate::leanh::LeanObject,
    mut v_onContinue_843_: *mut crate::leanh::LeanObject,
    mut v_onReturn_844_: *mut crate::leanh::LeanObject,
    mut v_onExcept_845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_846_ = l_Std_Do_StringInvariant_withEarlyReturnNewDo(
        v_00_u03b2_839_,
        v_ps_840_,
        v_00_u03b3_841_,
        v_s_842_,
        v_onContinue_843_,
        v_onReturn_844_,
        v_onExcept_845_,
    );
    crate::leanh::lean_dec_ref(v_s_842_);
    return v_res_846_;
}
pub unsafe fn l_Std_Do_StringSliceInvariant_withEarlyReturn___redArg(
    mut v_ps_847_: *mut crate::leanh::LeanObject,
    mut v_onContinue_848_: *mut crate::leanh::LeanObject,
    mut v_onReturn_849_: *mut crate::leanh::LeanObject,
    mut v_onExcept_850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_851_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_851_, 0, v_ps_847_);
    crate::leanh::lean_closure_set(v___f_851_, 1, v_onReturn_849_);
    crate::leanh::lean_closure_set(v___f_851_, 2, v_onContinue_848_);
    v___x_852_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_852_, 0, v___f_851_);
    crate::leanh::lean_ctor_set(v___x_852_, 1, v_onExcept_850_);
    return v___x_852_;
}
pub unsafe fn l_Std_Do_StringSliceInvariant_withEarlyReturn(
    mut v_00_u03b2_853_: *mut crate::leanh::LeanObject,
    mut v_ps_854_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_855_: *mut crate::leanh::LeanObject,
    mut v_s_856_: *mut crate::leanh::LeanObject,
    mut v_onContinue_857_: *mut crate::leanh::LeanObject,
    mut v_onReturn_858_: *mut crate::leanh::LeanObject,
    mut v_onExcept_859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_860_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_StringInvariant_withEarlyReturn___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_860_, 0, v_ps_854_);
    crate::leanh::lean_closure_set(v___f_860_, 1, v_onReturn_858_);
    crate::leanh::lean_closure_set(v___f_860_, 2, v_onContinue_857_);
    v___x_861_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_861_, 0, v___f_860_);
    crate::leanh::lean_ctor_set(v___x_861_, 1, v_onExcept_859_);
    return v___x_861_;
}
pub unsafe fn l_Std_Do_StringSliceInvariant_withEarlyReturn___boxed(
    mut v_00_u03b2_862_: *mut crate::leanh::LeanObject,
    mut v_ps_863_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_864_: *mut crate::leanh::LeanObject,
    mut v_s_865_: *mut crate::leanh::LeanObject,
    mut v_onContinue_866_: *mut crate::leanh::LeanObject,
    mut v_onReturn_867_: *mut crate::leanh::LeanObject,
    mut v_onExcept_868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_869_ = l_Std_Do_StringSliceInvariant_withEarlyReturn(
        v_00_u03b2_862_,
        v_ps_863_,
        v_00_u03b3_864_,
        v_s_865_,
        v_onContinue_866_,
        v_onReturn_867_,
        v_onExcept_868_,
    );
    crate::leanh::lean_dec_ref(v_s_865_);
    return v_res_869_;
}
pub unsafe fn l_Std_Do_StringSliceInvariant_withEarlyReturnNewDo___redArg(
    mut v_ps_870_: *mut crate::leanh::LeanObject,
    mut v_onContinue_871_: *mut crate::leanh::LeanObject,
    mut v_onReturn_872_: *mut crate::leanh::LeanObject,
    mut v_onExcept_873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_874_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_874_, 0, v_ps_870_);
    crate::leanh::lean_closure_set(v___f_874_, 1, v_onReturn_872_);
    crate::leanh::lean_closure_set(v___f_874_, 2, v_onContinue_871_);
    v___x_875_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_875_, 0, v___f_874_);
    crate::leanh::lean_ctor_set(v___x_875_, 1, v_onExcept_873_);
    return v___x_875_;
}
pub unsafe fn l_Std_Do_StringSliceInvariant_withEarlyReturnNewDo(
    mut v_00_u03b2_876_: *mut crate::leanh::LeanObject,
    mut v_ps_877_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_878_: *mut crate::leanh::LeanObject,
    mut v_s_879_: *mut crate::leanh::LeanObject,
    mut v_onContinue_880_: *mut crate::leanh::LeanObject,
    mut v_onReturn_881_: *mut crate::leanh::LeanObject,
    mut v_onExcept_882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_883_ = crate::leanh::lean_alloc_closure(
        l_Std_Do_StringInvariant_withEarlyReturnNewDo___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_883_, 0, v_ps_877_);
    crate::leanh::lean_closure_set(v___f_883_, 1, v_onReturn_881_);
    crate::leanh::lean_closure_set(v___f_883_, 2, v_onContinue_880_);
    v___x_884_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_884_, 0, v___f_883_);
    crate::leanh::lean_ctor_set(v___x_884_, 1, v_onExcept_882_);
    return v___x_884_;
}
pub unsafe fn l_Std_Do_StringSliceInvariant_withEarlyReturnNewDo___boxed(
    mut v_00_u03b2_885_: *mut crate::leanh::LeanObject,
    mut v_ps_886_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_887_: *mut crate::leanh::LeanObject,
    mut v_s_888_: *mut crate::leanh::LeanObject,
    mut v_onContinue_889_: *mut crate::leanh::LeanObject,
    mut v_onReturn_890_: *mut crate::leanh::LeanObject,
    mut v_onExcept_891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_892_ = l_Std_Do_StringSliceInvariant_withEarlyReturnNewDo(
        v_00_u03b2_885_,
        v_ps_886_,
        v_00_u03b3_887_,
        v_s_888_,
        v_onContinue_889_,
        v_onReturn_890_,
        v_onExcept_891_,
    );
    crate::leanh::lean_dec_ref(v_s_888_);
    return v_res_892_;
}
pub unsafe fn l_Std_Do_WhileVariant_eval___redArg(
    mut v_ps_893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_894_ = l_Std_Do_PostShape_args(v_ps_893_);
    v___x_895_ = l_Std_Do_SVal_evalsTo___redArg(v___x_894_);
    return v___x_895_;
}
pub unsafe fn l_Std_Do_WhileVariant_eval___redArg___boxed(
    mut v_ps_896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_897_ = l_Std_Do_WhileVariant_eval___redArg(v_ps_896_);
    crate::leanh::lean_dec(v_ps_896_);
    return v_res_897_;
}
pub unsafe fn l_Std_Do_WhileVariant_eval(
    mut v_00_u03b1_898_: *mut crate::leanh::LeanObject,
    mut v_ps_899_: *mut crate::leanh::LeanObject,
    mut v_variant_900_: *mut crate::leanh::LeanObject,
    mut v_a_901_: *mut crate::leanh::LeanObject,
    mut v_n_902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_903_ = l_Std_Do_PostShape_args(v_ps_899_);
    v___x_904_ = l_Std_Do_SVal_evalsTo___redArg(v___x_903_);
    return v___x_904_;
}
pub unsafe fn l_Std_Do_WhileVariant_eval___boxed(
    mut v_00_u03b1_905_: *mut crate::leanh::LeanObject,
    mut v_ps_906_: *mut crate::leanh::LeanObject,
    mut v_variant_907_: *mut crate::leanh::LeanObject,
    mut v_a_908_: *mut crate::leanh::LeanObject,
    mut v_n_909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_910_ = l_Std_Do_WhileVariant_eval(
        v_00_u03b1_905_,
        v_ps_906_,
        v_variant_907_,
        v_a_908_,
        v_n_909_,
    );
    crate::leanh::lean_dec(v_n_909_);
    crate::leanh::lean_dec(v_a_908_);
    crate::leanh::lean_dec(v_variant_907_);
    crate::leanh::lean_dec(v_ps_906_);
    return v_res_910_;
}
pub unsafe fn l___private_Std_Do_Triple_SpecLemmas_0__Lean_Loop_forIn_match__1_splitter___redArg(
    mut v_____do__lift_911_: *mut crate::leanh::LeanObject,
    mut v_h__1_912_: *mut crate::leanh::LeanObject,
    mut v_h__2_913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_911_) == 0 {
        let mut v_a_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_913_);
        v_a_914_ = crate::leanh::lean_ctor_get(v_____do__lift_911_, 0);
        crate::leanh::lean_inc(v_a_914_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_911_, 1);
        v___x_915_ = crate::leanh::lean_apply_1(v_h__1_912_, v_a_914_);
        return v___x_915_;
    } else {
        let mut v_a_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_912_);
        v_a_916_ = crate::leanh::lean_ctor_get(v_____do__lift_911_, 0);
        crate::leanh::lean_inc(v_a_916_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_911_, 1);
        v___x_917_ = crate::leanh::lean_apply_1(v_h__2_913_, v_a_916_);
        return v___x_917_;
    }
}
pub unsafe fn l___private_Std_Do_Triple_SpecLemmas_0__Lean_Loop_forIn_match__1_splitter(
    mut v_00_u03b2_918_: *mut crate::leanh::LeanObject,
    mut v_motive_919_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_920_: *mut crate::leanh::LeanObject,
    mut v_h__1_921_: *mut crate::leanh::LeanObject,
    mut v_h__2_922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_920_) == 0 {
        let mut v_a_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_922_);
        v_a_923_ = crate::leanh::lean_ctor_get(v_____do__lift_920_, 0);
        crate::leanh::lean_inc(v_a_923_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_920_, 1);
        v___x_924_ = crate::leanh::lean_apply_1(v_h__1_921_, v_a_923_);
        return v___x_924_;
    } else {
        let mut v_a_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_921_);
        v_a_925_ = crate::leanh::lean_ctor_get(v_____do__lift_920_, 0);
        crate::leanh::lean_inc(v_a_925_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_920_, 1);
        v___x_926_ = crate::leanh::lean_apply_1(v_h__2_922_, v_a_925_);
        return v___x_926_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Do_Triple_SpecLemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Do_Triple_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Internal_Order_While(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Mod(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Iterate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Splits(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Termination(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Iterate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Do_Triple_SpecLemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_List_Cursor_current___auto__1 = _init_l_List_Cursor_current___auto__1();
    crate::leanh::lean_mark_persistent(l_List_Cursor_current___auto__1);
    l_List_Cursor_tail___auto__1 = _init_l_List_Cursor_tail___auto__1();
    crate::leanh::lean_mark_persistent(l_List_Cursor_tail___auto__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Do_Triple_SpecLemmas(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Do_Triple_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Internal_Order_While(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Mod(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Iterate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Splits(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Termination(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Iterate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Do_Triple_SpecLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Do_Triple_SpecLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Do_Triple_SpecLemmas(builtin);
}

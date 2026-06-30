// Lean compiler output
// Module: Lean.Data.Trie
// Imports: Lean.Data.Format Init.Data.Option.Coe Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_array_to_list, lean_array_uget_borrowed, lean_byte_array_fget,
    lean_byte_array_mk, lean_byte_array_push, lean_byte_array_size,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_to_int, lean_string_get_byte_fast, lean_string_utf8_byte_size, lean_uint8_dec_eq,
    lean_uint8_to_nat, lean_usize_add, lean_usize_dec_eq, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::ByteArray::Basic::l_ByteArray_toList;
use crate::r#gen::Init::Data::Format::Basic::{
    l_Std_Format_defWidth, l_Std_Format_joinSep___redArg, l_Std_Format_pretty,
    l_Std_instToFormatFormat___lam__0___boxed,
};
use crate::r#gen::Init::Data::List::Impl::l___private_Init_Data_List_Impl_0__List_zipWithTR_go;
use crate::r#gen::Init::Data::Option::Coe::{
    initialize_Init_Data_Option_Coe, runtime_initialize_Init_Data_Option_Coe,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_Lean_mkAtom;
use crate::r#gen::Lean::Data::Format::{
    initialize_Lean_Data_Format, runtime_initialize_Lean_Data_Format,
};
pub static l_Lean_Data_Trie_empty___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lean_Data_Trie_empty___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_empty___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Data_Trie_instEmptyCollection___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Data_Trie_instEmptyCollection___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Data_Trie_values___redArg___closed__0_value: leanh::LeanArrayObject<0> =
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
static mut l_Lean_Data_Trie_values___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_values___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0_value:
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
static mut l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__0_value:
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
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__1_value:
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
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__2_value:
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
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__3_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
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
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Data_Trie_matchPrefix___auto__1___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Data_Trie_matchPrefix___auto__1___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Data_Trie_matchPrefix___auto__1___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__4_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__4_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__4_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__3_value)
            as *mut leanh::LeanObject,
        8504843326314613972 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__5_value: leanh::LeanArrayObject<
    0,
> = leanh::LeanArrayObject {
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
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__6_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
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
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_Data_Trie_matchPrefix___auto__1___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Data_Trie_matchPrefix___auto__1___closed__7_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__7_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Data_Trie_matchPrefix___auto__1___closed__7_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__7_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__7_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__7_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__6_value)
            as *mut leanh::LeanObject,
        17228437386856258271 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__8_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__9_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__8_value)
            as *mut leanh::LeanObject,
        9855511589286918680 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__10_value:
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
    m_data: [115, 105, 109, 112, 0],
};
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__10_value)
        as *mut leanh::LeanObject;
static l_Lean_Data_Trie_matchPrefix___auto__1___closed__11_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Data_Trie_matchPrefix___auto__1___closed__11_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__11_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Data_Trie_matchPrefix___auto__1___closed__11_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__11_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__11_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__11_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__10_value)
            as *mut leanh::LeanObject,
        12783917532758215986 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__14_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__14_value)
        as *mut leanh::LeanObject;
static l_Lean_Data_Trie_matchPrefix___auto__1___closed__15_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Data_Trie_matchPrefix___auto__1___closed__15_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__15_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Data_Trie_matchPrefix___auto__1___closed__15_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__15_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__2_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__15_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__15_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__14_value)
            as *mut leanh::LeanObject,
        3488656302031949961 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__16_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 1,
    },
    m_objs: [
        (((2 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__25_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__25: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__26_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__26: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__27_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__27: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__28_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__28: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__29_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__29: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__30_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__30: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Data_Trie_matchPrefix___auto__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___closed__0_value:
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
static mut l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Data_Trie_instToString___private__1___redArg___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_instToFormatFormat___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Data_Trie_instToString___private__1___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_instToString___private__1___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Data_Trie_instToString___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Data_Trie_instToString___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Data_Trie_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Data_Trie_ctorIdx___redArg(
    mut v_x_790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_790_) {
        0 => {
            let mut v___x_791_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_791_ = leanh::lean_unsigned_to_nat(0);
            return v___x_791_;
        }
        1 => {
            let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_792_ = leanh::lean_unsigned_to_nat(1);
            return v___x_792_;
        }
        _ => {
            let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_793_ = leanh::lean_unsigned_to_nat(2);
            return v___x_793_;
        }
    }
}
pub unsafe fn l_Lean_Data_Trie_ctorIdx___redArg___boxed(
    mut v_x_794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_795_ = l_Lean_Data_Trie_ctorIdx___redArg(v_x_794_);
    leanh::lean_dec_ref(v_x_794_);
    return v_res_795_;
}
pub unsafe fn l_Lean_Data_Trie_ctorIdx(
    mut v_00_u03b1_796_: *mut leanh::LeanObject,
    mut v_x_797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_798_ = l_Lean_Data_Trie_ctorIdx___redArg(v_x_797_);
    return v___x_798_;
}
pub unsafe fn l_Lean_Data_Trie_ctorIdx___boxed(
    mut v_00_u03b1_799_: *mut leanh::LeanObject,
    mut v_x_800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_801_ = l_Lean_Data_Trie_ctorIdx(v_00_u03b1_799_, v_x_800_);
    leanh::lean_dec_ref(v_x_800_);
    return v_res_801_;
}
pub unsafe fn l_Lean_Data_Trie_ctorElim___redArg(
    mut v_t_802_: *mut leanh::LeanObject,
    mut v_k_803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_802_) {
        0 => {
            let mut v_a_804_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_804_ = leanh::lean_ctor_get(v_t_802_, 0);
            leanh::lean_inc(v_a_804_);
            leanh::lean_dec_ref_known(v_t_802_, 1);
            v___x_805_ = leanh::lean_apply_1(v_k_803_, v_a_804_);
            return v___x_805_;
        }
        1 => {
            let mut v_a_806_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_807_: u8 = 0;
            let mut v_a_808_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_809_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_810_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_806_ = leanh::lean_ctor_get(v_t_802_, 0);
            leanh::lean_inc(v_a_806_);
            v_a_807_ = leanh::lean_ctor_get_uint8(
                v_t_802_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
            );
            v_a_808_ = leanh::lean_ctor_get(v_t_802_, 1);
            leanh::lean_inc_ref(v_a_808_);
            leanh::lean_dec_ref_known(v_t_802_, 2);
            v___x_809_ = leanh::lean_box((v_a_807_) as usize);
            v___x_810_ = leanh::lean_apply_3(v_k_803_, v_a_806_, v___x_809_, v_a_808_);
            return v___x_810_;
        }
        _ => {
            let mut v_a_811_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_812_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_813_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_814_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_811_ = leanh::lean_ctor_get(v_t_802_, 0);
            leanh::lean_inc(v_a_811_);
            v_a_812_ = leanh::lean_ctor_get(v_t_802_, 1);
            leanh::lean_inc_ref(v_a_812_);
            v_a_813_ = leanh::lean_ctor_get(v_t_802_, 2);
            leanh::lean_inc_ref(v_a_813_);
            leanh::lean_dec_ref_known(v_t_802_, 3);
            v___x_814_ = leanh::lean_apply_3(v_k_803_, v_a_811_, v_a_812_, v_a_813_);
            return v___x_814_;
        }
    }
}
pub unsafe fn l_Lean_Data_Trie_ctorElim(
    mut v_00_u03b1_815_: *mut leanh::LeanObject,
    mut v_motive__1_816_: *mut leanh::LeanObject,
    mut v_ctorIdx_817_: *mut leanh::LeanObject,
    mut v_t_818_: *mut leanh::LeanObject,
    mut v_h_819_: *mut leanh::LeanObject,
    mut v_k_820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_821_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_818_, v_k_820_);
    return v___x_821_;
}
pub unsafe fn l_Lean_Data_Trie_ctorElim___boxed(
    mut v_00_u03b1_822_: *mut leanh::LeanObject,
    mut v_motive__1_823_: *mut leanh::LeanObject,
    mut v_ctorIdx_824_: *mut leanh::LeanObject,
    mut v_t_825_: *mut leanh::LeanObject,
    mut v_h_826_: *mut leanh::LeanObject,
    mut v_k_827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_828_ = l_Lean_Data_Trie_ctorElim(
        v_00_u03b1_822_,
        v_motive__1_823_,
        v_ctorIdx_824_,
        v_t_825_,
        v_h_826_,
        v_k_827_,
    );
    leanh::lean_dec(v_ctorIdx_824_);
    return v_res_828_;
}
pub unsafe fn l_Lean_Data_Trie_leaf_elim___redArg(
    mut v_t_829_: *mut leanh::LeanObject,
    mut v_leaf_830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_831_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_829_, v_leaf_830_);
    return v___x_831_;
}
pub unsafe fn l_Lean_Data_Trie_leaf_elim(
    mut v_00_u03b1_832_: *mut leanh::LeanObject,
    mut v_motive__1_833_: *mut leanh::LeanObject,
    mut v_t_834_: *mut leanh::LeanObject,
    mut v_h_835_: *mut leanh::LeanObject,
    mut v_leaf_836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_837_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_834_, v_leaf_836_);
    return v___x_837_;
}
pub unsafe fn l_Lean_Data_Trie_node1_elim___redArg(
    mut v_t_838_: *mut leanh::LeanObject,
    mut v_node1_839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_840_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_838_, v_node1_839_);
    return v___x_840_;
}
pub unsafe fn l_Lean_Data_Trie_node1_elim(
    mut v_00_u03b1_841_: *mut leanh::LeanObject,
    mut v_motive__1_842_: *mut leanh::LeanObject,
    mut v_t_843_: *mut leanh::LeanObject,
    mut v_h_844_: *mut leanh::LeanObject,
    mut v_node1_845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_846_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_843_, v_node1_845_);
    return v___x_846_;
}
pub unsafe fn l_Lean_Data_Trie_node_elim___redArg(
    mut v_t_847_: *mut leanh::LeanObject,
    mut v_node_848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_849_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_847_, v_node_848_);
    return v___x_849_;
}
pub unsafe fn l_Lean_Data_Trie_node_elim(
    mut v_00_u03b1_850_: *mut leanh::LeanObject,
    mut v_motive__1_851_: *mut leanh::LeanObject,
    mut v_t_852_: *mut leanh::LeanObject,
    mut v_h_853_: *mut leanh::LeanObject,
    mut v_node_854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_855_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_852_, v_node_854_);
    return v___x_855_;
}
pub unsafe fn l_Lean_Data_Trie_empty(
    mut v_00_u03b1_858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_859_ = l_Lean_Data_Trie_empty___closed__0;
    return v___x_859_;
}
pub unsafe fn _init_l_Lean_Data_Trie_instEmptyCollection___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_860_ = l_Lean_Data_Trie_empty(leanh::lean_box(0));
    return v___x_860_;
}
pub unsafe fn l_Lean_Data_Trie_instEmptyCollection(
    mut v_00_u03b1_861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_862_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_instEmptyCollection___closed__0_once),
        _init_l_Lean_Data_Trie_instEmptyCollection___closed__0,
    );
    return v___x_862_;
}
pub unsafe fn l_Lean_Data_Trie_instInhabited(
    mut v_00_u03b1_863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_864_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_instEmptyCollection___closed__0_once),
        _init_l_Lean_Data_Trie_instEmptyCollection___closed__0,
    );
    return v___x_864_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(
    mut v_s_865_: *mut leanh::LeanObject,
    mut v_f_866_: *mut leanh::LeanObject,
    mut v_i_867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: u8 = 0;
    v___x_868_ = lean_string_utf8_byte_size(v_s_865_);
    v___x_869_ = lean_nat_dec_lt(v_i_867_, v___x_868_);
    if v___x_869_ == 0 {
        let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_871_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_i_867_);
        v___x_870_ = leanh::lean_box(0);
        v___x_871_ = leanh::lean_apply_1(v_f_866_, v___x_870_);
        v___x_872_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_872_, 0, v___x_871_);
        v___x_873_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_873_, 0, v___x_872_);
        return v___x_873_;
    } else {
        let mut v_c_874_: u8 = 0;
        let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_t_877_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v_i_867_);
        v_c_874_ = lean_string_get_byte_fast(v_s_865_, v_i_867_);
        v___x_875_ = leanh::lean_unsigned_to_nat(1);
        v___x_876_ = lean_nat_add(v_i_867_, v___x_875_);
        leanh::lean_dec(v_i_867_);
        v_t_877_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(
            v_s_865_, v_f_866_, v___x_876_,
        );
        v___x_878_ = leanh::lean_box(0);
        v___x_879_ = leanh::lean_alloc_ctor(1, 2, (1) as u32);
        leanh::lean_ctor_set(v___x_879_, 0, v___x_878_);
        leanh::lean_ctor_set(v___x_879_, 1, v_t_877_);
        leanh::lean_ctor_set_uint8(
            v___x_879_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
            v_c_874_,
        );
        return v___x_879_;
    }
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg___boxed(
    mut v_s_880_: *mut leanh::LeanObject,
    mut v_f_881_: *mut leanh::LeanObject,
    mut v_i_882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_883_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(
        v_s_880_, v_f_881_, v_i_882_,
    );
    leanh::lean_dec_ref(v_s_880_);
    return v_res_883_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty(
    mut v_00_u03b1_884_: *mut leanh::LeanObject,
    mut v_s_885_: *mut leanh::LeanObject,
    mut v_f_886_: *mut leanh::LeanObject,
    mut v_i_887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_888_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(
        v_s_885_, v_f_886_, v_i_887_,
    );
    return v___x_888_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___boxed(
    mut v_00_u03b1_889_: *mut leanh::LeanObject,
    mut v_s_890_: *mut leanh::LeanObject,
    mut v_f_891_: *mut leanh::LeanObject,
    mut v_i_892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_893_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty(
        v_00_u03b1_889_,
        v_s_890_,
        v_f_891_,
        v_i_892_,
    );
    leanh::lean_dec_ref(v_s_890_);
    return v_res_893_;
}
pub unsafe fn l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(
    mut v_c_894_: u8,
    mut v_a_895_: *mut leanh::LeanObject,
    mut v_i_896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: u8 = 0;
    let mut v___x_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: u8 = 0;
    let mut v___x_901_: u8 = 0;
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_897_ = lean_byte_array_size(v_a_895_);
                v___x_898_ = lean_nat_dec_lt(v_i_896_, v___x_897_);
                if v___x_898_ == 0 {
                    leanh::lean_dec(v_i_896_);
                    v___x_899_ = leanh::lean_box(0);
                    return v___x_899_;
                } else {
                    v___x_900_ = lean_byte_array_fget(v_a_895_, v_i_896_);
                    v___x_901_ = lean_uint8_dec_eq(v___x_900_, v_c_894_);
                    if v___x_901_ == 0 {
                        v___x_902_ = leanh::lean_unsigned_to_nat(1);
                        v___x_903_ = lean_nat_add(v_i_896_, v___x_902_);
                        leanh::lean_dec(v_i_896_);
                        v_i_896_ = v___x_903_;
                        state = 0;
                        continue;
                    } else {
                        v___x_905_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_905_, 0, v_i_896_);
                        return v___x_905_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0___boxed(
    mut v_c_906_: *mut leanh::LeanObject,
    mut v_a_907_: *mut leanh::LeanObject,
    mut v_i_908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_909_: u8 = 0;
    let mut v_res_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_909_ = (leanh::lean_unbox(v_c_906_) as u8);
    v_res_910_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_boxed_909_, v_a_907_, v_i_908_);
    leanh::lean_dec_ref(v_a_907_);
    return v_res_910_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(
    mut v_s_911_: *mut leanh::LeanObject,
    mut v_f_912_: *mut leanh::LeanObject,
    mut v_x_913_: *mut leanh::LeanObject,
    mut v_x_914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_918_: u8 = 0;
    let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: u8 = 0;
    let mut v___x_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_926_: u8 = 0;
    let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_931_: u8 = 0;
    let mut v_a_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_933_: u8 = 0;
    let mut v_a_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_937_: u8 = 0;
    let mut v___x_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: u8 = 0;
    let mut v___x_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_945_: u8 = 0;
    let mut v___x_946_: u8 = 0;
    let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_966_: u8 = 0;
    let mut v_a_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: u8 = 0;
    let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_974_: u8 = 0;
    let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_980_: u8 = 0;
    let mut v_unused_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_984_: u8 = 0;
    let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_989_: u8 = 0;
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_998_: u8 = 0;
    let mut v_unused_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: u8 = 0;
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1007_: u8 = 0;
    let mut v___x_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1018_: u8 = 0;
    let mut v_unused_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_914_) {
                0 => {
                    v_a_915_ = leanh::lean_ctor_get(v_x_914_, 0);
                    v_isSharedCheck_931_ = (!leanh::lean_is_exclusive(v_x_914_)) as u8;
                    if v_isSharedCheck_931_ == 0 {
                        v___x_917_ = v_x_914_;
                        v_isShared_918_ = v_isSharedCheck_931_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_915_);
                        leanh::lean_dec(v_x_914_);
                        v___x_917_ = leanh::lean_box(0);
                        v_isShared_918_ = v_isSharedCheck_931_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_932_ = leanh::lean_ctor_get(v_x_914_, 0);
                    v_a_933_ = leanh::lean_ctor_get_uint8(
                        v_x_914_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v_a_934_ = leanh::lean_ctor_get(v_x_914_, 1);
                    v_isSharedCheck_966_ = (!leanh::lean_is_exclusive(v_x_914_)) as u8;
                    if v_isSharedCheck_966_ == 0 {
                        v___x_936_ = v_x_914_;
                        v_isShared_937_ = v_isSharedCheck_966_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_934_);
                        leanh::lean_inc(v_a_932_);
                        leanh::lean_dec(v_x_914_);
                        v___x_936_ = leanh::lean_box(0);
                        v_isShared_937_ = v_isSharedCheck_966_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v_a_967_ = leanh::lean_ctor_get(v_x_914_, 0);
                    v_a_968_ = leanh::lean_ctor_get(v_x_914_, 1);
                    v_a_969_ = leanh::lean_ctor_get(v_x_914_, 2);
                    v___x_970_ = lean_string_utf8_byte_size(v_s_911_);
                    v___x_971_ = lean_nat_dec_lt(v_x_913_, v___x_970_);
                    if v___x_971_ == 0 {
                        leanh::lean_inc_ref(v_a_969_);
                        leanh::lean_inc_ref(v_a_968_);
                        leanh::lean_inc(v_a_967_);
                        leanh::lean_dec(v_x_913_);
                        v_isSharedCheck_980_ = (!leanh::lean_is_exclusive(v_x_914_)) as u8;
                        if v_isSharedCheck_980_ == 0 {
                            v_unused_981_ = leanh::lean_ctor_get(v_x_914_, 2);
                            leanh::lean_dec(v_unused_981_);
                            v_unused_982_ = leanh::lean_ctor_get(v_x_914_, 1);
                            leanh::lean_dec(v_unused_982_);
                            v_unused_983_ = leanh::lean_ctor_get(v_x_914_, 0);
                            leanh::lean_dec(v_unused_983_);
                            v___x_973_ = v_x_914_;
                            v_isShared_974_ = v_isSharedCheck_980_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_914_);
                            v___x_973_ = leanh::lean_box(0);
                            v_isShared_974_ = v_isSharedCheck_980_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_x_913_);
                        v_c_984_ = lean_string_get_byte_fast(v_s_911_, v_x_913_);
                        v___x_985_ = leanh::lean_unsigned_to_nat(0);
                        v___x_986_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_984_, v_a_968_, v___x_985_);
                        if leanh::lean_obj_tag(v___x_986_) == 0 {
                            leanh::lean_inc_ref(v_a_969_);
                            leanh::lean_inc_ref(v_a_968_);
                            leanh::lean_inc(v_a_967_);
                            v_isSharedCheck_998_ =
                                (!leanh::lean_is_exclusive(v_x_914_)) as u8;
                            if v_isSharedCheck_998_ == 0 {
                                v_unused_999_ = leanh::lean_ctor_get(v_x_914_, 2);
                                leanh::lean_dec(v_unused_999_);
                                v_unused_1000_ = leanh::lean_ctor_get(v_x_914_, 1);
                                leanh::lean_dec(v_unused_1000_);
                                v_unused_1001_ = leanh::lean_ctor_get(v_x_914_, 0);
                                leanh::lean_dec(v_unused_1001_);
                                v___x_988_ = v_x_914_;
                                v_isShared_989_ = v_isSharedCheck_998_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_dec(v_x_914_);
                                v___x_988_ = leanh::lean_box(0);
                                v_isShared_989_ = v_isSharedCheck_998_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v_val_1002_ = leanh::lean_ctor_get(v___x_986_, 0);
                            leanh::lean_inc(v_val_1002_);
                            leanh::lean_dec_ref_known(v___x_986_, 1);
                            v___x_1003_ = lean_array_get_size(v_a_969_);
                            v___x_1004_ = lean_nat_dec_lt(v_val_1002_, v___x_1003_);
                            if v___x_1004_ == 0 {
                                leanh::lean_dec(v_val_1002_);
                                leanh::lean_dec(v_x_913_);
                                leanh::lean_dec(v_f_912_);
                                return v_x_914_;
                            } else {
                                leanh::lean_inc_ref(v_a_969_);
                                leanh::lean_inc_ref(v_a_968_);
                                leanh::lean_inc(v_a_967_);
                                v_isSharedCheck_1018_ =
                                    (!leanh::lean_is_exclusive(v_x_914_)) as u8;
                                if v_isSharedCheck_1018_ == 0 {
                                    v_unused_1019_ = leanh::lean_ctor_get(v_x_914_, 2);
                                    leanh::lean_dec(v_unused_1019_);
                                    v_unused_1020_ = leanh::lean_ctor_get(v_x_914_, 1);
                                    leanh::lean_dec(v_unused_1020_);
                                    v_unused_1021_ = leanh::lean_ctor_get(v_x_914_, 0);
                                    leanh::lean_dec(v_unused_1021_);
                                    v___x_1006_ = v_x_914_;
                                    v_isShared_1007_ = v_isSharedCheck_1018_;
                                    state = 10;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_x_914_);
                                    v___x_1006_ = leanh::lean_box(0);
                                    v_isShared_1007_ = v_isSharedCheck_1018_;
                                    state = 10;
                                    continue;
                                }
                            }
                        }
                    }
                }
            },
            1 => {
                v___x_919_ = lean_string_utf8_byte_size(v_s_911_);
                v___x_920_ = lean_nat_dec_lt(v_x_913_, v___x_919_);
                if v___x_920_ == 0 {
                    leanh::lean_dec(v_x_913_);
                    v___x_921_ = leanh::lean_apply_1(v_f_912_, v_a_915_);
                    v___x_922_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_922_, 0, v___x_921_);
                    if v_isShared_918_ == 0 {
                        leanh::lean_ctor_set(v___x_917_, 0, v___x_922_);
                        v___x_924_ = v___x_917_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_925_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
                        v___x_924_ = v_reuseFailAlloc_925_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_917_);
                    leanh::lean_inc(v_x_913_);
                    v_c_926_ = lean_string_get_byte_fast(v_s_911_, v_x_913_);
                    v___x_927_ = leanh::lean_unsigned_to_nat(1);
                    v___x_928_ = lean_nat_add(v_x_913_, v___x_927_);
                    leanh::lean_dec(v_x_913_);
                    v_t_929_ =
                        l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(
                            v_s_911_, v_f_912_, v___x_928_,
                        );
                    v___x_930_ = leanh::lean_alloc_ctor(1, 2, (1) as u32);
                    leanh::lean_ctor_set(v___x_930_, 0, v_a_915_);
                    leanh::lean_ctor_set(v___x_930_, 1, v_t_929_);
                    leanh::lean_ctor_set_uint8(
                        v___x_930_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_c_926_,
                    );
                    return v___x_930_;
                }
            }
            2 => {
                return v___x_924_;
            }
            3 => {
                v___x_938_ = lean_string_utf8_byte_size(v_s_911_);
                v___x_939_ = lean_nat_dec_lt(v_x_913_, v___x_938_);
                if v___x_939_ == 0 {
                    leanh::lean_dec(v_x_913_);
                    v___x_940_ = leanh::lean_apply_1(v_f_912_, v_a_932_);
                    v___x_941_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_941_, 0, v___x_940_);
                    if v_isShared_937_ == 0 {
                        leanh::lean_ctor_set(v___x_936_, 0, v___x_941_);
                        v___x_943_ = v___x_936_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_944_ = leanh::lean_alloc_ctor(1, 2, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_941_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_944_, 1, v_a_934_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_944_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                            v_a_933_,
                        );
                        v___x_943_ = v_reuseFailAlloc_944_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_x_913_);
                    v_c_945_ = lean_string_get_byte_fast(v_s_911_, v_x_913_);
                    v___x_946_ = lean_uint8_dec_eq(v_c_945_, v_a_933_);
                    if v___x_946_ == 0 {
                        leanh::lean_del_object(v___x_936_);
                        v___x_947_ = leanh::lean_unsigned_to_nat(1);
                        v___x_948_ = lean_nat_add(v_x_913_, v___x_947_);
                        leanh::lean_dec(v_x_913_);
                        v_t_949_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_911_, v_f_912_, v___x_948_);
                        v___x_950_ = leanh::lean_unsigned_to_nat(2);
                        v___x_951_ = lean_mk_empty_array_with_capacity(v___x_950_);
                        v___x_952_ = leanh::lean_box((v_c_945_) as usize);
                        leanh::lean_inc_ref(v___x_951_);
                        v___x_953_ = lean_array_push(v___x_951_, v___x_952_);
                        v___x_954_ = leanh::lean_box((v_a_933_) as usize);
                        v___x_955_ = lean_array_push(v___x_953_, v___x_954_);
                        v___x_956_ = lean_byte_array_mk(v___x_955_);
                        v___x_957_ = lean_array_push(v___x_951_, v_t_949_);
                        v___x_958_ = lean_array_push(v___x_957_, v_a_934_);
                        v___x_959_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_959_, 0, v_a_932_);
                        leanh::lean_ctor_set(v___x_959_, 1, v___x_956_);
                        leanh::lean_ctor_set(v___x_959_, 2, v___x_958_);
                        return v___x_959_;
                    } else {
                        v___x_960_ = leanh::lean_unsigned_to_nat(1);
                        v___x_961_ = lean_nat_add(v_x_913_, v___x_960_);
                        leanh::lean_dec(v_x_913_);
                        v___x_962_ =
                            l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(
                                v_s_911_, v_f_912_, v___x_961_, v_a_934_,
                            );
                        if v_isShared_937_ == 0 {
                            leanh::lean_ctor_set(v___x_936_, 1, v___x_962_);
                            v___x_964_ = v___x_936_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_965_ = leanh::lean_alloc_ctor(1, 2, (1) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_932_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_965_, 1, v___x_962_);
                            leanh::lean_ctor_set_uint8(
                                v_reuseFailAlloc_965_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                                v_a_933_,
                            );
                            v___x_964_ = v_reuseFailAlloc_965_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_943_;
            }
            5 => {
                return v___x_964_;
            }
            6 => {
                v___x_975_ = leanh::lean_apply_1(v_f_912_, v_a_967_);
                v___x_976_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_976_, 0, v___x_975_);
                if v_isShared_974_ == 0 {
                    leanh::lean_ctor_set(v___x_973_, 0, v___x_976_);
                    v___x_978_ = v___x_973_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_979_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_976_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_979_, 1, v_a_968_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_979_, 2, v_a_969_);
                    v___x_978_ = v_reuseFailAlloc_979_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_978_;
            }
            8 => {
                v___x_990_ = leanh::lean_unsigned_to_nat(1);
                v___x_991_ = lean_nat_add(v_x_913_, v___x_990_);
                leanh::lean_dec(v_x_913_);
                v_t_992_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(
                    v_s_911_, v_f_912_, v___x_991_,
                );
                v___x_993_ = lean_byte_array_push(v_a_968_, v_c_984_);
                v___x_994_ = lean_array_push(v_a_969_, v_t_992_);
                if v_isShared_989_ == 0 {
                    leanh::lean_ctor_set(v___x_988_, 2, v___x_994_);
                    leanh::lean_ctor_set(v___x_988_, 1, v___x_993_);
                    v___x_996_ = v___x_988_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_997_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_967_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_997_, 1, v___x_993_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_997_, 2, v___x_994_);
                    v___x_996_ = v_reuseFailAlloc_997_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_996_;
            }
            10 => {
                v___x_1008_ = leanh::lean_unsigned_to_nat(1);
                v___x_1009_ = lean_nat_add(v_x_913_, v___x_1008_);
                leanh::lean_dec(v_x_913_);
                v_v_1010_ = lean_array_fget(v_a_969_, v_val_1002_);
                v___x_1011_ = leanh::lean_box(0);
                v_xs_x27_1012_ = lean_array_fset(v_a_969_, v_val_1002_, v___x_1011_);
                v___x_1013_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(
                    v_s_911_,
                    v_f_912_,
                    v___x_1009_,
                    v_v_1010_,
                );
                v___x_1014_ = lean_array_fset(v_xs_x27_1012_, v_val_1002_, v___x_1013_);
                leanh::lean_dec(v_val_1002_);
                if v_isShared_1007_ == 0 {
                    leanh::lean_ctor_set(v___x_1006_, 2, v___x_1014_);
                    v___x_1016_ = v___x_1006_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1017_ = leanh::lean_alloc_ctor(2, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_967_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_a_968_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1017_, 2, v___x_1014_);
                    v___x_1016_ = v_reuseFailAlloc_1017_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1016_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg___boxed(
    mut v_s_1022_: *mut leanh::LeanObject,
    mut v_f_1023_: *mut leanh::LeanObject,
    mut v_x_1024_: *mut leanh::LeanObject,
    mut v_x_1025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1026_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(
        v_s_1022_, v_f_1023_, v_x_1024_, v_x_1025_,
    );
    leanh::lean_dec_ref(v_s_1022_);
    return v_res_1026_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop(
    mut v_00_u03b1_1027_: *mut leanh::LeanObject,
    mut v_s_1028_: *mut leanh::LeanObject,
    mut v_f_1029_: *mut leanh::LeanObject,
    mut v_x_1030_: *mut leanh::LeanObject,
    mut v_x_1031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1032_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(
        v_s_1028_, v_f_1029_, v_x_1030_, v_x_1031_,
    );
    return v___x_1032_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___boxed(
    mut v_00_u03b1_1033_: *mut leanh::LeanObject,
    mut v_s_1034_: *mut leanh::LeanObject,
    mut v_f_1035_: *mut leanh::LeanObject,
    mut v_x_1036_: *mut leanh::LeanObject,
    mut v_x_1037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1038_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop(
        v_00_u03b1_1033_,
        v_s_1034_,
        v_f_1035_,
        v_x_1036_,
        v_x_1037_,
    );
    leanh::lean_dec_ref(v_s_1034_);
    return v_res_1038_;
}
pub unsafe fn l_Lean_Data_Trie_upsert___redArg(
    mut v_t_1039_: *mut leanh::LeanObject,
    mut v_s_1040_: *mut leanh::LeanObject,
    mut v_f_1041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1042_ = leanh::lean_unsigned_to_nat(0);
    v___x_1043_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(
        v_s_1040_,
        v_f_1041_,
        v___x_1042_,
        v_t_1039_,
    );
    return v___x_1043_;
}
pub unsafe fn l_Lean_Data_Trie_upsert___redArg___boxed(
    mut v_t_1044_: *mut leanh::LeanObject,
    mut v_s_1045_: *mut leanh::LeanObject,
    mut v_f_1046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1047_ = l_Lean_Data_Trie_upsert___redArg(v_t_1044_, v_s_1045_, v_f_1046_);
    leanh::lean_dec_ref(v_s_1045_);
    return v_res_1047_;
}
pub unsafe fn l_Lean_Data_Trie_upsert(
    mut v_00_u03b1_1048_: *mut leanh::LeanObject,
    mut v_t_1049_: *mut leanh::LeanObject,
    mut v_s_1050_: *mut leanh::LeanObject,
    mut v_f_1051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1052_ = l_Lean_Data_Trie_upsert___redArg(v_t_1049_, v_s_1050_, v_f_1051_);
    return v___x_1052_;
}
pub unsafe fn l_Lean_Data_Trie_upsert___boxed(
    mut v_00_u03b1_1053_: *mut leanh::LeanObject,
    mut v_t_1054_: *mut leanh::LeanObject,
    mut v_s_1055_: *mut leanh::LeanObject,
    mut v_f_1056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1057_ = l_Lean_Data_Trie_upsert(v_00_u03b1_1053_, v_t_1054_, v_s_1055_, v_f_1056_);
    leanh::lean_dec_ref(v_s_1055_);
    return v_res_1057_;
}
pub unsafe fn l_Lean_Data_Trie_insert___redArg___lam__0(
    mut v_val_1058_: *mut leanh::LeanObject,
    mut v_x_1059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_val_1058_);
    return v_val_1058_;
}
pub unsafe fn l_Lean_Data_Trie_insert___redArg___lam__0___boxed(
    mut v_val_1060_: *mut leanh::LeanObject,
    mut v_x_1061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1062_ = l_Lean_Data_Trie_insert___redArg___lam__0(v_val_1060_, v_x_1061_);
    leanh::lean_dec(v_x_1061_);
    leanh::lean_dec(v_val_1060_);
    return v_res_1062_;
}
pub unsafe fn l_Lean_Data_Trie_insert___redArg(
    mut v_t_1063_: *mut leanh::LeanObject,
    mut v_s_1064_: *mut leanh::LeanObject,
    mut v_val_1065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1066_ = leanh::lean_alloc_closure(
        l_Lean_Data_Trie_insert___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1066_, 0, v_val_1065_);
    v___x_1067_ = l_Lean_Data_Trie_upsert___redArg(v_t_1063_, v_s_1064_, v___f_1066_);
    return v___x_1067_;
}
pub unsafe fn l_Lean_Data_Trie_insert___redArg___boxed(
    mut v_t_1068_: *mut leanh::LeanObject,
    mut v_s_1069_: *mut leanh::LeanObject,
    mut v_val_1070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1071_ = l_Lean_Data_Trie_insert___redArg(v_t_1068_, v_s_1069_, v_val_1070_);
    leanh::lean_dec_ref(v_s_1069_);
    return v_res_1071_;
}
pub unsafe fn l_Lean_Data_Trie_insert(
    mut v_00_u03b1_1072_: *mut leanh::LeanObject,
    mut v_t_1073_: *mut leanh::LeanObject,
    mut v_s_1074_: *mut leanh::LeanObject,
    mut v_val_1075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1076_ = l_Lean_Data_Trie_insert___redArg(v_t_1073_, v_s_1074_, v_val_1075_);
    return v___x_1076_;
}
pub unsafe fn l_Lean_Data_Trie_insert___boxed(
    mut v_00_u03b1_1077_: *mut leanh::LeanObject,
    mut v_t_1078_: *mut leanh::LeanObject,
    mut v_s_1079_: *mut leanh::LeanObject,
    mut v_val_1080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1081_ = l_Lean_Data_Trie_insert(v_00_u03b1_1077_, v_t_1078_, v_s_1079_, v_val_1080_);
    leanh::lean_dec_ref(v_s_1079_);
    return v_res_1081_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg(
    mut v_s_1082_: *mut leanh::LeanObject,
    mut v_x_1083_: *mut leanh::LeanObject,
    mut v_x_1084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: u8 = 0;
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1090_: u8 = 0;
    let mut v_a_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: u8 = 0;
    let mut v_c_1094_: u8 = 0;
    let mut v___x_1095_: u8 = 0;
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: u8 = 0;
    let mut v_c_1105_: u8 = 0;
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1084_) {
                0 => {
                    v_a_1085_ = leanh::lean_ctor_get(v_x_1084_, 0);
                    v___x_1086_ = lean_string_utf8_byte_size(v_s_1082_);
                    v___x_1087_ = lean_nat_dec_lt(v_x_1083_, v___x_1086_);
                    leanh::lean_dec(v_x_1083_);
                    if v___x_1087_ == 0 {
                        leanh::lean_inc(v_a_1085_);
                        return v_a_1085_;
                    } else {
                        v___x_1088_ = leanh::lean_box(0);
                        return v___x_1088_;
                    }
                }
                1 => {
                    v_a_1089_ = leanh::lean_ctor_get(v_x_1084_, 0);
                    v_a_1090_ = leanh::lean_ctor_get_uint8(
                        v_x_1084_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v_a_1091_ = leanh::lean_ctor_get(v_x_1084_, 1);
                    v___x_1092_ = lean_string_utf8_byte_size(v_s_1082_);
                    v___x_1093_ = lean_nat_dec_lt(v_x_1083_, v___x_1092_);
                    if v___x_1093_ == 0 {
                        leanh::lean_dec(v_x_1083_);
                        leanh::lean_inc(v_a_1089_);
                        return v_a_1089_;
                    } else {
                        leanh::lean_inc(v_x_1083_);
                        v_c_1094_ = lean_string_get_byte_fast(v_s_1082_, v_x_1083_);
                        v___x_1095_ = lean_uint8_dec_eq(v_c_1094_, v_a_1090_);
                        if v___x_1095_ == 0 {
                            leanh::lean_dec(v_x_1083_);
                            v___x_1096_ = leanh::lean_box(0);
                            return v___x_1096_;
                        } else {
                            v___x_1097_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1098_ = lean_nat_add(v_x_1083_, v___x_1097_);
                            leanh::lean_dec(v_x_1083_);
                            v_x_1083_ = v___x_1098_;
                            v_x_1084_ = v_a_1091_;
                            state = 0;
                            continue;
                        }
                    }
                }
                _ => {
                    v_a_1100_ = leanh::lean_ctor_get(v_x_1084_, 0);
                    v_a_1101_ = leanh::lean_ctor_get(v_x_1084_, 1);
                    v_a_1102_ = leanh::lean_ctor_get(v_x_1084_, 2);
                    v___x_1103_ = lean_string_utf8_byte_size(v_s_1082_);
                    v___x_1104_ = lean_nat_dec_lt(v_x_1083_, v___x_1103_);
                    if v___x_1104_ == 0 {
                        leanh::lean_dec(v_x_1083_);
                        leanh::lean_inc(v_a_1100_);
                        return v_a_1100_;
                    } else {
                        leanh::lean_inc(v_x_1083_);
                        v_c_1105_ = lean_string_get_byte_fast(v_s_1082_, v_x_1083_);
                        v___x_1106_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1107_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_1105_, v_a_1101_, v___x_1106_);
                        if leanh::lean_obj_tag(v___x_1107_) == 0 {
                            leanh::lean_dec(v_x_1083_);
                            v___x_1108_ = leanh::lean_box(0);
                            return v___x_1108_;
                        } else {
                            v_val_1109_ = leanh::lean_ctor_get(v___x_1107_, 0);
                            leanh::lean_inc(v_val_1109_);
                            leanh::lean_dec_ref_known(v___x_1107_, 1);
                            v___x_1110_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1111_ = lean_nat_add(v_x_1083_, v___x_1110_);
                            leanh::lean_dec(v_x_1083_);
                            v___x_1112_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Data_Trie_instEmptyCollection___closed__0
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Data_Trie_instEmptyCollection___closed__0_once
                                ),
                                _init_l_Lean_Data_Trie_instEmptyCollection___closed__0,
                            );
                            v___x_1113_ =
                                lean_array_get_borrowed(v___x_1112_, v_a_1102_, v_val_1109_);
                            leanh::lean_dec(v_val_1109_);
                            v_x_1083_ = v___x_1111_;
                            v_x_1084_ = v___x_1113_;
                            state = 0;
                            continue;
                        }
                    }
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg___boxed(
    mut v_s_1115_: *mut leanh::LeanObject,
    mut v_x_1116_: *mut leanh::LeanObject,
    mut v_x_1117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1118_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg(
        v_s_1115_, v_x_1116_, v_x_1117_,
    );
    leanh::lean_dec_ref(v_x_1117_);
    leanh::lean_dec_ref(v_s_1115_);
    return v_res_1118_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop(
    mut v_00_u03b1_1119_: *mut leanh::LeanObject,
    mut v_s_1120_: *mut leanh::LeanObject,
    mut v_x_1121_: *mut leanh::LeanObject,
    mut v_x_1122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1123_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg(
        v_s_1120_, v_x_1121_, v_x_1122_,
    );
    return v___x_1123_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___boxed(
    mut v_00_u03b1_1124_: *mut leanh::LeanObject,
    mut v_s_1125_: *mut leanh::LeanObject,
    mut v_x_1126_: *mut leanh::LeanObject,
    mut v_x_1127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1128_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop(
        v_00_u03b1_1124_,
        v_s_1125_,
        v_x_1126_,
        v_x_1127_,
    );
    leanh::lean_dec_ref(v_x_1127_);
    leanh::lean_dec_ref(v_s_1125_);
    return v_res_1128_;
}
pub unsafe fn l_Lean_Data_Trie_find_x3f___redArg(
    mut v_t_1129_: *mut leanh::LeanObject,
    mut v_s_1130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1131_ = leanh::lean_unsigned_to_nat(0);
    v___x_1132_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg(
        v_s_1130_,
        v___x_1131_,
        v_t_1129_,
    );
    return v___x_1132_;
}
pub unsafe fn l_Lean_Data_Trie_find_x3f___redArg___boxed(
    mut v_t_1133_: *mut leanh::LeanObject,
    mut v_s_1134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1135_ = l_Lean_Data_Trie_find_x3f___redArg(v_t_1133_, v_s_1134_);
    leanh::lean_dec_ref(v_s_1134_);
    leanh::lean_dec_ref(v_t_1133_);
    return v_res_1135_;
}
pub unsafe fn l_Lean_Data_Trie_find_x3f(
    mut v_00_u03b1_1136_: *mut leanh::LeanObject,
    mut v_t_1137_: *mut leanh::LeanObject,
    mut v_s_1138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1139_ = l_Lean_Data_Trie_find_x3f___redArg(v_t_1137_, v_s_1138_);
    return v___x_1139_;
}
pub unsafe fn l_Lean_Data_Trie_find_x3f___boxed(
    mut v_00_u03b1_1140_: *mut leanh::LeanObject,
    mut v_t_1141_: *mut leanh::LeanObject,
    mut v_s_1142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1143_ = l_Lean_Data_Trie_find_x3f(v_00_u03b1_1140_, v_t_1141_, v_s_1142_);
    leanh::lean_dec_ref(v_s_1142_);
    leanh::lean_dec_ref(v_t_1141_);
    return v_res_1143_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(
    mut v_a_1144_: *mut leanh::LeanObject,
    mut v_a_1145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: u8 = 0;
    let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: u8 = 0;
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: usize = 0;
    let mut v___x_1172_: usize = 0;
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: usize = 0;
    let mut v___x_1175_: usize = 0;
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_a_1144_) {
                0 => {
                    v_a_1146_ = leanh::lean_ctor_get(v_a_1144_, 0);
                    if leanh::lean_obj_tag(v_a_1146_) == 1 {
                        v_val_1147_ = leanh::lean_ctor_get(v_a_1146_, 0);
                        v___x_1148_ = leanh::lean_box(0);
                        leanh::lean_inc(v_val_1147_);
                        v___x_1149_ = lean_array_push(v_a_1145_, v_val_1147_);
                        v___x_1150_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1150_, 0, v___x_1148_);
                        leanh::lean_ctor_set(v___x_1150_, 1, v___x_1149_);
                        return v___x_1150_;
                    } else {
                        v___x_1151_ = leanh::lean_box(0);
                        v___x_1152_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1152_, 0, v___x_1151_);
                        leanh::lean_ctor_set(v___x_1152_, 1, v_a_1145_);
                        return v___x_1152_;
                    }
                }
                1 => {
                    v_a_1153_ = leanh::lean_ctor_get(v_a_1144_, 0);
                    if leanh::lean_obj_tag(v_a_1153_) == 1 {
                        v_a_1154_ = leanh::lean_ctor_get(v_a_1144_, 1);
                        v_val_1155_ = leanh::lean_ctor_get(v_a_1153_, 0);
                        leanh::lean_inc(v_val_1155_);
                        v___x_1156_ = lean_array_push(v_a_1145_, v_val_1155_);
                        v_a_1144_ = v_a_1154_;
                        v_a_1145_ = v___x_1156_;
                        state = 0;
                        continue;
                    } else {
                        v_a_1158_ = leanh::lean_ctor_get(v_a_1144_, 1);
                        v_a_1144_ = v_a_1158_;
                        state = 0;
                        continue;
                    }
                }
                _ => {
                    v_a_1160_ = leanh::lean_ctor_get(v_a_1144_, 0);
                    v_a_1161_ = leanh::lean_ctor_get(v_a_1144_, 2);
                    if leanh::lean_obj_tag(v_a_1160_) == 1 {
                        v_val_1177_ = leanh::lean_ctor_get(v_a_1160_, 0);
                        leanh::lean_inc(v_val_1177_);
                        v___x_1178_ = lean_array_push(v_a_1145_, v_val_1177_);
                        v___y_1163_ = v___x_1178_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1163_ = v_a_1145_;
                        state = 1;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1164_ = leanh::lean_unsigned_to_nat(0);
                v___x_1165_ = lean_array_get_size(v_a_1161_);
                v___x_1166_ = leanh::lean_box(0);
                v___x_1167_ = lean_nat_dec_lt(v___x_1164_, v___x_1165_);
                if v___x_1167_ == 0 {
                    v___x_1168_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1168_, 0, v___x_1166_);
                    leanh::lean_ctor_set(v___x_1168_, 1, v___y_1163_);
                    return v___x_1168_;
                } else {
                    v___x_1169_ = lean_nat_dec_le(v___x_1165_, v___x_1165_);
                    if v___x_1169_ == 0 {
                        if v___x_1167_ == 0 {
                            v___x_1170_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1170_, 0, v___x_1166_);
                            leanh::lean_ctor_set(v___x_1170_, 1, v___y_1163_);
                            return v___x_1170_;
                        } else {
                            v___x_1171_ = 0usize;
                            v___x_1172_ = lean_usize_of_nat(v___x_1165_);
                            v___x_1173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(v_a_1161_, v___x_1171_, v___x_1172_, v___x_1166_, v___y_1163_);
                            return v___x_1173_;
                        }
                    } else {
                        v___x_1174_ = 0usize;
                        v___x_1175_ = lean_usize_of_nat(v___x_1165_);
                        v___x_1176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(v_a_1161_, v___x_1174_, v___x_1175_, v___x_1166_, v___y_1163_);
                        return v___x_1176_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(
    mut v_as_1179_: *mut leanh::LeanObject,
    mut v_i_1180_: usize,
    mut v_stop_1181_: usize,
    mut v_b_1182_: *mut leanh::LeanObject,
    mut v___y_1183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1184_: u8 = 0;
    let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: usize = 0;
    let mut v___x_1190_: usize = 0;
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1184_ = lean_usize_dec_eq(v_i_1180_, v_stop_1181_);
                if v___x_1184_ == 0 {
                    v___x_1185_ = lean_array_uget_borrowed(v_as_1179_, v_i_1180_);
                    v___x_1186_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(
                        v___x_1185_,
                        v___y_1183_,
                    );
                    v_fst_1187_ = leanh::lean_ctor_get(v___x_1186_, 0);
                    leanh::lean_inc(v_fst_1187_);
                    v_snd_1188_ = leanh::lean_ctor_get(v___x_1186_, 1);
                    leanh::lean_inc(v_snd_1188_);
                    leanh::lean_dec_ref(v___x_1186_);
                    v___x_1189_ = 1usize;
                    v___x_1190_ = lean_usize_add(v_i_1180_, v___x_1189_);
                    v_i_1180_ = v___x_1190_;
                    v_b_1182_ = v_fst_1187_;
                    v___y_1183_ = v_snd_1188_;
                    state = 0;
                    continue;
                } else {
                    v___x_1192_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1192_, 0, v_b_1182_);
                    leanh::lean_ctor_set(v___x_1192_, 1, v___y_1183_);
                    return v___x_1192_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg___boxed(
    mut v_as_1193_: *mut leanh::LeanObject,
    mut v_i_1194_: *mut leanh::LeanObject,
    mut v_stop_1195_: *mut leanh::LeanObject,
    mut v_b_1196_: *mut leanh::LeanObject,
    mut v___y_1197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1198_: usize = 0;
    let mut v_stop_boxed_1199_: usize = 0;
    let mut v_res_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1198_ = leanh::lean_unbox_usize(v_i_1194_);
    leanh::lean_dec(v_i_1194_);
    v_stop_boxed_1199_ = leanh::lean_unbox_usize(v_stop_1195_);
    leanh::lean_dec(v_stop_1195_);
    v_res_1200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(v_as_1193_, v_i_boxed_1198_, v_stop_boxed_1199_, v_b_1196_, v___y_1197_);
    leanh::lean_dec_ref(v_as_1193_);
    return v_res_1200_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg___boxed(
    mut v_a_1201_: *mut leanh::LeanObject,
    mut v_a_1202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1203_ =
        l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(v_a_1201_, v_a_1202_);
    leanh::lean_dec_ref(v_a_1201_);
    return v_res_1203_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go(
    mut v_00_u03b1_1204_: *mut leanh::LeanObject,
    mut v_a_1205_: *mut leanh::LeanObject,
    mut v_a_1206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1207_ =
        l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(v_a_1205_, v_a_1206_);
    return v___x_1207_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___boxed(
    mut v_00_u03b1_1208_: *mut leanh::LeanObject,
    mut v_a_1209_: *mut leanh::LeanObject,
    mut v_a_1210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1211_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go(
        v_00_u03b1_1208_,
        v_a_1209_,
        v_a_1210_,
    );
    leanh::lean_dec_ref(v_a_1209_);
    return v_res_1211_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0(
    mut v_00_u03b1_1212_: *mut leanh::LeanObject,
    mut v_as_1213_: *mut leanh::LeanObject,
    mut v_i_1214_: usize,
    mut v_stop_1215_: usize,
    mut v_b_1216_: *mut leanh::LeanObject,
    mut v___y_1217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(v_as_1213_, v_i_1214_, v_stop_1215_, v_b_1216_, v___y_1217_);
    return v___x_1218_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___boxed(
    mut v_00_u03b1_1219_: *mut leanh::LeanObject,
    mut v_as_1220_: *mut leanh::LeanObject,
    mut v_i_1221_: *mut leanh::LeanObject,
    mut v_stop_1222_: *mut leanh::LeanObject,
    mut v_b_1223_: *mut leanh::LeanObject,
    mut v___y_1224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1225_: usize = 0;
    let mut v_stop_boxed_1226_: usize = 0;
    let mut v_res_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1225_ = leanh::lean_unbox_usize(v_i_1221_);
    leanh::lean_dec(v_i_1221_);
    v_stop_boxed_1226_ = leanh::lean_unbox_usize(v_stop_1222_);
    leanh::lean_dec(v_stop_1222_);
    v_res_1227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0(v_00_u03b1_1219_, v_as_1220_, v_i_boxed_1225_, v_stop_boxed_1226_, v_b_1223_, v___y_1224_);
    leanh::lean_dec_ref(v_as_1220_);
    return v_res_1227_;
}
pub unsafe fn l_Lean_Data_Trie_values___redArg(
    mut v_t_1230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1231_ = l_Lean_Data_Trie_values___redArg___closed__0;
    v___x_1232_ =
        l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(v_t_1230_, v___x_1231_);
    v_snd_1233_ = leanh::lean_ctor_get(v___x_1232_, 1);
    leanh::lean_inc(v_snd_1233_);
    leanh::lean_dec_ref(v___x_1232_);
    return v_snd_1233_;
}
pub unsafe fn l_Lean_Data_Trie_values___redArg___boxed(
    mut v_t_1234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1235_ = l_Lean_Data_Trie_values___redArg(v_t_1234_);
    leanh::lean_dec_ref(v_t_1234_);
    return v_res_1235_;
}
pub unsafe fn l_Lean_Data_Trie_values(
    mut v_00_u03b1_1236_: *mut leanh::LeanObject,
    mut v_t_1237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1238_ = l_Lean_Data_Trie_values___redArg(v_t_1237_);
    return v___x_1238_;
}
pub unsafe fn l_Lean_Data_Trie_values___boxed(
    mut v_00_u03b1_1239_: *mut leanh::LeanObject,
    mut v_t_1240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1241_ = l_Lean_Data_Trie_values(v_00_u03b1_1239_, v_t_1240_);
    leanh::lean_dec_ref(v_t_1240_);
    return v_res_1241_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(
    mut v_pre_1244_: *mut leanh::LeanObject,
    mut v_t_1245_: *mut leanh::LeanObject,
    mut v_i_1246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: u8 = 0;
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1250_: u8 = 0;
    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1252_: u8 = 0;
    let mut v_a_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: u8 = 0;
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1247_ = lean_string_utf8_byte_size(v_pre_1244_);
                v___x_1248_ = lean_nat_dec_lt(v_i_1246_, v___x_1247_);
                if v___x_1248_ == 0 {
                    leanh::lean_dec(v_i_1246_);
                    v___x_1249_ = l_Lean_Data_Trie_values___redArg(v_t_1245_);
                    return v___x_1249_;
                } else {
                    leanh::lean_inc(v_i_1246_);
                    v_c_1250_ = lean_string_get_byte_fast(v_pre_1244_, v_i_1246_);
                    match leanh::lean_obj_tag(v_t_1245_) {
                        0 => {
                            leanh::lean_dec(v_i_1246_);
                            v___x_1251_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0;
                            return v___x_1251_;
                        }
                        1 => {
                            v_a_1252_ = leanh::lean_ctor_get_uint8(
                                v_t_1245_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                            );
                            v_a_1253_ = leanh::lean_ctor_get(v_t_1245_, 1);
                            v___x_1254_ = lean_uint8_dec_eq(v_c_1250_, v_a_1252_);
                            if v___x_1254_ == 0 {
                                leanh::lean_dec(v_i_1246_);
                                v___x_1255_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0;
                                return v___x_1255_;
                            } else {
                                v___x_1256_ = leanh::lean_unsigned_to_nat(1);
                                v___x_1257_ = lean_nat_add(v_i_1246_, v___x_1256_);
                                leanh::lean_dec(v_i_1246_);
                                v_t_1245_ = v_a_1253_;
                                v_i_1246_ = v___x_1257_;
                                state = 0;
                                continue;
                            }
                        }
                        _ => {
                            v_a_1259_ = leanh::lean_ctor_get(v_t_1245_, 1);
                            v_a_1260_ = leanh::lean_ctor_get(v_t_1245_, 2);
                            v___x_1261_ = leanh::lean_unsigned_to_nat(0);
                            v___x_1262_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_1250_, v_a_1259_, v___x_1261_);
                            if leanh::lean_obj_tag(v___x_1262_) == 0 {
                                leanh::lean_dec(v_i_1246_);
                                v___x_1263_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0;
                                return v___x_1263_;
                            } else {
                                v_val_1264_ = leanh::lean_ctor_get(v___x_1262_, 0);
                                leanh::lean_inc(v_val_1264_);
                                leanh::lean_dec_ref_known(v___x_1262_, 1);
                                v___x_1265_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Data_Trie_instEmptyCollection___closed__0
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Data_Trie_instEmptyCollection___closed__0_once
                                    ),
                                    _init_l_Lean_Data_Trie_instEmptyCollection___closed__0,
                                );
                                v___x_1266_ =
                                    lean_array_get_borrowed(v___x_1265_, v_a_1260_, v_val_1264_);
                                leanh::lean_dec(v_val_1264_);
                                v___x_1267_ = leanh::lean_unsigned_to_nat(1);
                                v___x_1268_ = lean_nat_add(v_i_1246_, v___x_1267_);
                                leanh::lean_dec(v_i_1246_);
                                v_t_1245_ = v___x_1266_;
                                v_i_1246_ = v___x_1268_;
                                state = 0;
                                continue;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___boxed(
    mut v_pre_1270_: *mut leanh::LeanObject,
    mut v_t_1271_: *mut leanh::LeanObject,
    mut v_i_1272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1273_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(
        v_pre_1270_,
        v_t_1271_,
        v_i_1272_,
    );
    leanh::lean_dec_ref(v_t_1271_);
    leanh::lean_dec_ref(v_pre_1270_);
    return v_res_1273_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go(
    mut v_00_u03b1_1274_: *mut leanh::LeanObject,
    mut v_pre_1275_: *mut leanh::LeanObject,
    mut v_t_1276_: *mut leanh::LeanObject,
    mut v_i_1277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1278_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(
        v_pre_1275_,
        v_t_1276_,
        v_i_1277_,
    );
    return v___x_1278_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___boxed(
    mut v_00_u03b1_1279_: *mut leanh::LeanObject,
    mut v_pre_1280_: *mut leanh::LeanObject,
    mut v_t_1281_: *mut leanh::LeanObject,
    mut v_i_1282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1283_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go(
        v_00_u03b1_1279_,
        v_pre_1280_,
        v_t_1281_,
        v_i_1282_,
    );
    leanh::lean_dec_ref(v_t_1281_);
    leanh::lean_dec_ref(v_pre_1280_);
    return v_res_1283_;
}
pub unsafe fn l_Lean_Data_Trie_findPrefix___redArg(
    mut v_t_1284_: *mut leanh::LeanObject,
    mut v_pre_1285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1286_ = leanh::lean_unsigned_to_nat(0);
    v___x_1287_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(
        v_pre_1285_,
        v_t_1284_,
        v___x_1286_,
    );
    return v___x_1287_;
}
pub unsafe fn l_Lean_Data_Trie_findPrefix___redArg___boxed(
    mut v_t_1288_: *mut leanh::LeanObject,
    mut v_pre_1289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1290_ = l_Lean_Data_Trie_findPrefix___redArg(v_t_1288_, v_pre_1289_);
    leanh::lean_dec_ref(v_pre_1289_);
    leanh::lean_dec_ref(v_t_1288_);
    return v_res_1290_;
}
pub unsafe fn l_Lean_Data_Trie_findPrefix(
    mut v_00_u03b1_1291_: *mut leanh::LeanObject,
    mut v_t_1292_: *mut leanh::LeanObject,
    mut v_pre_1293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1294_ = l_Lean_Data_Trie_findPrefix___redArg(v_t_1292_, v_pre_1293_);
    return v___x_1294_;
}
pub unsafe fn l_Lean_Data_Trie_findPrefix___boxed(
    mut v_00_u03b1_1295_: *mut leanh::LeanObject,
    mut v_t_1296_: *mut leanh::LeanObject,
    mut v_pre_1297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1298_ = l_Lean_Data_Trie_findPrefix(v_00_u03b1_1295_, v_t_1296_, v_pre_1297_);
    leanh::lean_dec_ref(v_pre_1297_);
    leanh::lean_dec_ref(v_t_1296_);
    return v_res_1298_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1325_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__10;
    v___x_1326_ = l_Lean_mkAtom(v___x_1325_);
    return v___x_1326_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1327_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__12_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__12,
    );
    v___x_1328_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__5;
    v___x_1329_ = lean_array_push(v___x_1328_, v___x_1327_);
    return v___x_1329_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1340_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__16;
    v___x_1341_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__5;
    v___x_1342_ = lean_array_push(v___x_1341_, v___x_1340_);
    return v___x_1342_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1343_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__17_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__17,
    );
    v___x_1344_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__15;
    v___x_1345_ = leanh::lean_box(2);
    v___x_1346_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1346_, 0, v___x_1345_);
    leanh::lean_ctor_set(v___x_1346_, 1, v___x_1344_);
    leanh::lean_ctor_set(v___x_1346_, 2, v___x_1343_);
    return v___x_1346_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1347_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__18_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__18,
    );
    v___x_1348_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__13_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__13,
    );
    v___x_1349_ = lean_array_push(v___x_1348_, v___x_1347_);
    return v___x_1349_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1350_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__16;
    v___x_1351_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__19_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__19,
    );
    v___x_1352_ = lean_array_push(v___x_1351_, v___x_1350_);
    return v___x_1352_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1353_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__16;
    v___x_1354_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__20_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__20,
    );
    v___x_1355_ = lean_array_push(v___x_1354_, v___x_1353_);
    return v___x_1355_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1356_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__16;
    v___x_1357_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__21_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__21,
    );
    v___x_1358_ = lean_array_push(v___x_1357_, v___x_1356_);
    return v___x_1358_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1359_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__16;
    v___x_1360_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__22_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__22,
    );
    v___x_1361_ = lean_array_push(v___x_1360_, v___x_1359_);
    return v___x_1361_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1362_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__23_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__23,
    );
    v___x_1363_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__11;
    v___x_1364_ = leanh::lean_box(2);
    v___x_1365_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1365_, 0, v___x_1364_);
    leanh::lean_ctor_set(v___x_1365_, 1, v___x_1363_);
    leanh::lean_ctor_set(v___x_1365_, 2, v___x_1362_);
    return v___x_1365_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1366_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__24_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__24,
    );
    v___x_1367_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__5;
    v___x_1368_ = lean_array_push(v___x_1367_, v___x_1366_);
    return v___x_1368_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1369_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__25_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__25,
    );
    v___x_1370_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__9;
    v___x_1371_ = leanh::lean_box(2);
    v___x_1372_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1372_, 0, v___x_1371_);
    leanh::lean_ctor_set(v___x_1372_, 1, v___x_1370_);
    leanh::lean_ctor_set(v___x_1372_, 2, v___x_1369_);
    return v___x_1372_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__27()
-> *mut leanh::LeanObject {
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1373_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__26_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__26,
    );
    v___x_1374_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__5;
    v___x_1375_ = lean_array_push(v___x_1374_, v___x_1373_);
    return v___x_1375_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__28()
-> *mut leanh::LeanObject {
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1376_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__27_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__27,
    );
    v___x_1377_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__7;
    v___x_1378_ = leanh::lean_box(2);
    v___x_1379_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1379_, 0, v___x_1378_);
    leanh::lean_ctor_set(v___x_1379_, 1, v___x_1377_);
    leanh::lean_ctor_set(v___x_1379_, 2, v___x_1376_);
    return v___x_1379_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__29()
-> *mut leanh::LeanObject {
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1380_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__28_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__28,
    );
    v___x_1381_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__5;
    v___x_1382_ = lean_array_push(v___x_1381_, v___x_1380_);
    return v___x_1382_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__30()
-> *mut leanh::LeanObject {
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1383_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__29_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__29,
    );
    v___x_1384_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__4;
    v___x_1385_ = leanh::lean_box(2);
    v___x_1386_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1386_, 0, v___x_1385_);
    leanh::lean_ctor_set(v___x_1386_, 1, v___x_1384_);
    leanh::lean_ctor_set(v___x_1386_, 2, v___x_1383_);
    return v___x_1386_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1() -> *mut leanh::LeanObject {
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1387_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__30),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__30_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__30,
    );
    return v___x_1387_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg(
    mut v_s_1388_: *mut leanh::LeanObject,
    mut v_endByte_1389_: *mut leanh::LeanObject,
    mut v_x_1390_: *mut leanh::LeanObject,
    mut v_x_1391_: *mut leanh::LeanObject,
    mut v_x_1392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1395_: u8 = 0;
    let mut v_a_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1398_: u8 = 0;
    let mut v___y_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1400_: u8 = 0;
    let mut v___x_1401_: u8 = 0;
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: u8 = 0;
    let mut v___x_1406_: u8 = 0;
    let mut v_a_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1411_: u8 = 0;
    let mut v___y_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1413_: u8 = 0;
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: u8 = 0;
    let mut v___x_1423_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1390_) {
                0 => {
                    leanh::lean_dec(v_x_1391_);
                    v_a_1393_ = leanh::lean_ctor_get(v_x_1390_, 0);
                    if leanh::lean_obj_tag(v_a_1393_) == 0 {
                        leanh::lean_inc(v_x_1392_);
                        return v_x_1392_;
                    } else {
                        leanh::lean_inc_ref(v_a_1393_);
                        return v_a_1393_;
                    }
                }
                1 => {
                    v_a_1394_ = leanh::lean_ctor_get(v_x_1390_, 0);
                    v_a_1395_ = leanh::lean_ctor_get_uint8(
                        v_x_1390_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v_a_1396_ = leanh::lean_ctor_get(v_x_1390_, 1);
                    if leanh::lean_obj_tag(v_a_1394_) == 0 {
                        v___x_1405_ = lean_nat_dec_lt(v_x_1391_, v_endByte_1389_);
                        v___y_1398_ = v___x_1405_;
                        v___y_1399_ = v_x_1392_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1406_ = lean_nat_dec_lt(v_x_1391_, v_endByte_1389_);
                        v___y_1398_ = v___x_1406_;
                        v___y_1399_ = v_a_1394_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    v_a_1407_ = leanh::lean_ctor_get(v_x_1390_, 0);
                    v_a_1408_ = leanh::lean_ctor_get(v_x_1390_, 1);
                    v_a_1409_ = leanh::lean_ctor_get(v_x_1390_, 2);
                    if leanh::lean_obj_tag(v_a_1407_) == 0 {
                        v___x_1422_ = lean_nat_dec_lt(v_x_1391_, v_endByte_1389_);
                        v___y_1411_ = v___x_1422_;
                        v___y_1412_ = v_x_1392_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1423_ = lean_nat_dec_lt(v_x_1391_, v_endByte_1389_);
                        v___y_1411_ = v___x_1423_;
                        v___y_1412_ = v_a_1407_;
                        state = 2;
                        continue;
                    }
                }
            },
            1 => {
                if v___y_1398_ == 0 {
                    leanh::lean_dec(v_x_1391_);
                    leanh::lean_inc(v___y_1399_);
                    return v___y_1399_;
                } else {
                    leanh::lean_inc(v_x_1391_);
                    v_c_1400_ = lean_string_get_byte_fast(v_s_1388_, v_x_1391_);
                    v___x_1401_ = lean_uint8_dec_eq(v_c_1400_, v_a_1395_);
                    if v___x_1401_ == 0 {
                        leanh::lean_dec(v_x_1391_);
                        leanh::lean_inc(v___y_1399_);
                        return v___y_1399_;
                    } else {
                        v___x_1402_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1403_ = lean_nat_add(v_x_1391_, v___x_1402_);
                        leanh::lean_dec(v_x_1391_);
                        v_x_1390_ = v_a_1396_;
                        v_x_1391_ = v___x_1403_;
                        v_x_1392_ = v___y_1399_;
                        state = 0;
                        continue;
                    }
                }
            }
            2 => {
                if v___y_1411_ == 0 {
                    leanh::lean_dec(v_x_1391_);
                    leanh::lean_inc(v___y_1412_);
                    return v___y_1412_;
                } else {
                    leanh::lean_inc(v_x_1391_);
                    v_c_1413_ = lean_string_get_byte_fast(v_s_1388_, v_x_1391_);
                    v___x_1414_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1415_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_1413_, v_a_1408_, v___x_1414_);
                    if leanh::lean_obj_tag(v___x_1415_) == 0 {
                        leanh::lean_dec(v_x_1391_);
                        leanh::lean_inc(v___y_1412_);
                        return v___y_1412_;
                    } else {
                        v_val_1416_ = leanh::lean_ctor_get(v___x_1415_, 0);
                        leanh::lean_inc(v_val_1416_);
                        leanh::lean_dec_ref_known(v___x_1415_, 1);
                        v___x_1417_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Data_Trie_instEmptyCollection___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Data_Trie_instEmptyCollection___closed__0_once
                            ),
                            _init_l_Lean_Data_Trie_instEmptyCollection___closed__0,
                        );
                        v___x_1418_ = lean_array_get_borrowed(v___x_1417_, v_a_1409_, v_val_1416_);
                        leanh::lean_dec(v_val_1416_);
                        v___x_1419_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1420_ = lean_nat_add(v_x_1391_, v___x_1419_);
                        leanh::lean_dec(v_x_1391_);
                        v_x_1390_ = v___x_1418_;
                        v_x_1391_ = v___x_1420_;
                        v_x_1392_ = v___y_1412_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg___boxed(
    mut v_s_1424_: *mut leanh::LeanObject,
    mut v_endByte_1425_: *mut leanh::LeanObject,
    mut v_x_1426_: *mut leanh::LeanObject,
    mut v_x_1427_: *mut leanh::LeanObject,
    mut v_x_1428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1429_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg(
        v_s_1424_,
        v_endByte_1425_,
        v_x_1426_,
        v_x_1427_,
        v_x_1428_,
    );
    leanh::lean_dec(v_x_1428_);
    leanh::lean_dec_ref(v_x_1426_);
    leanh::lean_dec(v_endByte_1425_);
    leanh::lean_dec_ref(v_s_1424_);
    return v_res_1429_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop(
    mut v_00_u03b1_1430_: *mut leanh::LeanObject,
    mut v_s_1431_: *mut leanh::LeanObject,
    mut v_endByte_1432_: *mut leanh::LeanObject,
    mut v_endByte__valid_1433_: *mut leanh::LeanObject,
    mut v_x_1434_: *mut leanh::LeanObject,
    mut v_x_1435_: *mut leanh::LeanObject,
    mut v_x_1436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1437_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg(
        v_s_1431_,
        v_endByte_1432_,
        v_x_1434_,
        v_x_1435_,
        v_x_1436_,
    );
    return v___x_1437_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___boxed(
    mut v_00_u03b1_1438_: *mut leanh::LeanObject,
    mut v_s_1439_: *mut leanh::LeanObject,
    mut v_endByte_1440_: *mut leanh::LeanObject,
    mut v_endByte__valid_1441_: *mut leanh::LeanObject,
    mut v_x_1442_: *mut leanh::LeanObject,
    mut v_x_1443_: *mut leanh::LeanObject,
    mut v_x_1444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1445_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop(
        v_00_u03b1_1438_,
        v_s_1439_,
        v_endByte_1440_,
        v_endByte__valid_1441_,
        v_x_1442_,
        v_x_1443_,
        v_x_1444_,
    );
    leanh::lean_dec(v_x_1444_);
    leanh::lean_dec_ref(v_x_1442_);
    leanh::lean_dec(v_endByte_1440_);
    leanh::lean_dec_ref(v_s_1439_);
    return v_res_1445_;
}
pub unsafe fn l_Lean_Data_Trie_matchPrefix___redArg(
    mut v_s_1446_: *mut leanh::LeanObject,
    mut v_t_1447_: *mut leanh::LeanObject,
    mut v_i_1448_: *mut leanh::LeanObject,
    mut v_endByte_1449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1450_ = leanh::lean_box(0);
    v___x_1451_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg(
        v_s_1446_,
        v_endByte_1449_,
        v_t_1447_,
        v_i_1448_,
        v___x_1450_,
    );
    return v___x_1451_;
}
pub unsafe fn l_Lean_Data_Trie_matchPrefix___redArg___boxed(
    mut v_s_1452_: *mut leanh::LeanObject,
    mut v_t_1453_: *mut leanh::LeanObject,
    mut v_i_1454_: *mut leanh::LeanObject,
    mut v_endByte_1455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1456_ =
        l_Lean_Data_Trie_matchPrefix___redArg(v_s_1452_, v_t_1453_, v_i_1454_, v_endByte_1455_);
    leanh::lean_dec(v_endByte_1455_);
    leanh::lean_dec_ref(v_t_1453_);
    leanh::lean_dec_ref(v_s_1452_);
    return v_res_1456_;
}
pub unsafe fn l_Lean_Data_Trie_matchPrefix(
    mut v_00_u03b1_1457_: *mut leanh::LeanObject,
    mut v_s_1458_: *mut leanh::LeanObject,
    mut v_t_1459_: *mut leanh::LeanObject,
    mut v_i_1460_: *mut leanh::LeanObject,
    mut v_endByte_1461_: *mut leanh::LeanObject,
    mut v_endByte__valid_1462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1463_ =
        l_Lean_Data_Trie_matchPrefix___redArg(v_s_1458_, v_t_1459_, v_i_1460_, v_endByte_1461_);
    return v___x_1463_;
}
pub unsafe fn l_Lean_Data_Trie_matchPrefix___boxed(
    mut v_00_u03b1_1464_: *mut leanh::LeanObject,
    mut v_s_1465_: *mut leanh::LeanObject,
    mut v_t_1466_: *mut leanh::LeanObject,
    mut v_i_1467_: *mut leanh::LeanObject,
    mut v_endByte_1468_: *mut leanh::LeanObject,
    mut v_endByte__valid_1469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1470_ = l_Lean_Data_Trie_matchPrefix(
        v_00_u03b1_1464_,
        v_s_1465_,
        v_t_1466_,
        v_i_1467_,
        v_endByte_1468_,
        v_endByte__valid_1469_,
    );
    leanh::lean_dec(v_endByte_1468_);
    leanh::lean_dec_ref(v_t_1466_);
    leanh::lean_dec_ref(v_s_1465_);
    return v_res_1470_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0_spec__0(
    mut v_x_1471_: *mut leanh::LeanObject,
    mut v_x_1472_: *mut leanh::LeanObject,
    mut v_x_1473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1478_: u8 = 0;
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1484_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1473_) == 0 {
                    leanh::lean_dec(v_x_1471_);
                    return v_x_1472_;
                } else {
                    v_head_1474_ = leanh::lean_ctor_get(v_x_1473_, 0);
                    v_tail_1475_ = leanh::lean_ctor_get(v_x_1473_, 1);
                    v_isSharedCheck_1484_ = (!leanh::lean_is_exclusive(v_x_1473_)) as u8;
                    if v_isSharedCheck_1484_ == 0 {
                        v___x_1477_ = v_x_1473_;
                        v_isShared_1478_ = v_isSharedCheck_1484_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1475_);
                        leanh::lean_inc(v_head_1474_);
                        leanh::lean_dec(v_x_1473_);
                        v___x_1477_ = leanh::lean_box(0);
                        v_isShared_1478_ = v_isSharedCheck_1484_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1471_);
                if v_isShared_1478_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1477_, 5);
                    leanh::lean_ctor_set(v___x_1477_, 1, v_x_1471_);
                    leanh::lean_ctor_set(v___x_1477_, 0, v_x_1472_);
                    v___x_1480_ = v___x_1477_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1483_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_x_1472_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_x_1471_);
                    v___x_1480_ = v_reuseFailAlloc_1483_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1481_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1481_, 0, v___x_1480_);
                leanh::lean_ctor_set(v___x_1481_, 1, v_head_1474_);
                v_x_1472_ = v___x_1481_;
                v_x_1473_ = v_tail_1475_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0(
    mut v_x_1485_: *mut leanh::LeanObject,
    mut v_x_1486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1485_) == 0 {
        let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1486_);
        v___x_1487_ = leanh::lean_box(0);
        return v___x_1487_;
    } else {
        let mut v_tail_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_1488_ = leanh::lean_ctor_get(v_x_1485_, 1);
        if leanh::lean_obj_tag(v_tail_1488_) == 0 {
            let mut v_head_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_1486_);
            v_head_1489_ = leanh::lean_ctor_get(v_x_1485_, 0);
            leanh::lean_inc(v_head_1489_);
            leanh::lean_dec_ref_known(v_x_1485_, 2);
            return v_head_1489_;
        } else {
            let mut v_head_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_1488_);
            v_head_1490_ = leanh::lean_ctor_get(v_x_1485_, 0);
            leanh::lean_inc(v_head_1490_);
            leanh::lean_dec_ref_known(v_x_1485_, 2);
            v___x_1491_ = l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0_spec__0(v_x_1486_, v_head_1490_, v_tail_1488_);
            return v___x_1491_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__1(
    mut v_a_1492_: *mut leanh::LeanObject,
    mut v_a_1493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1492_) == 0 {
                    v___x_1494_ = lean_array_to_list(v_a_1493_);
                    return v___x_1494_;
                } else {
                    v_head_1495_ = leanh::lean_ctor_get(v_a_1492_, 0);
                    leanh::lean_inc(v_head_1495_);
                    v_tail_1496_ = leanh::lean_ctor_get(v_a_1492_, 1);
                    leanh::lean_inc(v_tail_1496_);
                    leanh::lean_dec_ref_known(v_a_1492_, 2);
                    v___x_1497_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_1493_,
                        v_head_1495_,
                    );
                    v_a_1492_ = v_tail_1496_;
                    v_a_1493_ = v___x_1497_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1499_ = leanh::lean_unsigned_to_nat(4);
    v___x_1500_ = lean_nat_to_int(v___x_1499_);
    return v___x_1500_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___boxed(
    mut v_c_1501_: *mut leanh::LeanObject,
    mut v_t_1502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1503_: u8 = 0;
    let mut v_res_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1503_ = (leanh::lean_unbox(v_c_1501_) as u8);
    v_res_1504_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0(
        v_c_boxed_1503_,
        v_t_1502_,
    );
    return v_res_1504_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(
    mut v_x_1507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1507_) {
        0 => {
            let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v_x_1507_, 1);
            v___x_1508_ = leanh::lean_box(0);
            return v___x_1508_;
        }
        1 => {
            let mut v_a_1509_: u8 = 0;
            let mut v_a_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1519_: u8 = 0;
            let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_1509_ = leanh::lean_ctor_get_uint8(
                v_x_1507_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
            );
            v_a_1510_ = leanh::lean_ctor_get(v_x_1507_, 1);
            leanh::lean_inc_ref(v_a_1510_);
            leanh::lean_dec_ref_known(v_x_1507_, 2);
            v___x_1511_ = lean_uint8_to_nat(v_a_1509_);
            v___x_1512_ = l_Nat_reprFast(v___x_1511_);
            v___x_1513_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1513_, 0, v___x_1512_);
            v___x_1514_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0_once), _init_l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0);
            v___x_1515_ = leanh::lean_box(1);
            v___x_1516_ =
                l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_a_1510_);
            v___x_1517_ = l_Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0(v___x_1516_, v___x_1515_);
            v___x_1518_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1518_, 0, v___x_1514_);
            leanh::lean_ctor_set(v___x_1518_, 1, v___x_1517_);
            v___x_1519_ = 0;
            v___x_1520_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
            leanh::lean_ctor_set(v___x_1520_, 0, v___x_1518_);
            leanh::lean_ctor_set_uint8(
                v___x_1520_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                v___x_1519_,
            );
            v___x_1521_ = leanh::lean_box(0);
            v___x_1522_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1522_, 0, v___x_1520_);
            leanh::lean_ctor_set(v___x_1522_, 1, v___x_1521_);
            v___x_1523_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1523_, 0, v___x_1513_);
            leanh::lean_ctor_set(v___x_1523_, 1, v___x_1522_);
            return v___x_1523_;
        }
        _ => {
            let mut v_a_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_1524_ = leanh::lean_ctor_get(v_x_1507_, 1);
            leanh::lean_inc_ref(v_a_1524_);
            v_a_1525_ = leanh::lean_ctor_get(v_x_1507_, 2);
            leanh::lean_inc_ref(v_a_1525_);
            leanh::lean_dec_ref_known(v_x_1507_, 3);
            v___f_1526_ = leanh::lean_alloc_closure(
                l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___boxed
                    as *mut core::ffi::c_void,
                2,
                0,
            );
            v___x_1527_ = l_ByteArray_toList(v_a_1524_);
            leanh::lean_dec_ref(v_a_1524_);
            v___x_1528_ = lean_array_to_list(v_a_1525_);
            v___x_1529_ =
                l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___closed__0;
            v___x_1530_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___f_1526_,
                v___x_1527_,
                v___x_1528_,
                v___x_1529_,
            );
            v___x_1531_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__1(v___x_1530_, v___x_1529_);
            return v___x_1531_;
        }
    }
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0(
    mut v_c_1532_: u8,
    mut v_t_1533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: u8 = 0;
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1534_ = lean_uint8_to_nat(v_c_1532_);
    v___x_1535_ = l_Nat_reprFast(v___x_1534_);
    v___x_1536_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1536_, 0, v___x_1535_);
    v___x_1537_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0_once), _init_l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0);
    v___x_1538_ = leanh::lean_box(1);
    v___x_1539_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_1533_);
    v___x_1540_ = l_Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0(v___x_1539_, v___x_1538_);
    v___x_1541_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1541_, 0, v___x_1537_);
    leanh::lean_ctor_set(v___x_1541_, 1, v___x_1540_);
    v___x_1542_ = 0;
    v___x_1543_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1543_, 0, v___x_1541_);
    leanh::lean_ctor_set_uint8(
        v___x_1543_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1542_,
    );
    v___x_1544_ = leanh::lean_box(0);
    v___x_1545_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1545_, 0, v___x_1543_);
    leanh::lean_ctor_set(v___x_1545_, 1, v___x_1544_);
    v___x_1546_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1546_, 0, v___x_1536_);
    leanh::lean_ctor_set(v___x_1546_, 1, v___x_1545_);
    return v___x_1546_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux(
    mut v_00_u03b1_1547_: *mut leanh::LeanObject,
    mut v_x_1548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1549_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_x_1548_);
    return v___x_1549_;
}
pub unsafe fn l_Lean_Data_Trie_instToString___private__1___redArg(
    mut v_t_1551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1552_ = l_Lean_Data_Trie_instToString___private__1___redArg___closed__0;
    v___x_1553_ = leanh::lean_box(1);
    v___x_1554_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_1551_);
    v___x_1555_ = l_Std_Format_joinSep___redArg(v___f_1552_, v___x_1554_, v___x_1553_);
    v___x_1556_ = l_Std_Format_defWidth;
    v___x_1557_ = leanh::lean_unsigned_to_nat(0);
    v___x_1558_ = l_Std_Format_pretty(v___x_1555_, v___x_1556_, v___x_1557_, v___x_1557_);
    return v___x_1558_;
}
pub unsafe fn l_Lean_Data_Trie_instToString___private__1(
    mut v_00_u03b1_1559_: *mut leanh::LeanObject,
    mut v_t_1560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1561_ = l_Lean_Data_Trie_instToString___private__1___redArg___closed__0;
    v___x_1562_ = leanh::lean_box(1);
    v___x_1563_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_1560_);
    v___x_1564_ = l_Std_Format_joinSep___redArg(v___f_1561_, v___x_1563_, v___x_1562_);
    v___x_1565_ = l_Std_Format_defWidth;
    v___x_1566_ = leanh::lean_unsigned_to_nat(0);
    v___x_1567_ = l_Std_Format_pretty(v___x_1564_, v___x_1565_, v___x_1566_, v___x_1566_);
    return v___x_1567_;
}
pub unsafe fn l_Lean_Data_Trie_instToString___lam__0(
    mut v_t_1568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1569_ = l_Lean_Data_Trie_instToString___private__1___redArg___closed__0;
    v___x_1570_ = leanh::lean_box(1);
    v___x_1571_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_1568_);
    v___x_1572_ = l_Std_Format_joinSep___redArg(v___f_1569_, v___x_1571_, v___x_1570_);
    v___x_1573_ = l_Std_Format_defWidth;
    v___x_1574_ = leanh::lean_unsigned_to_nat(0);
    v___x_1575_ = l_Std_Format_pretty(v___x_1572_, v___x_1573_, v___x_1574_, v___x_1574_);
    return v___x_1575_;
}
pub unsafe fn l_Lean_Data_Trie_instToString(
    mut v_00_u03b1_1577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1578_ = l_Lean_Data_Trie_instToString___closed__0;
    return v___f_1578_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Trie(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Format(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Coe(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Trie(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Data_Trie_matchPrefix___auto__1 = _init_l_Lean_Data_Trie_matchPrefix___auto__1();
    leanh::lean_mark_persistent(l_Lean_Data_Trie_matchPrefix___auto__1);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Trie(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Format(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Coe(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Trie(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Trie(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Trie(builtin);
}
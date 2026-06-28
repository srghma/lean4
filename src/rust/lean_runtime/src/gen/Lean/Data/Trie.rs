// Lean compiler output
// Module: Lean.Data.Trie
// Imports: Lean.Data.Format Init.Data.Option.Coe Init.Omega
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
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom};
use crate::r#gen::Lean::Data::Format::{
    initialize_Lean_Data_Format, runtime_initialize_Lean_Data_Format,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::ByteArray::Basic::lean_byte_array_fget;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::PosRaw::lean_string_get_byte_fast;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint8_to_nat, lean_usize_add, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_array_to_list, lean_byte_array_mk, lean_byte_array_push, lean_byte_array_size,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt,
    lean_string_utf8_byte_size, lean_uint8_dec_eq, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_3, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Data_Trie_empty___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_Data_Trie_empty___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_empty___closed__0_value) as *mut LeanObject;
static mut l_Lean_Data_Trie_instEmptyCollection___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Data_Trie_instEmptyCollection___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Data_Trie_values___redArg___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_Data_Trie_values___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_values___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__1_value: LeanStringObject<7> =
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
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__2_value: LeanStringObject<7> =
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
        m_data: [84, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__3_value: LeanStringObject<10> =
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
        m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__3_value)
        as *mut LeanObject;
static l_Lean_Data_Trie_matchPrefix___auto__1___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Data_Trie_matchPrefix___auto__1___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Data_Trie_matchPrefix___auto__1___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__3_value)
                as *mut LeanObject,
            8504843326314613972 as *mut LeanObject,
        ],
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__5_value: LeanArrayObject<0> =
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
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__6_value: LeanStringObject<19> =
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
            116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__6_value)
        as *mut LeanObject;
static l_Lean_Data_Trie_matchPrefix___auto__1___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Data_Trie_matchPrefix___auto__1___closed__7_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Data_Trie_matchPrefix___auto__1___closed__7_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__7_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__6_value)
                as *mut LeanObject,
            17228437386856258271 as *mut LeanObject,
        ],
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__8_value: LeanStringObject<5> =
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
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__8_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__10_value: LeanStringObject<5> =
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
        m_data: [115, 105, 109, 112, 0],
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__10_value)
        as *mut LeanObject;
static l_Lean_Data_Trie_matchPrefix___auto__1___closed__11_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Data_Trie_matchPrefix___auto__1___closed__11_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__11_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Data_Trie_matchPrefix___auto__1___closed__11_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__11_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__11_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__10_value)
                as *mut LeanObject,
            12783917532758215986 as *mut LeanObject,
        ],
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__14_value: LeanStringObject<10> =
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
        m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__14_value)
        as *mut LeanObject;
static l_Lean_Data_Trie_matchPrefix___auto__1___closed__15_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Data_Trie_matchPrefix___auto__1___closed__15_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__15_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Data_Trie_matchPrefix___auto__1___closed__15_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__15_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__15_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__15_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__14_value)
                as *mut LeanObject,
            3488656302031949961 as *mut LeanObject,
        ],
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Data_Trie_matchPrefix___auto__1___closed__16_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 1,
        },
        m_objs: [
            (((2 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__16_value)
        as *mut LeanObject;
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__17: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__26: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__27_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__27: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__28_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__28: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__29_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__29: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__30_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Data_Trie_matchPrefix___auto__1___closed__30: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Data_Trie_matchPrefix___auto__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Data_Trie_instToString___private__1___redArg___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_instToFormatFormat___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Data_Trie_instToString___private__1___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_instToString___private__1___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Data_Trie_instToString___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Data_Trie_instToString___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Data_Trie_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_Trie_instToString___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lean_Data_Trie_ctorIdx___redArg(mut v_x_790_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_790_) {
        0 => {
            let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
            v___x_791_ = lean_unsigned_to_nat(0);
            return v___x_791_;
        }
        1 => {
            let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
            v___x_792_ = lean_unsigned_to_nat(1);
            return v___x_792_;
        }
        _ => {
            let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
            v___x_793_ = lean_unsigned_to_nat(2);
            return v___x_793_;
        }
    }
}
pub unsafe fn l_Lean_Data_Trie_ctorIdx___redArg___boxed(
    mut v_x_794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_795_: *mut LeanObject = core::ptr::null_mut();
    v_res_795_ = l_Lean_Data_Trie_ctorIdx___redArg(v_x_794_);
    lean_dec_ref(v_x_794_);
    return v_res_795_;
}
pub unsafe fn l_Lean_Data_Trie_ctorIdx(
    mut v_00_u03b1_796_: *mut LeanObject,
    mut v_x_797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    v___x_798_ = l_Lean_Data_Trie_ctorIdx___redArg(v_x_797_);
    return v___x_798_;
}
pub unsafe fn l_Lean_Data_Trie_ctorIdx___boxed(
    mut v_00_u03b1_799_: *mut LeanObject,
    mut v_x_800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_801_: *mut LeanObject = core::ptr::null_mut();
    v_res_801_ = l_Lean_Data_Trie_ctorIdx(v_00_u03b1_799_, v_x_800_);
    lean_dec_ref(v_x_800_);
    return v_res_801_;
}
pub unsafe fn l_Lean_Data_Trie_ctorElim___redArg(
    mut v_t_802_: *mut LeanObject,
    mut v_k_803_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_802_) {
        0 => {
            let mut v_a_804_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
            v_a_804_ = lean_ctor_get(v_t_802_, 0);
            lean_inc(v_a_804_);
            lean_dec_ref_known(v_t_802_, 1);
            v___x_805_ = lean_apply_1(v_k_803_, v_a_804_);
            return v___x_805_;
        }
        1 => {
            let mut v_a_806_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_807_: u8 = 0;
            let mut v_a_808_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
            v_a_806_ = lean_ctor_get(v_t_802_, 0);
            lean_inc(v_a_806_);
            v_a_807_ = lean_ctor_get_uint8(
                v_t_802_,
                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
            );
            v_a_808_ = lean_ctor_get(v_t_802_, 1);
            lean_inc_ref(v_a_808_);
            lean_dec_ref_known(v_t_802_, 2);
            v___x_809_ = lean_box((v_a_807_) as usize);
            v___x_810_ = lean_apply_3(v_k_803_, v_a_806_, v___x_809_, v_a_808_);
            return v___x_810_;
        }
        _ => {
            let mut v_a_811_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_812_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_813_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
            v_a_811_ = lean_ctor_get(v_t_802_, 0);
            lean_inc(v_a_811_);
            v_a_812_ = lean_ctor_get(v_t_802_, 1);
            lean_inc_ref(v_a_812_);
            v_a_813_ = lean_ctor_get(v_t_802_, 2);
            lean_inc_ref(v_a_813_);
            lean_dec_ref_known(v_t_802_, 3);
            v___x_814_ = lean_apply_3(v_k_803_, v_a_811_, v_a_812_, v_a_813_);
            return v___x_814_;
        }
    }
}
pub unsafe fn l_Lean_Data_Trie_ctorElim(
    mut v_00_u03b1_815_: *mut LeanObject,
    mut v_motive__1_816_: *mut LeanObject,
    mut v_ctorIdx_817_: *mut LeanObject,
    mut v_t_818_: *mut LeanObject,
    mut v_h_819_: *mut LeanObject,
    mut v_k_820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    v___x_821_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_818_, v_k_820_);
    return v___x_821_;
}
pub unsafe fn l_Lean_Data_Trie_ctorElim___boxed(
    mut v_00_u03b1_822_: *mut LeanObject,
    mut v_motive__1_823_: *mut LeanObject,
    mut v_ctorIdx_824_: *mut LeanObject,
    mut v_t_825_: *mut LeanObject,
    mut v_h_826_: *mut LeanObject,
    mut v_k_827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_828_: *mut LeanObject = core::ptr::null_mut();
    v_res_828_ = l_Lean_Data_Trie_ctorElim(
        v_00_u03b1_822_,
        v_motive__1_823_,
        v_ctorIdx_824_,
        v_t_825_,
        v_h_826_,
        v_k_827_,
    );
    lean_dec(v_ctorIdx_824_);
    return v_res_828_;
}
pub unsafe fn l_Lean_Data_Trie_leaf_elim___redArg(
    mut v_t_829_: *mut LeanObject,
    mut v_leaf_830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    v___x_831_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_829_, v_leaf_830_);
    return v___x_831_;
}
pub unsafe fn l_Lean_Data_Trie_leaf_elim(
    mut v_00_u03b1_832_: *mut LeanObject,
    mut v_motive__1_833_: *mut LeanObject,
    mut v_t_834_: *mut LeanObject,
    mut v_h_835_: *mut LeanObject,
    mut v_leaf_836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
    v___x_837_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_834_, v_leaf_836_);
    return v___x_837_;
}
pub unsafe fn l_Lean_Data_Trie_node1_elim___redArg(
    mut v_t_838_: *mut LeanObject,
    mut v_node1_839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    v___x_840_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_838_, v_node1_839_);
    return v___x_840_;
}
pub unsafe fn l_Lean_Data_Trie_node1_elim(
    mut v_00_u03b1_841_: *mut LeanObject,
    mut v_motive__1_842_: *mut LeanObject,
    mut v_t_843_: *mut LeanObject,
    mut v_h_844_: *mut LeanObject,
    mut v_node1_845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    v___x_846_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_843_, v_node1_845_);
    return v___x_846_;
}
pub unsafe fn l_Lean_Data_Trie_node_elim___redArg(
    mut v_t_847_: *mut LeanObject,
    mut v_node_848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    v___x_849_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_847_, v_node_848_);
    return v___x_849_;
}
pub unsafe fn l_Lean_Data_Trie_node_elim(
    mut v_00_u03b1_850_: *mut LeanObject,
    mut v_motive__1_851_: *mut LeanObject,
    mut v_t_852_: *mut LeanObject,
    mut v_h_853_: *mut LeanObject,
    mut v_node_854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    v___x_855_ = l_Lean_Data_Trie_ctorElim___redArg(v_t_852_, v_node_854_);
    return v___x_855_;
}
pub unsafe fn l_Lean_Data_Trie_empty(mut v_00_u03b1_858_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    v___x_859_ = l_Lean_Data_Trie_empty___closed__0;
    return v___x_859_;
}
pub unsafe fn _init_l_Lean_Data_Trie_instEmptyCollection___closed__0() -> *mut LeanObject {
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    v___x_860_ = l_Lean_Data_Trie_empty(lean_box(0));
    return v___x_860_;
}
pub unsafe fn l_Lean_Data_Trie_instEmptyCollection(
    mut v_00_u03b1_861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    v___x_862_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_instEmptyCollection___closed__0_once),
        _init_l_Lean_Data_Trie_instEmptyCollection___closed__0,
    );
    return v___x_862_;
}
pub unsafe fn l_Lean_Data_Trie_instInhabited(
    mut v_00_u03b1_863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    v___x_864_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_instEmptyCollection___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_instEmptyCollection___closed__0_once),
        _init_l_Lean_Data_Trie_instEmptyCollection___closed__0,
    );
    return v___x_864_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(
    mut v_s_865_: *mut LeanObject,
    mut v_f_866_: *mut LeanObject,
    mut v_i_867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_869_: u8 = 0;
    v___x_868_ = lean_string_utf8_byte_size(v_s_865_);
    v___x_869_ = lean_nat_dec_lt(v_i_867_, v___x_868_);
    if v___x_869_ == 0 {
        let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_i_867_);
        v___x_870_ = lean_box(0);
        v___x_871_ = lean_apply_1(v_f_866_, v___x_870_);
        v___x_872_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_872_, 0, v___x_871_);
        v___x_873_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_873_, 0, v___x_872_);
        return v___x_873_;
    } else {
        let mut v_c_874_: u8 = 0;
        let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
        let mut v_t_877_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_i_867_);
        v_c_874_ = lean_string_get_byte_fast(v_s_865_, v_i_867_);
        v___x_875_ = lean_unsigned_to_nat(1);
        v___x_876_ = lean_nat_add(v_i_867_, v___x_875_);
        lean_dec(v_i_867_);
        v_t_877_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(
            v_s_865_, v_f_866_, v___x_876_,
        );
        v___x_878_ = lean_box(0);
        v___x_879_ = lean_alloc_ctor(1, 2, (1) as u32);
        lean_ctor_set(v___x_879_, 0, v___x_878_);
        lean_ctor_set(v___x_879_, 1, v_t_877_);
        lean_ctor_set_uint8(
            v___x_879_,
            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
            v_c_874_,
        );
        return v___x_879_;
    }
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg___boxed(
    mut v_s_880_: *mut LeanObject,
    mut v_f_881_: *mut LeanObject,
    mut v_i_882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_883_: *mut LeanObject = core::ptr::null_mut();
    v_res_883_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(
        v_s_880_, v_f_881_, v_i_882_,
    );
    lean_dec_ref(v_s_880_);
    return v_res_883_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty(
    mut v_00_u03b1_884_: *mut LeanObject,
    mut v_s_885_: *mut LeanObject,
    mut v_f_886_: *mut LeanObject,
    mut v_i_887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    v___x_888_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(
        v_s_885_, v_f_886_, v_i_887_,
    );
    return v___x_888_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___boxed(
    mut v_00_u03b1_889_: *mut LeanObject,
    mut v_s_890_: *mut LeanObject,
    mut v_f_891_: *mut LeanObject,
    mut v_i_892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_893_: *mut LeanObject = core::ptr::null_mut();
    v_res_893_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty(
        v_00_u03b1_889_,
        v_s_890_,
        v_f_891_,
        v_i_892_,
    );
    lean_dec_ref(v_s_890_);
    return v_res_893_;
}
pub unsafe fn l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(
    mut v_c_894_: u8,
    mut v_a_895_: *mut LeanObject,
    mut v_i_896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: u8 = 0;
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_900_: u8 = 0;
    let mut v___x_901_: u8 = 0;
    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_897_ = lean_byte_array_size(v_a_895_);
                v___x_898_ = lean_nat_dec_lt(v_i_896_, v___x_897_);
                if v___x_898_ == 0 {
                    lean_dec(v_i_896_);
                    v___x_899_ = lean_box(0);
                    return v___x_899_;
                } else {
                    v___x_900_ = lean_byte_array_fget(v_a_895_, v_i_896_);
                    v___x_901_ = lean_uint8_dec_eq(v___x_900_, v_c_894_);
                    if v___x_901_ == 0 {
                        v___x_902_ = lean_unsigned_to_nat(1);
                        v___x_903_ = lean_nat_add(v_i_896_, v___x_902_);
                        lean_dec(v_i_896_);
                        v_i_896_ = v___x_903_;
                        state = 0;
                        continue;
                    } else {
                        v___x_905_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_905_, 0, v_i_896_);
                        return v___x_905_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0___boxed(
    mut v_c_906_: *mut LeanObject,
    mut v_a_907_: *mut LeanObject,
    mut v_i_908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_909_: u8 = 0;
    let mut v_res_910_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_909_ = (lean_unbox(v_c_906_) as u8);
    v_res_910_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_boxed_909_, v_a_907_, v_i_908_);
    lean_dec_ref(v_a_907_);
    return v_res_910_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(
    mut v_s_911_: *mut LeanObject,
    mut v_f_912_: *mut LeanObject,
    mut v_x_913_: *mut LeanObject,
    mut v_x_914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_918_: u8 = 0;
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_920_: u8 = 0;
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_926_: u8 = 0;
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_t_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_931_: u8 = 0;
    let mut v_a_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_933_: u8 = 0;
    let mut v_a_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_937_: u8 = 0;
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_939_: u8 = 0;
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_945_: u8 = 0;
    let mut v___x_946_: u8 = 0;
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_t_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_966_: u8 = 0;
    let mut v_a_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_971_: u8 = 0;
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_974_: u8 = 0;
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_980_: u8 = 0;
    let mut v_unused_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_984_: u8 = 0;
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_989_: u8 = 0;
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_t_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_998_: u8 = 0;
    let mut v_unused_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: u8 = 0;
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1007_: u8 = 0;
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1018_: u8 = 0;
    let mut v_unused_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_914_) {
                0 => {
                    v_a_915_ = lean_ctor_get(v_x_914_, 0);
                    v_isSharedCheck_931_ = (!lean_is_exclusive(v_x_914_)) as u8;
                    if v_isSharedCheck_931_ == 0 {
                        v___x_917_ = v_x_914_;
                        v_isShared_918_ = v_isSharedCheck_931_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_915_);
                        lean_dec(v_x_914_);
                        v___x_917_ = lean_box(0);
                        v_isShared_918_ = v_isSharedCheck_931_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_932_ = lean_ctor_get(v_x_914_, 0);
                    v_a_933_ = lean_ctor_get_uint8(
                        v_x_914_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v_a_934_ = lean_ctor_get(v_x_914_, 1);
                    v_isSharedCheck_966_ = (!lean_is_exclusive(v_x_914_)) as u8;
                    if v_isSharedCheck_966_ == 0 {
                        v___x_936_ = v_x_914_;
                        v_isShared_937_ = v_isSharedCheck_966_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_934_);
                        lean_inc(v_a_932_);
                        lean_dec(v_x_914_);
                        v___x_936_ = lean_box(0);
                        v_isShared_937_ = v_isSharedCheck_966_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v_a_967_ = lean_ctor_get(v_x_914_, 0);
                    v_a_968_ = lean_ctor_get(v_x_914_, 1);
                    v_a_969_ = lean_ctor_get(v_x_914_, 2);
                    v___x_970_ = lean_string_utf8_byte_size(v_s_911_);
                    v___x_971_ = lean_nat_dec_lt(v_x_913_, v___x_970_);
                    if v___x_971_ == 0 {
                        lean_inc_ref(v_a_969_);
                        lean_inc_ref(v_a_968_);
                        lean_inc(v_a_967_);
                        lean_dec(v_x_913_);
                        v_isSharedCheck_980_ = (!lean_is_exclusive(v_x_914_)) as u8;
                        if v_isSharedCheck_980_ == 0 {
                            v_unused_981_ = lean_ctor_get(v_x_914_, 2);
                            lean_dec(v_unused_981_);
                            v_unused_982_ = lean_ctor_get(v_x_914_, 1);
                            lean_dec(v_unused_982_);
                            v_unused_983_ = lean_ctor_get(v_x_914_, 0);
                            lean_dec(v_unused_983_);
                            v___x_973_ = v_x_914_;
                            v_isShared_974_ = v_isSharedCheck_980_;
                            state = 6;
                            continue;
                        } else {
                            lean_dec(v_x_914_);
                            v___x_973_ = lean_box(0);
                            v_isShared_974_ = v_isSharedCheck_980_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_inc(v_x_913_);
                        v_c_984_ = lean_string_get_byte_fast(v_s_911_, v_x_913_);
                        v___x_985_ = lean_unsigned_to_nat(0);
                        v___x_986_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_984_, v_a_968_, v___x_985_);
                        if lean_obj_tag(v___x_986_) == 0 {
                            lean_inc_ref(v_a_969_);
                            lean_inc_ref(v_a_968_);
                            lean_inc(v_a_967_);
                            v_isSharedCheck_998_ = (!lean_is_exclusive(v_x_914_)) as u8;
                            if v_isSharedCheck_998_ == 0 {
                                v_unused_999_ = lean_ctor_get(v_x_914_, 2);
                                lean_dec(v_unused_999_);
                                v_unused_1000_ = lean_ctor_get(v_x_914_, 1);
                                lean_dec(v_unused_1000_);
                                v_unused_1001_ = lean_ctor_get(v_x_914_, 0);
                                lean_dec(v_unused_1001_);
                                v___x_988_ = v_x_914_;
                                v_isShared_989_ = v_isSharedCheck_998_;
                                state = 8;
                                continue;
                            } else {
                                lean_dec(v_x_914_);
                                v___x_988_ = lean_box(0);
                                v_isShared_989_ = v_isSharedCheck_998_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v_val_1002_ = lean_ctor_get(v___x_986_, 0);
                            lean_inc(v_val_1002_);
                            lean_dec_ref_known(v___x_986_, 1);
                            v___x_1003_ = lean_array_get_size(v_a_969_);
                            v___x_1004_ = lean_nat_dec_lt(v_val_1002_, v___x_1003_);
                            if v___x_1004_ == 0 {
                                lean_dec(v_val_1002_);
                                lean_dec(v_x_913_);
                                lean_dec(v_f_912_);
                                return v_x_914_;
                            } else {
                                lean_inc_ref(v_a_969_);
                                lean_inc_ref(v_a_968_);
                                lean_inc(v_a_967_);
                                v_isSharedCheck_1018_ = (!lean_is_exclusive(v_x_914_)) as u8;
                                if v_isSharedCheck_1018_ == 0 {
                                    v_unused_1019_ = lean_ctor_get(v_x_914_, 2);
                                    lean_dec(v_unused_1019_);
                                    v_unused_1020_ = lean_ctor_get(v_x_914_, 1);
                                    lean_dec(v_unused_1020_);
                                    v_unused_1021_ = lean_ctor_get(v_x_914_, 0);
                                    lean_dec(v_unused_1021_);
                                    v___x_1006_ = v_x_914_;
                                    v_isShared_1007_ = v_isSharedCheck_1018_;
                                    state = 10;
                                    continue;
                                } else {
                                    lean_dec(v_x_914_);
                                    v___x_1006_ = lean_box(0);
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
                    lean_dec(v_x_913_);
                    v___x_921_ = lean_apply_1(v_f_912_, v_a_915_);
                    v___x_922_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_922_, 0, v___x_921_);
                    if v_isShared_918_ == 0 {
                        lean_ctor_set(v___x_917_, 0, v___x_922_);
                        v___x_924_ = v___x_917_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
                        v___x_924_ = v_reuseFailAlloc_925_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_917_);
                    lean_inc(v_x_913_);
                    v_c_926_ = lean_string_get_byte_fast(v_s_911_, v_x_913_);
                    v___x_927_ = lean_unsigned_to_nat(1);
                    v___x_928_ = lean_nat_add(v_x_913_, v___x_927_);
                    lean_dec(v_x_913_);
                    v_t_929_ =
                        l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(
                            v_s_911_, v_f_912_, v___x_928_,
                        );
                    v___x_930_ = lean_alloc_ctor(1, 2, (1) as u32);
                    lean_ctor_set(v___x_930_, 0, v_a_915_);
                    lean_ctor_set(v___x_930_, 1, v_t_929_);
                    lean_ctor_set_uint8(
                        v___x_930_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
                    lean_dec(v_x_913_);
                    v___x_940_ = lean_apply_1(v_f_912_, v_a_932_);
                    v___x_941_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_941_, 0, v___x_940_);
                    if v_isShared_937_ == 0 {
                        lean_ctor_set(v___x_936_, 0, v___x_941_);
                        v___x_943_ = v___x_936_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 2, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_941_);
                        lean_ctor_set(v_reuseFailAlloc_944_, 1, v_a_934_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_944_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                            v_a_933_,
                        );
                        v___x_943_ = v_reuseFailAlloc_944_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc(v_x_913_);
                    v_c_945_ = lean_string_get_byte_fast(v_s_911_, v_x_913_);
                    v___x_946_ = lean_uint8_dec_eq(v_c_945_, v_a_933_);
                    if v___x_946_ == 0 {
                        lean_del_object(v___x_936_);
                        v___x_947_ = lean_unsigned_to_nat(1);
                        v___x_948_ = lean_nat_add(v_x_913_, v___x_947_);
                        lean_dec(v_x_913_);
                        v_t_949_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(v_s_911_, v_f_912_, v___x_948_);
                        v___x_950_ = lean_unsigned_to_nat(2);
                        v___x_951_ = lean_mk_empty_array_with_capacity(v___x_950_);
                        v___x_952_ = lean_box((v_c_945_) as usize);
                        lean_inc_ref(v___x_951_);
                        v___x_953_ = lean_array_push(v___x_951_, v___x_952_);
                        v___x_954_ = lean_box((v_a_933_) as usize);
                        v___x_955_ = lean_array_push(v___x_953_, v___x_954_);
                        v___x_956_ = lean_byte_array_mk(v___x_955_);
                        v___x_957_ = lean_array_push(v___x_951_, v_t_949_);
                        v___x_958_ = lean_array_push(v___x_957_, v_a_934_);
                        v___x_959_ = lean_alloc_ctor(2, 3, (0) as u32);
                        lean_ctor_set(v___x_959_, 0, v_a_932_);
                        lean_ctor_set(v___x_959_, 1, v___x_956_);
                        lean_ctor_set(v___x_959_, 2, v___x_958_);
                        return v___x_959_;
                    } else {
                        v___x_960_ = lean_unsigned_to_nat(1);
                        v___x_961_ = lean_nat_add(v_x_913_, v___x_960_);
                        lean_dec(v_x_913_);
                        v___x_962_ =
                            l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(
                                v_s_911_, v_f_912_, v___x_961_, v_a_934_,
                            );
                        if v_isShared_937_ == 0 {
                            lean_ctor_set(v___x_936_, 1, v___x_962_);
                            v___x_964_ = v___x_936_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 2, (1) as u32);
                            lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_932_);
                            lean_ctor_set(v_reuseFailAlloc_965_, 1, v___x_962_);
                            lean_ctor_set_uint8(
                                v_reuseFailAlloc_965_,
                                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
                v___x_975_ = lean_apply_1(v_f_912_, v_a_967_);
                v___x_976_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_976_, 0, v___x_975_);
                if v_isShared_974_ == 0 {
                    lean_ctor_set(v___x_973_, 0, v___x_976_);
                    v___x_978_ = v___x_973_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_979_ = lean_alloc_ctor(2, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_976_);
                    lean_ctor_set(v_reuseFailAlloc_979_, 1, v_a_968_);
                    lean_ctor_set(v_reuseFailAlloc_979_, 2, v_a_969_);
                    v___x_978_ = v_reuseFailAlloc_979_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_978_;
            }
            8 => {
                v___x_990_ = lean_unsigned_to_nat(1);
                v___x_991_ = lean_nat_add(v_x_913_, v___x_990_);
                lean_dec(v_x_913_);
                v_t_992_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_insertEmpty___redArg(
                    v_s_911_, v_f_912_, v___x_991_,
                );
                v___x_993_ = lean_byte_array_push(v_a_968_, v_c_984_);
                v___x_994_ = lean_array_push(v_a_969_, v_t_992_);
                if v_isShared_989_ == 0 {
                    lean_ctor_set(v___x_988_, 2, v___x_994_);
                    lean_ctor_set(v___x_988_, 1, v___x_993_);
                    v___x_996_ = v___x_988_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_997_ = lean_alloc_ctor(2, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_967_);
                    lean_ctor_set(v_reuseFailAlloc_997_, 1, v___x_993_);
                    lean_ctor_set(v_reuseFailAlloc_997_, 2, v___x_994_);
                    v___x_996_ = v_reuseFailAlloc_997_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_996_;
            }
            10 => {
                v___x_1008_ = lean_unsigned_to_nat(1);
                v___x_1009_ = lean_nat_add(v_x_913_, v___x_1008_);
                lean_dec(v_x_913_);
                v_v_1010_ = lean_array_fget(v_a_969_, v_val_1002_);
                v___x_1011_ = lean_box(0);
                v_xs_x27_1012_ = lean_array_fset(v_a_969_, v_val_1002_, v___x_1011_);
                v___x_1013_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(
                    v_s_911_,
                    v_f_912_,
                    v___x_1009_,
                    v_v_1010_,
                );
                v___x_1014_ = lean_array_fset(v_xs_x27_1012_, v_val_1002_, v___x_1013_);
                lean_dec(v_val_1002_);
                if v_isShared_1007_ == 0 {
                    lean_ctor_set(v___x_1006_, 2, v___x_1014_);
                    v___x_1016_ = v___x_1006_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1017_ = lean_alloc_ctor(2, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_967_);
                    lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_a_968_);
                    lean_ctor_set(v_reuseFailAlloc_1017_, 2, v___x_1014_);
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
    mut v_s_1022_: *mut LeanObject,
    mut v_f_1023_: *mut LeanObject,
    mut v_x_1024_: *mut LeanObject,
    mut v_x_1025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1026_: *mut LeanObject = core::ptr::null_mut();
    v_res_1026_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(
        v_s_1022_, v_f_1023_, v_x_1024_, v_x_1025_,
    );
    lean_dec_ref(v_s_1022_);
    return v_res_1026_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop(
    mut v_00_u03b1_1027_: *mut LeanObject,
    mut v_s_1028_: *mut LeanObject,
    mut v_f_1029_: *mut LeanObject,
    mut v_x_1030_: *mut LeanObject,
    mut v_x_1031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    v___x_1032_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(
        v_s_1028_, v_f_1029_, v_x_1030_, v_x_1031_,
    );
    return v___x_1032_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___boxed(
    mut v_00_u03b1_1033_: *mut LeanObject,
    mut v_s_1034_: *mut LeanObject,
    mut v_f_1035_: *mut LeanObject,
    mut v_x_1036_: *mut LeanObject,
    mut v_x_1037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1038_: *mut LeanObject = core::ptr::null_mut();
    v_res_1038_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop(
        v_00_u03b1_1033_,
        v_s_1034_,
        v_f_1035_,
        v_x_1036_,
        v_x_1037_,
    );
    lean_dec_ref(v_s_1034_);
    return v_res_1038_;
}
pub unsafe fn l_Lean_Data_Trie_upsert___redArg(
    mut v_t_1039_: *mut LeanObject,
    mut v_s_1040_: *mut LeanObject,
    mut v_f_1041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    v___x_1042_ = lean_unsigned_to_nat(0);
    v___x_1043_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop___redArg(
        v_s_1040_,
        v_f_1041_,
        v___x_1042_,
        v_t_1039_,
    );
    return v___x_1043_;
}
pub unsafe fn l_Lean_Data_Trie_upsert___redArg___boxed(
    mut v_t_1044_: *mut LeanObject,
    mut v_s_1045_: *mut LeanObject,
    mut v_f_1046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1047_: *mut LeanObject = core::ptr::null_mut();
    v_res_1047_ = l_Lean_Data_Trie_upsert___redArg(v_t_1044_, v_s_1045_, v_f_1046_);
    lean_dec_ref(v_s_1045_);
    return v_res_1047_;
}
pub unsafe fn l_Lean_Data_Trie_upsert(
    mut v_00_u03b1_1048_: *mut LeanObject,
    mut v_t_1049_: *mut LeanObject,
    mut v_s_1050_: *mut LeanObject,
    mut v_f_1051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    v___x_1052_ = l_Lean_Data_Trie_upsert___redArg(v_t_1049_, v_s_1050_, v_f_1051_);
    return v___x_1052_;
}
pub unsafe fn l_Lean_Data_Trie_upsert___boxed(
    mut v_00_u03b1_1053_: *mut LeanObject,
    mut v_t_1054_: *mut LeanObject,
    mut v_s_1055_: *mut LeanObject,
    mut v_f_1056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1057_: *mut LeanObject = core::ptr::null_mut();
    v_res_1057_ = l_Lean_Data_Trie_upsert(v_00_u03b1_1053_, v_t_1054_, v_s_1055_, v_f_1056_);
    lean_dec_ref(v_s_1055_);
    return v_res_1057_;
}
pub unsafe fn l_Lean_Data_Trie_insert___redArg___lam__0(
    mut v_val_1058_: *mut LeanObject,
    mut v_x_1059_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_val_1058_);
    return v_val_1058_;
}
pub unsafe fn l_Lean_Data_Trie_insert___redArg___lam__0___boxed(
    mut v_val_1060_: *mut LeanObject,
    mut v_x_1061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1062_: *mut LeanObject = core::ptr::null_mut();
    v_res_1062_ = l_Lean_Data_Trie_insert___redArg___lam__0(v_val_1060_, v_x_1061_);
    lean_dec(v_x_1061_);
    lean_dec(v_val_1060_);
    return v_res_1062_;
}
pub unsafe fn l_Lean_Data_Trie_insert___redArg(
    mut v_t_1063_: *mut LeanObject,
    mut v_s_1064_: *mut LeanObject,
    mut v_val_1065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    v___f_1066_ = lean_alloc_closure(
        l_Lean_Data_Trie_insert___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1066_, 0, v_val_1065_);
    v___x_1067_ = l_Lean_Data_Trie_upsert___redArg(v_t_1063_, v_s_1064_, v___f_1066_);
    return v___x_1067_;
}
pub unsafe fn l_Lean_Data_Trie_insert___redArg___boxed(
    mut v_t_1068_: *mut LeanObject,
    mut v_s_1069_: *mut LeanObject,
    mut v_val_1070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1071_: *mut LeanObject = core::ptr::null_mut();
    v_res_1071_ = l_Lean_Data_Trie_insert___redArg(v_t_1068_, v_s_1069_, v_val_1070_);
    lean_dec_ref(v_s_1069_);
    return v_res_1071_;
}
pub unsafe fn l_Lean_Data_Trie_insert(
    mut v_00_u03b1_1072_: *mut LeanObject,
    mut v_t_1073_: *mut LeanObject,
    mut v_s_1074_: *mut LeanObject,
    mut v_val_1075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    v___x_1076_ = l_Lean_Data_Trie_insert___redArg(v_t_1073_, v_s_1074_, v_val_1075_);
    return v___x_1076_;
}
pub unsafe fn l_Lean_Data_Trie_insert___boxed(
    mut v_00_u03b1_1077_: *mut LeanObject,
    mut v_t_1078_: *mut LeanObject,
    mut v_s_1079_: *mut LeanObject,
    mut v_val_1080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1081_: *mut LeanObject = core::ptr::null_mut();
    v_res_1081_ = l_Lean_Data_Trie_insert(v_00_u03b1_1077_, v_t_1078_, v_s_1079_, v_val_1080_);
    lean_dec_ref(v_s_1079_);
    return v_res_1081_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg(
    mut v_s_1082_: *mut LeanObject,
    mut v_x_1083_: *mut LeanObject,
    mut v_x_1084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: u8 = 0;
    let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1090_: u8 = 0;
    let mut v_a_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: u8 = 0;
    let mut v_c_1094_: u8 = 0;
    let mut v___x_1095_: u8 = 0;
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: u8 = 0;
    let mut v_c_1105_: u8 = 0;
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_1084_) {
                0 => {
                    v_a_1085_ = lean_ctor_get(v_x_1084_, 0);
                    v___x_1086_ = lean_string_utf8_byte_size(v_s_1082_);
                    v___x_1087_ = lean_nat_dec_lt(v_x_1083_, v___x_1086_);
                    lean_dec(v_x_1083_);
                    if v___x_1087_ == 0 {
                        lean_inc(v_a_1085_);
                        return v_a_1085_;
                    } else {
                        v___x_1088_ = lean_box(0);
                        return v___x_1088_;
                    }
                }
                1 => {
                    v_a_1089_ = lean_ctor_get(v_x_1084_, 0);
                    v_a_1090_ = lean_ctor_get_uint8(
                        v_x_1084_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v_a_1091_ = lean_ctor_get(v_x_1084_, 1);
                    v___x_1092_ = lean_string_utf8_byte_size(v_s_1082_);
                    v___x_1093_ = lean_nat_dec_lt(v_x_1083_, v___x_1092_);
                    if v___x_1093_ == 0 {
                        lean_dec(v_x_1083_);
                        lean_inc(v_a_1089_);
                        return v_a_1089_;
                    } else {
                        lean_inc(v_x_1083_);
                        v_c_1094_ = lean_string_get_byte_fast(v_s_1082_, v_x_1083_);
                        v___x_1095_ = lean_uint8_dec_eq(v_c_1094_, v_a_1090_);
                        if v___x_1095_ == 0 {
                            lean_dec(v_x_1083_);
                            v___x_1096_ = lean_box(0);
                            return v___x_1096_;
                        } else {
                            v___x_1097_ = lean_unsigned_to_nat(1);
                            v___x_1098_ = lean_nat_add(v_x_1083_, v___x_1097_);
                            lean_dec(v_x_1083_);
                            v_x_1083_ = v___x_1098_;
                            v_x_1084_ = v_a_1091_;
                            state = 0;
                            continue;
                        }
                    }
                }
                _ => {
                    v_a_1100_ = lean_ctor_get(v_x_1084_, 0);
                    v_a_1101_ = lean_ctor_get(v_x_1084_, 1);
                    v_a_1102_ = lean_ctor_get(v_x_1084_, 2);
                    v___x_1103_ = lean_string_utf8_byte_size(v_s_1082_);
                    v___x_1104_ = lean_nat_dec_lt(v_x_1083_, v___x_1103_);
                    if v___x_1104_ == 0 {
                        lean_dec(v_x_1083_);
                        lean_inc(v_a_1100_);
                        return v_a_1100_;
                    } else {
                        lean_inc(v_x_1083_);
                        v_c_1105_ = lean_string_get_byte_fast(v_s_1082_, v_x_1083_);
                        v___x_1106_ = lean_unsigned_to_nat(0);
                        v___x_1107_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_1105_, v_a_1101_, v___x_1106_);
                        if lean_obj_tag(v___x_1107_) == 0 {
                            lean_dec(v_x_1083_);
                            v___x_1108_ = lean_box(0);
                            return v___x_1108_;
                        } else {
                            v_val_1109_ = lean_ctor_get(v___x_1107_, 0);
                            lean_inc(v_val_1109_);
                            lean_dec_ref_known(v___x_1107_, 1);
                            v___x_1110_ = lean_unsigned_to_nat(1);
                            v___x_1111_ = lean_nat_add(v_x_1083_, v___x_1110_);
                            lean_dec(v_x_1083_);
                            v___x_1112_ = lean_obj_once(
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
                            lean_dec(v_val_1109_);
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
    mut v_s_1115_: *mut LeanObject,
    mut v_x_1116_: *mut LeanObject,
    mut v_x_1117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1118_: *mut LeanObject = core::ptr::null_mut();
    v_res_1118_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg(
        v_s_1115_, v_x_1116_, v_x_1117_,
    );
    lean_dec_ref(v_x_1117_);
    lean_dec_ref(v_s_1115_);
    return v_res_1118_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop(
    mut v_00_u03b1_1119_: *mut LeanObject,
    mut v_s_1120_: *mut LeanObject,
    mut v_x_1121_: *mut LeanObject,
    mut v_x_1122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    v___x_1123_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg(
        v_s_1120_, v_x_1121_, v_x_1122_,
    );
    return v___x_1123_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___boxed(
    mut v_00_u03b1_1124_: *mut LeanObject,
    mut v_s_1125_: *mut LeanObject,
    mut v_x_1126_: *mut LeanObject,
    mut v_x_1127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1128_: *mut LeanObject = core::ptr::null_mut();
    v_res_1128_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop(
        v_00_u03b1_1124_,
        v_s_1125_,
        v_x_1126_,
        v_x_1127_,
    );
    lean_dec_ref(v_x_1127_);
    lean_dec_ref(v_s_1125_);
    return v_res_1128_;
}
pub unsafe fn l_Lean_Data_Trie_find_x3f___redArg(
    mut v_t_1129_: *mut LeanObject,
    mut v_s_1130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    v___x_1131_ = lean_unsigned_to_nat(0);
    v___x_1132_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_find_x3f_loop___redArg(
        v_s_1130_,
        v___x_1131_,
        v_t_1129_,
    );
    return v___x_1132_;
}
pub unsafe fn l_Lean_Data_Trie_find_x3f___redArg___boxed(
    mut v_t_1133_: *mut LeanObject,
    mut v_s_1134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1135_: *mut LeanObject = core::ptr::null_mut();
    v_res_1135_ = l_Lean_Data_Trie_find_x3f___redArg(v_t_1133_, v_s_1134_);
    lean_dec_ref(v_s_1134_);
    lean_dec_ref(v_t_1133_);
    return v_res_1135_;
}
pub unsafe fn l_Lean_Data_Trie_find_x3f(
    mut v_00_u03b1_1136_: *mut LeanObject,
    mut v_t_1137_: *mut LeanObject,
    mut v_s_1138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    v___x_1139_ = l_Lean_Data_Trie_find_x3f___redArg(v_t_1137_, v_s_1138_);
    return v___x_1139_;
}
pub unsafe fn l_Lean_Data_Trie_find_x3f___boxed(
    mut v_00_u03b1_1140_: *mut LeanObject,
    mut v_t_1141_: *mut LeanObject,
    mut v_s_1142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1143_: *mut LeanObject = core::ptr::null_mut();
    v_res_1143_ = l_Lean_Data_Trie_find_x3f(v_00_u03b1_1140_, v_t_1141_, v_s_1142_);
    lean_dec_ref(v_s_1142_);
    lean_dec_ref(v_t_1141_);
    return v_res_1143_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(
    mut v_a_1144_: *mut LeanObject,
    mut v_a_1145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: u8 = 0;
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: u8 = 0;
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: usize = 0;
    let mut v___x_1172_: usize = 0;
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: usize = 0;
    let mut v___x_1175_: usize = 0;
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_a_1144_) {
                0 => {
                    v_a_1146_ = lean_ctor_get(v_a_1144_, 0);
                    if lean_obj_tag(v_a_1146_) == 1 {
                        v_val_1147_ = lean_ctor_get(v_a_1146_, 0);
                        v___x_1148_ = lean_box(0);
                        lean_inc(v_val_1147_);
                        v___x_1149_ = lean_array_push(v_a_1145_, v_val_1147_);
                        v___x_1150_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1150_, 0, v___x_1148_);
                        lean_ctor_set(v___x_1150_, 1, v___x_1149_);
                        return v___x_1150_;
                    } else {
                        v___x_1151_ = lean_box(0);
                        v___x_1152_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1152_, 0, v___x_1151_);
                        lean_ctor_set(v___x_1152_, 1, v_a_1145_);
                        return v___x_1152_;
                    }
                }
                1 => {
                    v_a_1153_ = lean_ctor_get(v_a_1144_, 0);
                    if lean_obj_tag(v_a_1153_) == 1 {
                        v_a_1154_ = lean_ctor_get(v_a_1144_, 1);
                        v_val_1155_ = lean_ctor_get(v_a_1153_, 0);
                        lean_inc(v_val_1155_);
                        v___x_1156_ = lean_array_push(v_a_1145_, v_val_1155_);
                        v_a_1144_ = v_a_1154_;
                        v_a_1145_ = v___x_1156_;
                        state = 0;
                        continue;
                    } else {
                        v_a_1158_ = lean_ctor_get(v_a_1144_, 1);
                        v_a_1144_ = v_a_1158_;
                        state = 0;
                        continue;
                    }
                }
                _ => {
                    v_a_1160_ = lean_ctor_get(v_a_1144_, 0);
                    v_a_1161_ = lean_ctor_get(v_a_1144_, 2);
                    if lean_obj_tag(v_a_1160_) == 1 {
                        v_val_1177_ = lean_ctor_get(v_a_1160_, 0);
                        lean_inc(v_val_1177_);
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
                v___x_1164_ = lean_unsigned_to_nat(0);
                v___x_1165_ = lean_array_get_size(v_a_1161_);
                v___x_1166_ = lean_box(0);
                v___x_1167_ = lean_nat_dec_lt(v___x_1164_, v___x_1165_);
                if v___x_1167_ == 0 {
                    v___x_1168_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1168_, 0, v___x_1166_);
                    lean_ctor_set(v___x_1168_, 1, v___y_1163_);
                    return v___x_1168_;
                } else {
                    v___x_1169_ = lean_nat_dec_le(v___x_1165_, v___x_1165_);
                    if v___x_1169_ == 0 {
                        if v___x_1167_ == 0 {
                            v___x_1170_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_1170_, 0, v___x_1166_);
                            lean_ctor_set(v___x_1170_, 1, v___y_1163_);
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
    mut v_as_1179_: *mut LeanObject,
    mut v_i_1180_: usize,
    mut v_stop_1181_: usize,
    mut v_b_1182_: *mut LeanObject,
    mut v___y_1183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1184_: u8 = 0;
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: usize = 0;
    let mut v___x_1190_: usize = 0;
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
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
                    v_fst_1187_ = lean_ctor_get(v___x_1186_, 0);
                    lean_inc(v_fst_1187_);
                    v_snd_1188_ = lean_ctor_get(v___x_1186_, 1);
                    lean_inc(v_snd_1188_);
                    lean_dec_ref(v___x_1186_);
                    v___x_1189_ = 1usize;
                    v___x_1190_ = lean_usize_add(v_i_1180_, v___x_1189_);
                    v_i_1180_ = v___x_1190_;
                    v_b_1182_ = v_fst_1187_;
                    v___y_1183_ = v_snd_1188_;
                    state = 0;
                    continue;
                } else {
                    v___x_1192_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1192_, 0, v_b_1182_);
                    lean_ctor_set(v___x_1192_, 1, v___y_1183_);
                    return v___x_1192_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg___boxed(
    mut v_as_1193_: *mut LeanObject,
    mut v_i_1194_: *mut LeanObject,
    mut v_stop_1195_: *mut LeanObject,
    mut v_b_1196_: *mut LeanObject,
    mut v___y_1197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1198_: usize = 0;
    let mut v_stop_boxed_1199_: usize = 0;
    let mut v_res_1200_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1198_ = lean_unbox_usize(v_i_1194_);
    lean_dec(v_i_1194_);
    v_stop_boxed_1199_ = lean_unbox_usize(v_stop_1195_);
    lean_dec(v_stop_1195_);
    v_res_1200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(v_as_1193_, v_i_boxed_1198_, v_stop_boxed_1199_, v_b_1196_, v___y_1197_);
    lean_dec_ref(v_as_1193_);
    return v_res_1200_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg___boxed(
    mut v_a_1201_: *mut LeanObject,
    mut v_a_1202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1203_: *mut LeanObject = core::ptr::null_mut();
    v_res_1203_ =
        l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(v_a_1201_, v_a_1202_);
    lean_dec_ref(v_a_1201_);
    return v_res_1203_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go(
    mut v_00_u03b1_1204_: *mut LeanObject,
    mut v_a_1205_: *mut LeanObject,
    mut v_a_1206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    v___x_1207_ =
        l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(v_a_1205_, v_a_1206_);
    return v___x_1207_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___boxed(
    mut v_00_u03b1_1208_: *mut LeanObject,
    mut v_a_1209_: *mut LeanObject,
    mut v_a_1210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1211_: *mut LeanObject = core::ptr::null_mut();
    v_res_1211_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go(
        v_00_u03b1_1208_,
        v_a_1209_,
        v_a_1210_,
    );
    lean_dec_ref(v_a_1209_);
    return v_res_1211_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0(
    mut v_00_u03b1_1212_: *mut LeanObject,
    mut v_as_1213_: *mut LeanObject,
    mut v_i_1214_: usize,
    mut v_stop_1215_: usize,
    mut v_b_1216_: *mut LeanObject,
    mut v___y_1217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
    v___x_1218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___redArg(v_as_1213_, v_i_1214_, v_stop_1215_, v_b_1216_, v___y_1217_);
    return v___x_1218_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0___boxed(
    mut v_00_u03b1_1219_: *mut LeanObject,
    mut v_as_1220_: *mut LeanObject,
    mut v_i_1221_: *mut LeanObject,
    mut v_stop_1222_: *mut LeanObject,
    mut v_b_1223_: *mut LeanObject,
    mut v___y_1224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1225_: usize = 0;
    let mut v_stop_boxed_1226_: usize = 0;
    let mut v_res_1227_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1225_ = lean_unbox_usize(v_i_1221_);
    lean_dec(v_i_1221_);
    v_stop_boxed_1226_ = lean_unbox_usize(v_stop_1222_);
    lean_dec(v_stop_1222_);
    v_res_1227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_values_go_spec__0(v_00_u03b1_1219_, v_as_1220_, v_i_boxed_1225_, v_stop_boxed_1226_, v_b_1223_, v___y_1224_);
    lean_dec_ref(v_as_1220_);
    return v_res_1227_;
}
pub unsafe fn l_Lean_Data_Trie_values___redArg(mut v_t_1230_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1233_: *mut LeanObject = core::ptr::null_mut();
    v___x_1231_ = l_Lean_Data_Trie_values___redArg___closed__0;
    v___x_1232_ =
        l___private_Lean_Data_Trie_0__Lean_Data_Trie_values_go___redArg(v_t_1230_, v___x_1231_);
    v_snd_1233_ = lean_ctor_get(v___x_1232_, 1);
    lean_inc(v_snd_1233_);
    lean_dec_ref(v___x_1232_);
    return v_snd_1233_;
}
pub unsafe fn l_Lean_Data_Trie_values___redArg___boxed(
    mut v_t_1234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1235_: *mut LeanObject = core::ptr::null_mut();
    v_res_1235_ = l_Lean_Data_Trie_values___redArg(v_t_1234_);
    lean_dec_ref(v_t_1234_);
    return v_res_1235_;
}
pub unsafe fn l_Lean_Data_Trie_values(
    mut v_00_u03b1_1236_: *mut LeanObject,
    mut v_t_1237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    v___x_1238_ = l_Lean_Data_Trie_values___redArg(v_t_1237_);
    return v___x_1238_;
}
pub unsafe fn l_Lean_Data_Trie_values___boxed(
    mut v_00_u03b1_1239_: *mut LeanObject,
    mut v_t_1240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1241_: *mut LeanObject = core::ptr::null_mut();
    v_res_1241_ = l_Lean_Data_Trie_values(v_00_u03b1_1239_, v_t_1240_);
    lean_dec_ref(v_t_1240_);
    return v_res_1241_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(
    mut v_pre_1244_: *mut LeanObject,
    mut v_t_1245_: *mut LeanObject,
    mut v_i_1246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: u8 = 0;
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1250_: u8 = 0;
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1252_: u8 = 0;
    let mut v_a_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: u8 = 0;
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1247_ = lean_string_utf8_byte_size(v_pre_1244_);
                v___x_1248_ = lean_nat_dec_lt(v_i_1246_, v___x_1247_);
                if v___x_1248_ == 0 {
                    lean_dec(v_i_1246_);
                    v___x_1249_ = l_Lean_Data_Trie_values___redArg(v_t_1245_);
                    return v___x_1249_;
                } else {
                    lean_inc(v_i_1246_);
                    v_c_1250_ = lean_string_get_byte_fast(v_pre_1244_, v_i_1246_);
                    match lean_obj_tag(v_t_1245_) {
                        0 => {
                            lean_dec(v_i_1246_);
                            v___x_1251_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0;
                            return v___x_1251_;
                        }
                        1 => {
                            v_a_1252_ = lean_ctor_get_uint8(
                                v_t_1245_,
                                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                            );
                            v_a_1253_ = lean_ctor_get(v_t_1245_, 1);
                            v___x_1254_ = lean_uint8_dec_eq(v_c_1250_, v_a_1252_);
                            if v___x_1254_ == 0 {
                                lean_dec(v_i_1246_);
                                v___x_1255_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0;
                                return v___x_1255_;
                            } else {
                                v___x_1256_ = lean_unsigned_to_nat(1);
                                v___x_1257_ = lean_nat_add(v_i_1246_, v___x_1256_);
                                lean_dec(v_i_1246_);
                                v_t_1245_ = v_a_1253_;
                                v_i_1246_ = v___x_1257_;
                                state = 0;
                                continue;
                            }
                        }
                        _ => {
                            v_a_1259_ = lean_ctor_get(v_t_1245_, 1);
                            v_a_1260_ = lean_ctor_get(v_t_1245_, 2);
                            v___x_1261_ = lean_unsigned_to_nat(0);
                            v___x_1262_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_1250_, v_a_1259_, v___x_1261_);
                            if lean_obj_tag(v___x_1262_) == 0 {
                                lean_dec(v_i_1246_);
                                v___x_1263_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg___closed__0;
                                return v___x_1263_;
                            } else {
                                v_val_1264_ = lean_ctor_get(v___x_1262_, 0);
                                lean_inc(v_val_1264_);
                                lean_dec_ref_known(v___x_1262_, 1);
                                v___x_1265_ = lean_obj_once(
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
                                lean_dec(v_val_1264_);
                                v___x_1267_ = lean_unsigned_to_nat(1);
                                v___x_1268_ = lean_nat_add(v_i_1246_, v___x_1267_);
                                lean_dec(v_i_1246_);
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
    mut v_pre_1270_: *mut LeanObject,
    mut v_t_1271_: *mut LeanObject,
    mut v_i_1272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1273_: *mut LeanObject = core::ptr::null_mut();
    v_res_1273_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(
        v_pre_1270_,
        v_t_1271_,
        v_i_1272_,
    );
    lean_dec_ref(v_t_1271_);
    lean_dec_ref(v_pre_1270_);
    return v_res_1273_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go(
    mut v_00_u03b1_1274_: *mut LeanObject,
    mut v_pre_1275_: *mut LeanObject,
    mut v_t_1276_: *mut LeanObject,
    mut v_i_1277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    v___x_1278_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(
        v_pre_1275_,
        v_t_1276_,
        v_i_1277_,
    );
    return v___x_1278_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___boxed(
    mut v_00_u03b1_1279_: *mut LeanObject,
    mut v_pre_1280_: *mut LeanObject,
    mut v_t_1281_: *mut LeanObject,
    mut v_i_1282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1283_: *mut LeanObject = core::ptr::null_mut();
    v_res_1283_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go(
        v_00_u03b1_1279_,
        v_pre_1280_,
        v_t_1281_,
        v_i_1282_,
    );
    lean_dec_ref(v_t_1281_);
    lean_dec_ref(v_pre_1280_);
    return v_res_1283_;
}
pub unsafe fn l_Lean_Data_Trie_findPrefix___redArg(
    mut v_t_1284_: *mut LeanObject,
    mut v_pre_1285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    v___x_1286_ = lean_unsigned_to_nat(0);
    v___x_1287_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_findPrefix_go___redArg(
        v_pre_1285_,
        v_t_1284_,
        v___x_1286_,
    );
    return v___x_1287_;
}
pub unsafe fn l_Lean_Data_Trie_findPrefix___redArg___boxed(
    mut v_t_1288_: *mut LeanObject,
    mut v_pre_1289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1290_: *mut LeanObject = core::ptr::null_mut();
    v_res_1290_ = l_Lean_Data_Trie_findPrefix___redArg(v_t_1288_, v_pre_1289_);
    lean_dec_ref(v_pre_1289_);
    lean_dec_ref(v_t_1288_);
    return v_res_1290_;
}
pub unsafe fn l_Lean_Data_Trie_findPrefix(
    mut v_00_u03b1_1291_: *mut LeanObject,
    mut v_t_1292_: *mut LeanObject,
    mut v_pre_1293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    v___x_1294_ = l_Lean_Data_Trie_findPrefix___redArg(v_t_1292_, v_pre_1293_);
    return v___x_1294_;
}
pub unsafe fn l_Lean_Data_Trie_findPrefix___boxed(
    mut v_00_u03b1_1295_: *mut LeanObject,
    mut v_t_1296_: *mut LeanObject,
    mut v_pre_1297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1298_: *mut LeanObject = core::ptr::null_mut();
    v_res_1298_ = l_Lean_Data_Trie_findPrefix(v_00_u03b1_1295_, v_t_1296_, v_pre_1297_);
    lean_dec_ref(v_pre_1297_);
    lean_dec_ref(v_t_1296_);
    return v_res_1298_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__12() -> *mut LeanObject {
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    v___x_1325_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__10;
    v___x_1326_ = l_Lean_mkAtom(v___x_1325_);
    return v___x_1326_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__13() -> *mut LeanObject {
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    v___x_1327_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__12_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__12,
    );
    v___x_1328_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__5;
    v___x_1329_ = lean_array_push(v___x_1328_, v___x_1327_);
    return v___x_1329_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__17() -> *mut LeanObject {
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    v___x_1340_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__16;
    v___x_1341_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__5;
    v___x_1342_ = lean_array_push(v___x_1341_, v___x_1340_);
    return v___x_1342_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__18() -> *mut LeanObject {
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    v___x_1343_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__17_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__17,
    );
    v___x_1344_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__15;
    v___x_1345_ = lean_box(2);
    v___x_1346_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1346_, 0, v___x_1345_);
    lean_ctor_set(v___x_1346_, 1, v___x_1344_);
    lean_ctor_set(v___x_1346_, 2, v___x_1343_);
    return v___x_1346_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__19() -> *mut LeanObject {
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    v___x_1347_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__18_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__18,
    );
    v___x_1348_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__13_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__13,
    );
    v___x_1349_ = lean_array_push(v___x_1348_, v___x_1347_);
    return v___x_1349_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__20() -> *mut LeanObject {
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    v___x_1350_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__16;
    v___x_1351_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__19_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__19,
    );
    v___x_1352_ = lean_array_push(v___x_1351_, v___x_1350_);
    return v___x_1352_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__21() -> *mut LeanObject {
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    v___x_1353_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__16;
    v___x_1354_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__20_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__20,
    );
    v___x_1355_ = lean_array_push(v___x_1354_, v___x_1353_);
    return v___x_1355_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__22() -> *mut LeanObject {
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    v___x_1356_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__16;
    v___x_1357_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__21_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__21,
    );
    v___x_1358_ = lean_array_push(v___x_1357_, v___x_1356_);
    return v___x_1358_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__23() -> *mut LeanObject {
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    v___x_1359_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__16;
    v___x_1360_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__22_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__22,
    );
    v___x_1361_ = lean_array_push(v___x_1360_, v___x_1359_);
    return v___x_1361_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__24() -> *mut LeanObject {
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    v___x_1362_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__23_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__23,
    );
    v___x_1363_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__11;
    v___x_1364_ = lean_box(2);
    v___x_1365_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1365_, 0, v___x_1364_);
    lean_ctor_set(v___x_1365_, 1, v___x_1363_);
    lean_ctor_set(v___x_1365_, 2, v___x_1362_);
    return v___x_1365_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__25() -> *mut LeanObject {
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    v___x_1366_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__24_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__24,
    );
    v___x_1367_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__5;
    v___x_1368_ = lean_array_push(v___x_1367_, v___x_1366_);
    return v___x_1368_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__26() -> *mut LeanObject {
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    v___x_1369_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__25_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__25,
    );
    v___x_1370_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__9;
    v___x_1371_ = lean_box(2);
    v___x_1372_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1372_, 0, v___x_1371_);
    lean_ctor_set(v___x_1372_, 1, v___x_1370_);
    lean_ctor_set(v___x_1372_, 2, v___x_1369_);
    return v___x_1372_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__27() -> *mut LeanObject {
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    v___x_1373_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__26_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__26,
    );
    v___x_1374_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__5;
    v___x_1375_ = lean_array_push(v___x_1374_, v___x_1373_);
    return v___x_1375_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__28() -> *mut LeanObject {
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    v___x_1376_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__27_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__27,
    );
    v___x_1377_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__7;
    v___x_1378_ = lean_box(2);
    v___x_1379_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1379_, 0, v___x_1378_);
    lean_ctor_set(v___x_1379_, 1, v___x_1377_);
    lean_ctor_set(v___x_1379_, 2, v___x_1376_);
    return v___x_1379_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__29() -> *mut LeanObject {
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    v___x_1380_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__28_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__28,
    );
    v___x_1381_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__5;
    v___x_1382_ = lean_array_push(v___x_1381_, v___x_1380_);
    return v___x_1382_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__30() -> *mut LeanObject {
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    v___x_1383_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__29_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__29,
    );
    v___x_1384_ = l_Lean_Data_Trie_matchPrefix___auto__1___closed__4;
    v___x_1385_ = lean_box(2);
    v___x_1386_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_1386_, 0, v___x_1385_);
    lean_ctor_set(v___x_1386_, 1, v___x_1384_);
    lean_ctor_set(v___x_1386_, 2, v___x_1383_);
    return v___x_1386_;
}
pub unsafe fn _init_l_Lean_Data_Trie_matchPrefix___auto__1() -> *mut LeanObject {
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    v___x_1387_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__30),
        core::ptr::addr_of_mut!(l_Lean_Data_Trie_matchPrefix___auto__1___closed__30_once),
        _init_l_Lean_Data_Trie_matchPrefix___auto__1___closed__30,
    );
    return v___x_1387_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg(
    mut v_s_1388_: *mut LeanObject,
    mut v_endByte_1389_: *mut LeanObject,
    mut v_x_1390_: *mut LeanObject,
    mut v_x_1391_: *mut LeanObject,
    mut v_x_1392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1395_: u8 = 0;
    let mut v_a_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1398_: u8 = 0;
    let mut v___y_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1400_: u8 = 0;
    let mut v___x_1401_: u8 = 0;
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: u8 = 0;
    let mut v___x_1406_: u8 = 0;
    let mut v_a_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1411_: u8 = 0;
    let mut v___y_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1413_: u8 = 0;
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: u8 = 0;
    let mut v___x_1423_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_1390_) {
                0 => {
                    lean_dec(v_x_1391_);
                    v_a_1393_ = lean_ctor_get(v_x_1390_, 0);
                    if lean_obj_tag(v_a_1393_) == 0 {
                        lean_inc(v_x_1392_);
                        return v_x_1392_;
                    } else {
                        lean_inc_ref(v_a_1393_);
                        return v_a_1393_;
                    }
                }
                1 => {
                    v_a_1394_ = lean_ctor_get(v_x_1390_, 0);
                    v_a_1395_ = lean_ctor_get_uint8(
                        v_x_1390_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v_a_1396_ = lean_ctor_get(v_x_1390_, 1);
                    if lean_obj_tag(v_a_1394_) == 0 {
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
                    v_a_1407_ = lean_ctor_get(v_x_1390_, 0);
                    v_a_1408_ = lean_ctor_get(v_x_1390_, 1);
                    v_a_1409_ = lean_ctor_get(v_x_1390_, 2);
                    if lean_obj_tag(v_a_1407_) == 0 {
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
                    lean_dec(v_x_1391_);
                    lean_inc(v___y_1399_);
                    return v___y_1399_;
                } else {
                    lean_inc(v_x_1391_);
                    v_c_1400_ = lean_string_get_byte_fast(v_s_1388_, v_x_1391_);
                    v___x_1401_ = lean_uint8_dec_eq(v_c_1400_, v_a_1395_);
                    if v___x_1401_ == 0 {
                        lean_dec(v_x_1391_);
                        lean_inc(v___y_1399_);
                        return v___y_1399_;
                    } else {
                        v___x_1402_ = lean_unsigned_to_nat(1);
                        v___x_1403_ = lean_nat_add(v_x_1391_, v___x_1402_);
                        lean_dec(v_x_1391_);
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
                    lean_dec(v_x_1391_);
                    lean_inc(v___y_1412_);
                    return v___y_1412_;
                } else {
                    lean_inc(v_x_1391_);
                    v_c_1413_ = lean_string_get_byte_fast(v_s_1388_, v_x_1391_);
                    v___x_1414_ = lean_unsigned_to_nat(0);
                    v___x_1415_ = l_ByteArray_findIdx_x3f_loop___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_upsert_loop_spec__0(v_c_1413_, v_a_1408_, v___x_1414_);
                    if lean_obj_tag(v___x_1415_) == 0 {
                        lean_dec(v_x_1391_);
                        lean_inc(v___y_1412_);
                        return v___y_1412_;
                    } else {
                        v_val_1416_ = lean_ctor_get(v___x_1415_, 0);
                        lean_inc(v_val_1416_);
                        lean_dec_ref_known(v___x_1415_, 1);
                        v___x_1417_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Data_Trie_instEmptyCollection___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Data_Trie_instEmptyCollection___closed__0_once
                            ),
                            _init_l_Lean_Data_Trie_instEmptyCollection___closed__0,
                        );
                        v___x_1418_ = lean_array_get_borrowed(v___x_1417_, v_a_1409_, v_val_1416_);
                        lean_dec(v_val_1416_);
                        v___x_1419_ = lean_unsigned_to_nat(1);
                        v___x_1420_ = lean_nat_add(v_x_1391_, v___x_1419_);
                        lean_dec(v_x_1391_);
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
    mut v_s_1424_: *mut LeanObject,
    mut v_endByte_1425_: *mut LeanObject,
    mut v_x_1426_: *mut LeanObject,
    mut v_x_1427_: *mut LeanObject,
    mut v_x_1428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1429_: *mut LeanObject = core::ptr::null_mut();
    v_res_1429_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop___redArg(
        v_s_1424_,
        v_endByte_1425_,
        v_x_1426_,
        v_x_1427_,
        v_x_1428_,
    );
    lean_dec(v_x_1428_);
    lean_dec_ref(v_x_1426_);
    lean_dec(v_endByte_1425_);
    lean_dec_ref(v_s_1424_);
    return v_res_1429_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop(
    mut v_00_u03b1_1430_: *mut LeanObject,
    mut v_s_1431_: *mut LeanObject,
    mut v_endByte_1432_: *mut LeanObject,
    mut v_endByte__valid_1433_: *mut LeanObject,
    mut v_x_1434_: *mut LeanObject,
    mut v_x_1435_: *mut LeanObject,
    mut v_x_1436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1438_: *mut LeanObject,
    mut v_s_1439_: *mut LeanObject,
    mut v_endByte_1440_: *mut LeanObject,
    mut v_endByte__valid_1441_: *mut LeanObject,
    mut v_x_1442_: *mut LeanObject,
    mut v_x_1443_: *mut LeanObject,
    mut v_x_1444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1445_: *mut LeanObject = core::ptr::null_mut();
    v_res_1445_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_matchPrefix_loop(
        v_00_u03b1_1438_,
        v_s_1439_,
        v_endByte_1440_,
        v_endByte__valid_1441_,
        v_x_1442_,
        v_x_1443_,
        v_x_1444_,
    );
    lean_dec(v_x_1444_);
    lean_dec_ref(v_x_1442_);
    lean_dec(v_endByte_1440_);
    lean_dec_ref(v_s_1439_);
    return v_res_1445_;
}
pub unsafe fn l_Lean_Data_Trie_matchPrefix___redArg(
    mut v_s_1446_: *mut LeanObject,
    mut v_t_1447_: *mut LeanObject,
    mut v_i_1448_: *mut LeanObject,
    mut v_endByte_1449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    v___x_1450_ = lean_box(0);
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
    mut v_s_1452_: *mut LeanObject,
    mut v_t_1453_: *mut LeanObject,
    mut v_i_1454_: *mut LeanObject,
    mut v_endByte_1455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1456_: *mut LeanObject = core::ptr::null_mut();
    v_res_1456_ =
        l_Lean_Data_Trie_matchPrefix___redArg(v_s_1452_, v_t_1453_, v_i_1454_, v_endByte_1455_);
    lean_dec(v_endByte_1455_);
    lean_dec_ref(v_t_1453_);
    lean_dec_ref(v_s_1452_);
    return v_res_1456_;
}
pub unsafe fn l_Lean_Data_Trie_matchPrefix(
    mut v_00_u03b1_1457_: *mut LeanObject,
    mut v_s_1458_: *mut LeanObject,
    mut v_t_1459_: *mut LeanObject,
    mut v_i_1460_: *mut LeanObject,
    mut v_endByte_1461_: *mut LeanObject,
    mut v_endByte__valid_1462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    v___x_1463_ =
        l_Lean_Data_Trie_matchPrefix___redArg(v_s_1458_, v_t_1459_, v_i_1460_, v_endByte_1461_);
    return v___x_1463_;
}
pub unsafe fn l_Lean_Data_Trie_matchPrefix___boxed(
    mut v_00_u03b1_1464_: *mut LeanObject,
    mut v_s_1465_: *mut LeanObject,
    mut v_t_1466_: *mut LeanObject,
    mut v_i_1467_: *mut LeanObject,
    mut v_endByte_1468_: *mut LeanObject,
    mut v_endByte__valid_1469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1470_: *mut LeanObject = core::ptr::null_mut();
    v_res_1470_ = l_Lean_Data_Trie_matchPrefix(
        v_00_u03b1_1464_,
        v_s_1465_,
        v_t_1466_,
        v_i_1467_,
        v_endByte_1468_,
        v_endByte__valid_1469_,
    );
    lean_dec(v_endByte_1468_);
    lean_dec_ref(v_t_1466_);
    lean_dec_ref(v_s_1465_);
    return v_res_1470_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0_spec__0(
    mut v_x_1471_: *mut LeanObject,
    mut v_x_1472_: *mut LeanObject,
    mut v_x_1473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1478_: u8 = 0;
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1484_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1473_) == 0 {
                    lean_dec(v_x_1471_);
                    return v_x_1472_;
                } else {
                    v_head_1474_ = lean_ctor_get(v_x_1473_, 0);
                    v_tail_1475_ = lean_ctor_get(v_x_1473_, 1);
                    v_isSharedCheck_1484_ = (!lean_is_exclusive(v_x_1473_)) as u8;
                    if v_isSharedCheck_1484_ == 0 {
                        v___x_1477_ = v_x_1473_;
                        v_isShared_1478_ = v_isSharedCheck_1484_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1475_);
                        lean_inc(v_head_1474_);
                        lean_dec(v_x_1473_);
                        v___x_1477_ = lean_box(0);
                        v_isShared_1478_ = v_isSharedCheck_1484_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_1471_);
                if v_isShared_1478_ == 0 {
                    lean_ctor_set_tag(v___x_1477_, 5);
                    lean_ctor_set(v___x_1477_, 1, v_x_1471_);
                    lean_ctor_set(v___x_1477_, 0, v_x_1472_);
                    v___x_1480_ = v___x_1477_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1483_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_x_1472_);
                    lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_x_1471_);
                    v___x_1480_ = v_reuseFailAlloc_1483_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1481_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1481_, 0, v___x_1480_);
                lean_ctor_set(v___x_1481_, 1, v_head_1474_);
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
    mut v_x_1485_: *mut LeanObject,
    mut v_x_1486_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1485_) == 0 {
        let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1486_);
        v___x_1487_ = lean_box(0);
        return v___x_1487_;
    } else {
        let mut v_tail_1488_: *mut LeanObject = core::ptr::null_mut();
        v_tail_1488_ = lean_ctor_get(v_x_1485_, 1);
        if lean_obj_tag(v_tail_1488_) == 0 {
            let mut v_head_1489_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_1486_);
            v_head_1489_ = lean_ctor_get(v_x_1485_, 0);
            lean_inc(v_head_1489_);
            lean_dec_ref_known(v_x_1485_, 2);
            return v_head_1489_;
        } else {
            let mut v_head_1490_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_1488_);
            v_head_1490_ = lean_ctor_get(v_x_1485_, 0);
            lean_inc(v_head_1490_);
            lean_dec_ref_known(v_x_1485_, 2);
            v___x_1491_ = l_List_foldl___at___00Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0_spec__0(v_x_1486_, v_head_1490_, v_tail_1488_);
            return v___x_1491_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__1(
    mut v_a_1492_: *mut LeanObject,
    mut v_a_1493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1492_) == 0 {
                    v___x_1494_ = lean_array_to_list(v_a_1493_);
                    return v___x_1494_;
                } else {
                    v_head_1495_ = lean_ctor_get(v_a_1492_, 0);
                    lean_inc(v_head_1495_);
                    v_tail_1496_ = lean_ctor_get(v_a_1492_, 1);
                    lean_inc(v_tail_1496_);
                    lean_dec_ref_known(v_a_1492_, 2);
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
-> *mut LeanObject {
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    v___x_1499_ = lean_unsigned_to_nat(4);
    v___x_1500_ = lean_nat_to_int(v___x_1499_);
    return v___x_1500_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___boxed(
    mut v_c_1501_: *mut LeanObject,
    mut v_t_1502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_1503_: u8 = 0;
    let mut v_res_1504_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_1503_ = (lean_unbox(v_c_1501_) as u8);
    v_res_1504_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0(
        v_c_boxed_1503_,
        v_t_1502_,
    );
    return v_res_1504_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(
    mut v_x_1507_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1507_) {
        0 => {
            let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v_x_1507_, 1);
            v___x_1508_ = lean_box(0);
            return v___x_1508_;
        }
        1 => {
            let mut v_a_1509_: u8 = 0;
            let mut v_a_1510_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1519_: u8 = 0;
            let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
            v_a_1509_ = lean_ctor_get_uint8(
                v_x_1507_,
                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
            );
            v_a_1510_ = lean_ctor_get(v_x_1507_, 1);
            lean_inc_ref(v_a_1510_);
            lean_dec_ref_known(v_x_1507_, 2);
            v___x_1511_ = lean_uint8_to_nat(v_a_1509_);
            v___x_1512_ = l_Nat_reprFast(v___x_1511_);
            v___x_1513_ = lean_alloc_ctor(3, 1, (0) as u32);
            lean_ctor_set(v___x_1513_, 0, v___x_1512_);
            v___x_1514_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0_once), _init_l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0);
            v___x_1515_ = lean_box(1);
            v___x_1516_ =
                l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_a_1510_);
            v___x_1517_ = l_Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0(v___x_1516_, v___x_1515_);
            v___x_1518_ = lean_alloc_ctor(4, 2, (0) as u32);
            lean_ctor_set(v___x_1518_, 0, v___x_1514_);
            lean_ctor_set(v___x_1518_, 1, v___x_1517_);
            v___x_1519_ = 0;
            v___x_1520_ = lean_alloc_ctor(6, 1, (1) as u32);
            lean_ctor_set(v___x_1520_, 0, v___x_1518_);
            lean_ctor_set_uint8(
                v___x_1520_,
                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                v___x_1519_,
            );
            v___x_1521_ = lean_box(0);
            v___x_1522_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_1522_, 0, v___x_1520_);
            lean_ctor_set(v___x_1522_, 1, v___x_1521_);
            v___x_1523_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_1523_, 0, v___x_1513_);
            lean_ctor_set(v___x_1523_, 1, v___x_1522_);
            return v___x_1523_;
        }
        _ => {
            let mut v_a_1524_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_1525_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_1526_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
            v_a_1524_ = lean_ctor_get(v_x_1507_, 1);
            lean_inc_ref(v_a_1524_);
            v_a_1525_ = lean_ctor_get(v_x_1507_, 2);
            lean_inc_ref(v_a_1525_);
            lean_dec_ref_known(v_x_1507_, 3);
            v___f_1526_ = lean_alloc_closure(
                l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___boxed
                    as *mut core::ffi::c_void,
                2,
                0,
            );
            v___x_1527_ = l_ByteArray_toList(v_a_1524_);
            lean_dec_ref(v_a_1524_);
            v___x_1528_ = lean_array_to_list(v_a_1525_);
            v___x_1529_ =
                l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___closed__0;
            v___x_1530_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(
                lean_box(0),
                lean_box(0),
                lean_box(0),
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
    mut v_t_1533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: u8 = 0;
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    v___x_1534_ = lean_uint8_to_nat(v_c_1532_);
    v___x_1535_ = l_Nat_reprFast(v___x_1534_);
    v___x_1536_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1536_, 0, v___x_1535_);
    v___x_1537_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0_once), _init_l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg___lam__0___closed__0);
    v___x_1538_ = lean_box(1);
    v___x_1539_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_1533_);
    v___x_1540_ = l_Std_Format_joinSep___at___00__private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux_spec__0(v___x_1539_, v___x_1538_);
    v___x_1541_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1541_, 0, v___x_1537_);
    lean_ctor_set(v___x_1541_, 1, v___x_1540_);
    v___x_1542_ = 0;
    v___x_1543_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1543_, 0, v___x_1541_);
    lean_ctor_set_uint8(
        v___x_1543_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1542_,
    );
    v___x_1544_ = lean_box(0);
    v___x_1545_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1545_, 0, v___x_1543_);
    lean_ctor_set(v___x_1545_, 1, v___x_1544_);
    v___x_1546_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1546_, 0, v___x_1536_);
    lean_ctor_set(v___x_1546_, 1, v___x_1545_);
    return v___x_1546_;
}
pub unsafe fn l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux(
    mut v_00_u03b1_1547_: *mut LeanObject,
    mut v_x_1548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    v___x_1549_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_x_1548_);
    return v___x_1549_;
}
pub unsafe fn l_Lean_Data_Trie_instToString___private__1___redArg(
    mut v_t_1551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    v___f_1552_ = l_Lean_Data_Trie_instToString___private__1___redArg___closed__0;
    v___x_1553_ = lean_box(1);
    v___x_1554_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_1551_);
    v___x_1555_ = l_Std_Format_joinSep___redArg(v___f_1552_, v___x_1554_, v___x_1553_);
    v___x_1556_ = l_Std_Format_defWidth;
    v___x_1557_ = lean_unsigned_to_nat(0);
    v___x_1558_ = l_Std_Format_pretty(v___x_1555_, v___x_1556_, v___x_1557_, v___x_1557_);
    return v___x_1558_;
}
pub unsafe fn l_Lean_Data_Trie_instToString___private__1(
    mut v_00_u03b1_1559_: *mut LeanObject,
    mut v_t_1560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    v___f_1561_ = l_Lean_Data_Trie_instToString___private__1___redArg___closed__0;
    v___x_1562_ = lean_box(1);
    v___x_1563_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_1560_);
    v___x_1564_ = l_Std_Format_joinSep___redArg(v___f_1561_, v___x_1563_, v___x_1562_);
    v___x_1565_ = l_Std_Format_defWidth;
    v___x_1566_ = lean_unsigned_to_nat(0);
    v___x_1567_ = l_Std_Format_pretty(v___x_1564_, v___x_1565_, v___x_1566_, v___x_1566_);
    return v___x_1567_;
}
pub unsafe fn l_Lean_Data_Trie_instToString___lam__0(
    mut v_t_1568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    v___f_1569_ = l_Lean_Data_Trie_instToString___private__1___redArg___closed__0;
    v___x_1570_ = lean_box(1);
    v___x_1571_ = l___private_Lean_Data_Trie_0__Lean_Data_Trie_toStringAux___redArg(v_t_1568_);
    v___x_1572_ = l_Std_Format_joinSep___redArg(v___f_1569_, v___x_1571_, v___x_1570_);
    v___x_1573_ = l_Std_Format_defWidth;
    v___x_1574_ = lean_unsigned_to_nat(0);
    v___x_1575_ = l_Std_Format_pretty(v___x_1572_, v___x_1573_, v___x_1574_, v___x_1574_);
    return v___x_1575_;
}
pub unsafe fn l_Lean_Data_Trie_instToString(
    mut v_00_u03b1_1577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1578_: *mut LeanObject = core::ptr::null_mut();
    v___f_1578_ = l_Lean_Data_Trie_instToString___closed__0;
    return v___f_1578_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Trie(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Format(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Coe(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Trie(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lean_Data_Trie_matchPrefix___auto__1 = _init_l_Lean_Data_Trie_matchPrefix___auto__1();
    lean_mark_persistent(l_Lean_Data_Trie_matchPrefix___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Trie(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Format(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Coe(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Trie(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Trie(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Data_Trie(builtin);
}

// Lean compiler output
// Module: Init.Data.ByteArray.Basic
// Imports: Init.Data.UInt.BasicAux Init.Data.Array.DecidableEq Init.Data.List.Attach Init.Data.Array.Bootstrap Init.Data.Array.Lemmas Init.Omega
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::Array::DecidableEq::{
    initialize_Init_Data_Array_DecidableEq, runtime_initialize_Init_Data_Array_DecidableEq,
};
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::List::Attach::{
    initialize_Init_Data_List_Attach, runtime_initialize_Init_Data_List_Attach,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::UInt::BasicAux::{
    initialize_Init_Data_UInt_BasicAux, runtime_initialize_Init_Data_UInt_BasicAux,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_ByteArray_empty, l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom,
};
use crate::lean_imports_rs::Init::Data::ByteArray::Basic::{
    lean_byte_array_copy_slice, lean_byte_array_fget, lean_byte_array_fset, lean_byte_array_get,
    lean_byte_array_hash, lean_byte_array_set, lean_byte_array_uget, lean_byte_array_uset,
    lean_sarray_dec_eq, lean_sarray_size,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_byte_array_size, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_uint8_of_nat,
    lean_usize_dec_eq,
};
pub static l_ByteArray_instBEq___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_ByteArray_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ByteArray_instBEq___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_instBEq___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_ByteArray_instBEq: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_instBEq___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_ByteArray_instInhabited: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_ByteArray_instEmptyCollection: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_ByteArray_uget___auto__1___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_ByteArray_uget___auto__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_ByteArray_uget___auto__1___closed__1_value: crate::leanh::LeanStringObject<7> =
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
static mut l_ByteArray_uget___auto__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_ByteArray_uget___auto__1___closed__2_value: crate::leanh::LeanStringObject<7> =
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
static mut l_ByteArray_uget___auto__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_ByteArray_uget___auto__1___closed__3_value: crate::leanh::LeanStringObject<10> =
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
static mut l_ByteArray_uget___auto__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_ByteArray_uget___auto__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_ByteArray_uget___auto__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_ByteArray_uget___auto__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_ByteArray_uget___auto__1___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__3_value)
                as *mut crate::leanh::LeanObject,
            8504843326314613972 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_ByteArray_uget___auto__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_ByteArray_uget___auto__1___closed__5_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_ByteArray_uget___auto__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_ByteArray_uget___auto__1___closed__6_value: crate::leanh::LeanStringObject<19> =
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
static mut l_ByteArray_uget___auto__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_ByteArray_uget___auto__1___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_ByteArray_uget___auto__1___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__7_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_ByteArray_uget___auto__1___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__7_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_ByteArray_uget___auto__1___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__7_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__6_value)
                as *mut crate::leanh::LeanObject,
            17228437386856258271 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_ByteArray_uget___auto__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_ByteArray_uget___auto__1___closed__8_value: crate::leanh::LeanStringObject<5> =
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
static mut l_ByteArray_uget___auto__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_ByteArray_uget___auto__1___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__8_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_ByteArray_uget___auto__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_ByteArray_uget___auto__1___closed__10_value: crate::leanh::LeanStringObject<22> =
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
static mut l_ByteArray_uget___auto__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_ByteArray_uget___auto__1___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__10_value)
                as *mut crate::leanh::LeanObject,
            3731765604234633101 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_ByteArray_uget___auto__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_ByteArray_uget___auto__1___closed__12_value: crate::leanh::LeanStringObject<16> =
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
static mut l_ByteArray_uget___auto__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_uget___auto__1___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_ByteArray_uget___auto__1___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_ByteArray_uget___auto__1___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_ByteArray_uget___auto__1___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_ByteArray_uget___auto__1___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_ByteArray_uget___auto__1___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_ByteArray_uget___auto__1___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_ByteArray_uget___auto__1___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_ByteArray_uget___auto__1___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_ByteArray_uget___auto__1___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_ByteArray_uget___auto__1___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_ByteArray_uget___auto__1___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_ByteArray_uget___auto__1___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_ByteArray_uget___auto__1___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_ByteArray_uget___auto__1___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_ByteArray_uget___auto__1___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_ByteArray_uget___auto__1___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_ByteArray_uget___auto__1___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_ByteArray_uget___auto__1___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_ByteArray_uget___auto__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_ByteArray_get___auto__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_ByteArray_instGetElemNatUInt8LtSize___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ByteArray_instGetElemNatUInt8LtSize___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_ByteArray_instGetElemNatUInt8LtSize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_instGetElemNatUInt8LtSize___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_ByteArray_instGetElemNatUInt8LtSize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_instGetElemNatUInt8LtSize___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_ByteArray_set___auto__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_ByteArray_uset___auto__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_ByteArray_instHashable___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_ByteArray_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ByteArray_instHashable___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_instHashable___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_ByteArray_instHashable: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_instHashable___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_ByteArray_instAppend___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_ByteArray_fastAppend___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ByteArray_instAppend___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_instAppend___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_ByteArray_instAppend: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_instAppend___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_ByteArray_foldl___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ByteArray_foldl___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_ByteArray_foldl___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ByteArray_foldl___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_ByteArray_foldl___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ByteArray_foldl___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_ByteArray_foldl___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ByteArray_foldl___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_ByteArray_foldl___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ByteArray_foldl___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_ByteArray_foldl___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ByteArray_foldl___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_ByteArray_foldl___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ByteArray_foldl___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_ByteArray_foldl___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_ByteArray_foldl___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_ByteArray_foldl___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_ByteArray_foldl___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_ByteArray_foldl___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_ByteArray_foldl___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_foldl___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_ByteArray_instInhabitedIterator_default___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_ByteArray_instInhabitedIterator_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_ByteArray_instInhabitedIterator_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_ByteArray_instInhabitedIterator: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_ByteArray_instSizeOfIterator___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_ByteArray_instSizeOfIterator___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_ByteArray_instSizeOfIterator___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_instSizeOfIterator___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_ByteArray_instSizeOfIterator: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_ByteArray_instSizeOfIterator___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_ByteArray_Iterator_curr___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_ByteArray_Iterator_curr___closed__0: u8 = 0;
pub unsafe fn l_ByteArray_beq___boxed(
    mut v_lhs_924_: *mut crate::leanh::LeanObject,
    mut v_rhs_925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_926_: u8 = 0;
    let mut v_r_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_926_ = lean_sarray_dec_eq(v_lhs_924_, v_rhs_925_);
    crate::leanh::lean_dec_ref(v_rhs_925_);
    crate::leanh::lean_dec_ref(v_lhs_924_);
    v_r_927_ = crate::leanh::lean_box((v_res_926_) as usize);
    return v_r_927_;
}
pub unsafe fn l_ByteArray_decEq___boxed(
    mut v_lhs_932_: *mut crate::leanh::LeanObject,
    mut v_rhs_933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_934_: u8 = 0;
    let mut v_r_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_934_ = lean_sarray_dec_eq(v_lhs_932_, v_rhs_933_);
    crate::leanh::lean_dec_ref(v_rhs_933_);
    crate::leanh::lean_dec_ref(v_lhs_932_);
    v_r_935_ = crate::leanh::lean_box((v_res_934_) as usize);
    return v_r_935_;
}
pub unsafe fn l_ByteArray_instDecidableEq(
    mut v_lhs_936_: *mut crate::leanh::LeanObject,
    mut v_rhs_937_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_938_: u8 = 0;
    v___x_938_ = lean_sarray_dec_eq(v_lhs_936_, v_rhs_937_);
    return v___x_938_;
}
pub unsafe fn l_ByteArray_instDecidableEq___boxed(
    mut v_lhs_939_: *mut crate::leanh::LeanObject,
    mut v_rhs_940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_941_: u8 = 0;
    let mut v_r_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_941_ = l_ByteArray_instDecidableEq(v_lhs_939_, v_rhs_940_);
    crate::leanh::lean_dec_ref(v_rhs_940_);
    crate::leanh::lean_dec_ref(v_lhs_939_);
    v_r_942_ = crate::leanh::lean_box((v_res_941_) as usize);
    return v_r_942_;
}
pub unsafe fn _init_l_ByteArray_instInhabited() -> *mut crate::leanh::LeanObject {
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_943_ = l_ByteArray_empty;
    return v___x_943_;
}
pub unsafe fn _init_l_ByteArray_instEmptyCollection() -> *mut crate::leanh::LeanObject {
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_944_ = l_ByteArray_empty;
    return v___x_944_;
}
pub unsafe fn l_ByteArray_usize___boxed(
    mut v_a_946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_947_: usize = 0;
    let mut v_r_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_947_ = lean_sarray_size(v_a_946_);
    crate::leanh::lean_dec_ref(v_a_946_);
    v_r_948_ = crate::leanh::lean_box_usize(v_res_947_);
    return v_r_948_;
}
pub unsafe fn _init_l_ByteArray_uget___auto__1___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_973_ = l_ByteArray_uget___auto__1___closed__12;
    v___x_974_ = l_Lean_mkAtom(v___x_973_);
    return v___x_974_;
}
pub unsafe fn _init_l_ByteArray_uget___auto__1___closed__14() -> *mut crate::leanh::LeanObject {
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_975_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__13_once),
        _init_l_ByteArray_uget___auto__1___closed__13,
    );
    v___x_976_ = l_ByteArray_uget___auto__1___closed__5;
    v___x_977_ = lean_array_push(v___x_976_, v___x_975_);
    return v___x_977_;
}
pub unsafe fn _init_l_ByteArray_uget___auto__1___closed__15() -> *mut crate::leanh::LeanObject {
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_978_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__14),
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__14_once),
        _init_l_ByteArray_uget___auto__1___closed__14,
    );
    v___x_979_ = l_ByteArray_uget___auto__1___closed__11;
    v___x_980_ = crate::leanh::lean_box(2);
    v___x_981_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_981_, 0, v___x_980_);
    crate::leanh::lean_ctor_set(v___x_981_, 1, v___x_979_);
    crate::leanh::lean_ctor_set(v___x_981_, 2, v___x_978_);
    return v___x_981_;
}
pub unsafe fn _init_l_ByteArray_uget___auto__1___closed__16() -> *mut crate::leanh::LeanObject {
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_982_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__15_once),
        _init_l_ByteArray_uget___auto__1___closed__15,
    );
    v___x_983_ = l_ByteArray_uget___auto__1___closed__5;
    v___x_984_ = lean_array_push(v___x_983_, v___x_982_);
    return v___x_984_;
}
pub unsafe fn _init_l_ByteArray_uget___auto__1___closed__17() -> *mut crate::leanh::LeanObject {
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_985_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__16_once),
        _init_l_ByteArray_uget___auto__1___closed__16,
    );
    v___x_986_ = l_ByteArray_uget___auto__1___closed__9;
    v___x_987_ = crate::leanh::lean_box(2);
    v___x_988_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_988_, 0, v___x_987_);
    crate::leanh::lean_ctor_set(v___x_988_, 1, v___x_986_);
    crate::leanh::lean_ctor_set(v___x_988_, 2, v___x_985_);
    return v___x_988_;
}
pub unsafe fn _init_l_ByteArray_uget___auto__1___closed__18() -> *mut crate::leanh::LeanObject {
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_989_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__17_once),
        _init_l_ByteArray_uget___auto__1___closed__17,
    );
    v___x_990_ = l_ByteArray_uget___auto__1___closed__5;
    v___x_991_ = lean_array_push(v___x_990_, v___x_989_);
    return v___x_991_;
}
pub unsafe fn _init_l_ByteArray_uget___auto__1___closed__19() -> *mut crate::leanh::LeanObject {
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_992_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__18_once),
        _init_l_ByteArray_uget___auto__1___closed__18,
    );
    v___x_993_ = l_ByteArray_uget___auto__1___closed__7;
    v___x_994_ = crate::leanh::lean_box(2);
    v___x_995_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_995_, 0, v___x_994_);
    crate::leanh::lean_ctor_set(v___x_995_, 1, v___x_993_);
    crate::leanh::lean_ctor_set(v___x_995_, 2, v___x_992_);
    return v___x_995_;
}
pub unsafe fn _init_l_ByteArray_uget___auto__1___closed__20() -> *mut crate::leanh::LeanObject {
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_996_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__19_once),
        _init_l_ByteArray_uget___auto__1___closed__19,
    );
    v___x_997_ = l_ByteArray_uget___auto__1___closed__5;
    v___x_998_ = lean_array_push(v___x_997_, v___x_996_);
    return v___x_998_;
}
pub unsafe fn _init_l_ByteArray_uget___auto__1___closed__21() -> *mut crate::leanh::LeanObject {
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_999_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__20_once),
        _init_l_ByteArray_uget___auto__1___closed__20,
    );
    v___x_1000_ = l_ByteArray_uget___auto__1___closed__4;
    v___x_1001_ = crate::leanh::lean_box(2);
    v___x_1002_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1002_, 0, v___x_1001_);
    crate::leanh::lean_ctor_set(v___x_1002_, 1, v___x_1000_);
    crate::leanh::lean_ctor_set(v___x_1002_, 2, v___x_999_);
    return v___x_1002_;
}
pub unsafe fn _init_l_ByteArray_uget___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1003_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__21_once),
        _init_l_ByteArray_uget___auto__1___closed__21,
    );
    return v___x_1003_;
}
pub unsafe fn l_ByteArray_uget___boxed(
    mut v_a_1007_: *mut crate::leanh::LeanObject,
    mut v_i_1008_: *mut crate::leanh::LeanObject,
    mut v_h_1009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1010_: usize = 0;
    let mut v_res_1011_: u8 = 0;
    let mut v_r_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1010_ = crate::leanh::lean_unbox_usize(v_i_1008_);
    crate::leanh::lean_dec(v_i_1008_);
    v_res_1011_ = lean_byte_array_uget(v_a_1007_, v_i_boxed_1010_);
    crate::leanh::lean_dec_ref(v_a_1007_);
    v_r_1012_ = crate::leanh::lean_box((v_res_1011_) as usize);
    return v_r_1012_;
}
pub unsafe fn l_ByteArray_get_x21___boxed(
    mut v_a_00___x40___internal___hyg_1015_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1017_: u8 = 0;
    let mut v_r_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1017_ = lean_byte_array_get(
        v_a_00___x40___internal___hyg_1015_,
        v_a_00___x40___internal___hyg_1016_,
    );
    crate::leanh::lean_dec(v_a_00___x40___internal___hyg_1016_);
    crate::leanh::lean_dec_ref(v_a_00___x40___internal___hyg_1015_);
    v_r_1018_ = crate::leanh::lean_box((v_res_1017_) as usize);
    return v_r_1018_;
}
pub unsafe fn _init_l_ByteArray_get___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1019_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__21_once),
        _init_l_ByteArray_uget___auto__1___closed__21,
    );
    return v___x_1019_;
}
pub unsafe fn l_ByteArray_get___boxed(
    mut v_a_1023_: *mut crate::leanh::LeanObject,
    mut v_i_1024_: *mut crate::leanh::LeanObject,
    mut v_h_1025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1026_: u8 = 0;
    let mut v_r_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1026_ = lean_byte_array_fget(v_a_1023_, v_i_1024_);
    crate::leanh::lean_dec(v_i_1024_);
    crate::leanh::lean_dec_ref(v_a_1023_);
    v_r_1027_ = crate::leanh::lean_box((v_res_1026_) as usize);
    return v_r_1027_;
}
pub unsafe fn l_ByteArray_instGetElemNatUInt8LtSize___lam__0(
    mut v_xs_1028_: *mut crate::leanh::LeanObject,
    mut v_i_1029_: *mut crate::leanh::LeanObject,
    mut v_h_1030_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1031_: u8 = 0;
    v___x_1031_ = lean_byte_array_fget(v_xs_1028_, v_i_1029_);
    return v___x_1031_;
}
pub unsafe fn l_ByteArray_instGetElemNatUInt8LtSize___lam__0___boxed(
    mut v_xs_1032_: *mut crate::leanh::LeanObject,
    mut v_i_1033_: *mut crate::leanh::LeanObject,
    mut v_h_1034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1035_: u8 = 0;
    let mut v_r_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1035_ = l_ByteArray_instGetElemNatUInt8LtSize___lam__0(v_xs_1032_, v_i_1033_, v_h_1034_);
    crate::leanh::lean_dec(v_i_1033_);
    crate::leanh::lean_dec_ref(v_xs_1032_);
    v_r_1036_ = crate::leanh::lean_box((v_res_1035_) as usize);
    return v_r_1036_;
}
pub unsafe fn l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___lam__0(
    mut v_xs_1039_: *mut crate::leanh::LeanObject,
    mut v_i_1040_: usize,
    mut v_h_1041_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1042_: u8 = 0;
    v___x_1042_ = lean_byte_array_uget(v_xs_1039_, v_i_1040_);
    return v___x_1042_;
}
pub unsafe fn l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___lam__0___boxed(
    mut v_xs_1043_: *mut crate::leanh::LeanObject,
    mut v_i_1044_: *mut crate::leanh::LeanObject,
    mut v_h_1045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1046_: usize = 0;
    let mut v_res_1047_: u8 = 0;
    let mut v_r_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1046_ = crate::leanh::lean_unbox_usize(v_i_1044_);
    crate::leanh::lean_dec(v_i_1044_);
    v_res_1047_ = l_ByteArray_instGetElemUSizeUInt8LtNatValToFinSize___lam__0(
        v_xs_1043_,
        v_i_boxed_1046_,
        v_h_1045_,
    );
    crate::leanh::lean_dec_ref(v_xs_1043_);
    v_r_1048_ = crate::leanh::lean_box((v_res_1047_) as usize);
    return v_r_1048_;
}
pub unsafe fn l_ByteArray_set_x21___boxed(
    mut v_a_00___x40___internal___hyg_1054_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1055_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_3__boxed_1057_: u8 = 0;
    let mut v_res_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_3__boxed_1057_ =
        (crate::leanh::lean_unbox(v_a_00___x40___internal___hyg_1056_) as u8);
    v_res_1058_ = lean_byte_array_set(
        v_a_00___x40___internal___hyg_1054_,
        v_a_00___x40___internal___hyg_1055_,
        v_a_00___x40___internal___hyg_3__boxed_1057_,
    );
    crate::leanh::lean_dec(v_a_00___x40___internal___hyg_1055_);
    return v_res_1058_;
}
pub unsafe fn _init_l_ByteArray_set___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1059_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__21_once),
        _init_l_ByteArray_uget___auto__1___closed__21,
    );
    return v___x_1059_;
}
pub unsafe fn l_ByteArray_set___boxed(
    mut v_a_1064_: *mut crate::leanh::LeanObject,
    mut v_i_1065_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1066_: *mut crate::leanh::LeanObject,
    mut v_h_1067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_1068_: u8 = 0;
    let mut v_res_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_1068_ =
        (crate::leanh::lean_unbox(v_a_00___x40___internal___hyg_1066_) as u8);
    v_res_1069_ = lean_byte_array_fset(
        v_a_1064_,
        v_i_1065_,
        v_a_00___x40___internal___hyg_1__boxed_1068_,
    );
    crate::leanh::lean_dec(v_i_1065_);
    return v_res_1069_;
}
pub unsafe fn _init_l_ByteArray_uset___auto__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1070_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_ByteArray_uget___auto__1___closed__21_once),
        _init_l_ByteArray_uget___auto__1___closed__21,
    );
    return v___x_1070_;
}
pub unsafe fn l_ByteArray_uset___boxed(
    mut v_a_1075_: *mut crate::leanh::LeanObject,
    mut v_i_1076_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_1077_: *mut crate::leanh::LeanObject,
    mut v_h_1078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1079_: usize = 0;
    let mut v_a_00___x40___internal___hyg_1__boxed_1080_: u8 = 0;
    let mut v_res_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1079_ = crate::leanh::lean_unbox_usize(v_i_1076_);
    crate::leanh::lean_dec(v_i_1076_);
    v_a_00___x40___internal___hyg_1__boxed_1080_ =
        (crate::leanh::lean_unbox(v_a_00___x40___internal___hyg_1077_) as u8);
    v_res_1081_ = lean_byte_array_uset(
        v_a_1075_,
        v_i_boxed_1079_,
        v_a_00___x40___internal___hyg_1__boxed_1080_,
    );
    return v_res_1081_;
}
pub unsafe fn l_ByteArray_hash___boxed(
    mut v_a_1083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1084_: u64 = 0;
    let mut v_r_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1084_ = lean_byte_array_hash(v_a_1083_);
    crate::leanh::lean_dec_ref(v_a_1083_);
    v_r_1085_ = crate::leanh::lean_box_uint64(v_res_1084_);
    return v_r_1085_;
}
pub unsafe fn l_ByteArray_isEmpty(mut v_s_1088_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: u8 = 0;
    v___x_1089_ = lean_byte_array_size(v_s_1088_);
    v___x_1090_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1091_ = lean_nat_dec_eq(v___x_1089_, v___x_1090_);
    return v___x_1091_;
}
pub unsafe fn l_ByteArray_isEmpty___boxed(
    mut v_s_1092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1093_: u8 = 0;
    let mut v_r_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1093_ = l_ByteArray_isEmpty(v_s_1092_);
    crate::leanh::lean_dec_ref(v_s_1092_);
    v_r_1094_ = crate::leanh::lean_box((v_res_1093_) as usize);
    return v_r_1094_;
}
pub unsafe fn l_ByteArray_copySlice___boxed(
    mut v_src_1101_: *mut crate::leanh::LeanObject,
    mut v_srcOff_1102_: *mut crate::leanh::LeanObject,
    mut v_dest_1103_: *mut crate::leanh::LeanObject,
    mut v_destOff_1104_: *mut crate::leanh::LeanObject,
    mut v_len_1105_: *mut crate::leanh::LeanObject,
    mut v_exact_1106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_exact_boxed_1107_: u8 = 0;
    let mut v_res_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_exact_boxed_1107_ = (crate::leanh::lean_unbox(v_exact_1106_) as u8);
    v_res_1108_ = lean_byte_array_copy_slice(
        v_src_1101_,
        v_srcOff_1102_,
        v_dest_1103_,
        v_destOff_1104_,
        v_len_1105_,
        v_exact_boxed_1107_,
    );
    crate::leanh::lean_dec_ref(v_src_1101_);
    return v_res_1108_;
}
pub unsafe fn l_ByteArray_extract(
    mut v_a_1109_: *mut crate::leanh::LeanObject,
    mut v_b_1110_: *mut crate::leanh::LeanObject,
    mut v_e_1111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: u8 = 0;
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1112_ = l_ByteArray_empty;
    v___x_1113_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1114_ = lean_nat_sub(v_e_1111_, v_b_1110_);
    v___x_1115_ = 1;
    v___x_1116_ = lean_byte_array_copy_slice(
        v_a_1109_,
        v_b_1110_,
        v___x_1112_,
        v___x_1113_,
        v___x_1114_,
        v___x_1115_,
    );
    return v___x_1116_;
}
pub unsafe fn l_ByteArray_extract___boxed(
    mut v_a_1117_: *mut crate::leanh::LeanObject,
    mut v_b_1118_: *mut crate::leanh::LeanObject,
    mut v_e_1119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1120_ = l_ByteArray_extract(v_a_1117_, v_b_1118_, v_e_1119_);
    crate::leanh::lean_dec(v_e_1119_);
    crate::leanh::lean_dec_ref(v_a_1117_);
    return v_res_1120_;
}
pub unsafe fn l_ByteArray_fastAppend(
    mut v_a_1121_: *mut crate::leanh::LeanObject,
    mut v_b_1122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: u8 = 0;
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1123_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1124_ = lean_byte_array_size(v_a_1121_);
    v___x_1125_ = lean_byte_array_size(v_b_1122_);
    v___x_1126_ = 0;
    v___x_1127_ = lean_byte_array_copy_slice(
        v_b_1122_,
        v___x_1123_,
        v_a_1121_,
        v___x_1124_,
        v___x_1125_,
        v___x_1126_,
    );
    return v___x_1127_;
}
pub unsafe fn l_ByteArray_fastAppend___boxed(
    mut v_a_1128_: *mut crate::leanh::LeanObject,
    mut v_b_1129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1130_ = l_ByteArray_fastAppend(v_a_1128_, v_b_1129_);
    crate::leanh::lean_dec_ref(v_b_1129_);
    return v_res_1130_;
}
pub unsafe fn l_ByteArray_toList_loop(
    mut v_bs_1133_: *mut crate::leanh::LeanObject,
    mut v_i_1134_: *mut crate::leanh::LeanObject,
    mut v_r_1135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: u8 = 0;
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: u8 = 0;
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1136_ = lean_byte_array_size(v_bs_1133_);
                v___x_1137_ = lean_nat_dec_lt(v_i_1134_, v___x_1136_);
                if v___x_1137_ == 0 {
                    crate::leanh::lean_dec(v_i_1134_);
                    v___x_1138_ = l_List_reverse___redArg(v_r_1135_);
                    return v___x_1138_;
                } else {
                    v___x_1139_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1140_ = lean_nat_add(v_i_1134_, v___x_1139_);
                    v___x_1141_ = lean_byte_array_get(v_bs_1133_, v_i_1134_);
                    crate::leanh::lean_dec(v_i_1134_);
                    v___x_1142_ = crate::leanh::lean_box((v___x_1141_) as usize);
                    v___x_1143_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1143_, 0, v___x_1142_);
                    crate::leanh::lean_ctor_set(v___x_1143_, 1, v_r_1135_);
                    v_i_1134_ = v___x_1140_;
                    v_r_1135_ = v___x_1143_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_toList_loop___boxed(
    mut v_bs_1145_: *mut crate::leanh::LeanObject,
    mut v_i_1146_: *mut crate::leanh::LeanObject,
    mut v_r_1147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1148_ = l_ByteArray_toList_loop(v_bs_1145_, v_i_1146_, v_r_1147_);
    crate::leanh::lean_dec_ref(v_bs_1145_);
    return v_res_1148_;
}
pub unsafe fn l_ByteArray_toList(
    mut v_bs_1149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1150_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1151_ = crate::leanh::lean_box(0);
    v___x_1152_ = l_ByteArray_toList_loop(v_bs_1149_, v___x_1150_, v___x_1151_);
    return v___x_1152_;
}
pub unsafe fn l_ByteArray_toList___boxed(
    mut v_bs_1153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1154_ = l_ByteArray_toList(v_bs_1153_);
    crate::leanh::lean_dec_ref(v_bs_1153_);
    return v_res_1154_;
}
pub unsafe fn l_ByteArray_findFinIdx_x3f_loop(
    mut v_a_1155_: *mut crate::leanh::LeanObject,
    mut v_p_1156_: *mut crate::leanh::LeanObject,
    mut v_i_1157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: u8 = 0;
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: u8 = 0;
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: u8 = 0;
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1158_ = lean_byte_array_size(v_a_1155_);
                v___x_1159_ = lean_nat_dec_lt(v_i_1157_, v___x_1158_);
                if v___x_1159_ == 0 {
                    crate::leanh::lean_dec(v_i_1157_);
                    crate::leanh::lean_dec_ref(v_p_1156_);
                    v___x_1160_ = crate::leanh::lean_box(0);
                    return v___x_1160_;
                } else {
                    v___x_1161_ = lean_byte_array_fget(v_a_1155_, v_i_1157_);
                    v___x_1162_ = crate::leanh::lean_box((v___x_1161_) as usize);
                    crate::leanh::lean_inc_ref(v_p_1156_);
                    v___x_1163_ = crate::leanh::lean_apply_1(v_p_1156_, v___x_1162_);
                    v___x_1164_ = (crate::leanh::lean_unbox(v___x_1163_) as u8);
                    if v___x_1164_ == 0 {
                        v___x_1165_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1166_ = lean_nat_add(v_i_1157_, v___x_1165_);
                        crate::leanh::lean_dec(v_i_1157_);
                        v_i_1157_ = v___x_1166_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_p_1156_);
                        v___x_1168_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1168_, 0, v_i_1157_);
                        return v___x_1168_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_findFinIdx_x3f_loop___boxed(
    mut v_a_1169_: *mut crate::leanh::LeanObject,
    mut v_p_1170_: *mut crate::leanh::LeanObject,
    mut v_i_1171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1172_ = l_ByteArray_findFinIdx_x3f_loop(v_a_1169_, v_p_1170_, v_i_1171_);
    crate::leanh::lean_dec_ref(v_a_1169_);
    return v_res_1172_;
}
pub unsafe fn l_ByteArray_findFinIdx_x3f(
    mut v_a_1173_: *mut crate::leanh::LeanObject,
    mut v_p_1174_: *mut crate::leanh::LeanObject,
    mut v_start_1175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1176_ = l_ByteArray_findFinIdx_x3f_loop(v_a_1173_, v_p_1174_, v_start_1175_);
    return v___x_1176_;
}
pub unsafe fn l_ByteArray_findFinIdx_x3f___boxed(
    mut v_a_1177_: *mut crate::leanh::LeanObject,
    mut v_p_1178_: *mut crate::leanh::LeanObject,
    mut v_start_1179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1180_ = l_ByteArray_findFinIdx_x3f(v_a_1177_, v_p_1178_, v_start_1179_);
    crate::leanh::lean_dec_ref(v_a_1177_);
    return v_res_1180_;
}
pub unsafe fn l_ByteArray_findIdx_x3f_loop(
    mut v_a_1181_: *mut crate::leanh::LeanObject,
    mut v_p_1182_: *mut crate::leanh::LeanObject,
    mut v_i_1183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: u8 = 0;
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: u8 = 0;
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: u8 = 0;
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1184_ = lean_byte_array_size(v_a_1181_);
                v___x_1185_ = lean_nat_dec_lt(v_i_1183_, v___x_1184_);
                if v___x_1185_ == 0 {
                    crate::leanh::lean_dec(v_i_1183_);
                    crate::leanh::lean_dec_ref(v_p_1182_);
                    v___x_1186_ = crate::leanh::lean_box(0);
                    return v___x_1186_;
                } else {
                    v___x_1187_ = lean_byte_array_fget(v_a_1181_, v_i_1183_);
                    v___x_1188_ = crate::leanh::lean_box((v___x_1187_) as usize);
                    crate::leanh::lean_inc_ref(v_p_1182_);
                    v___x_1189_ = crate::leanh::lean_apply_1(v_p_1182_, v___x_1188_);
                    v___x_1190_ = (crate::leanh::lean_unbox(v___x_1189_) as u8);
                    if v___x_1190_ == 0 {
                        v___x_1191_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1192_ = lean_nat_add(v_i_1183_, v___x_1191_);
                        crate::leanh::lean_dec(v_i_1183_);
                        v_i_1183_ = v___x_1192_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_p_1182_);
                        v___x_1194_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1194_, 0, v_i_1183_);
                        return v___x_1194_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_findIdx_x3f_loop___boxed(
    mut v_a_1195_: *mut crate::leanh::LeanObject,
    mut v_p_1196_: *mut crate::leanh::LeanObject,
    mut v_i_1197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1198_ = l_ByteArray_findIdx_x3f_loop(v_a_1195_, v_p_1196_, v_i_1197_);
    crate::leanh::lean_dec_ref(v_a_1195_);
    return v_res_1198_;
}
pub unsafe fn l_ByteArray_findIdx_x3f(
    mut v_a_1199_: *mut crate::leanh::LeanObject,
    mut v_p_1200_: *mut crate::leanh::LeanObject,
    mut v_start_1201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1202_ = l_ByteArray_findIdx_x3f_loop(v_a_1199_, v_p_1200_, v_start_1201_);
    return v___x_1202_;
}
pub unsafe fn l_ByteArray_findIdx_x3f___boxed(
    mut v_a_1203_: *mut crate::leanh::LeanObject,
    mut v_p_1204_: *mut crate::leanh::LeanObject,
    mut v_start_1205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1206_ = l_ByteArray_findIdx_x3f(v_a_1203_, v_p_1204_, v_start_1205_);
    crate::leanh::lean_dec_ref(v_a_1203_);
    return v_res_1206_;
}
pub unsafe fn l_ByteArray_forInUnsafe_loop___redArg___lam__0___boxed(
    mut v_toApplicative_1207_: *mut crate::leanh::LeanObject,
    mut v_i_1208_: *mut crate::leanh::LeanObject,
    mut v_inst_1209_: *mut crate::leanh::LeanObject,
    mut v_as_1210_: *mut crate::leanh::LeanObject,
    mut v_f_1211_: *mut crate::leanh::LeanObject,
    mut v_sz_1212_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1214_: usize = 0;
    let mut v_sz_boxed_1215_: usize = 0;
    let mut v_res_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1214_ = crate::leanh::lean_unbox_usize(v_i_1208_);
    crate::leanh::lean_dec(v_i_1208_);
    v_sz_boxed_1215_ = crate::leanh::lean_unbox_usize(v_sz_1212_);
    crate::leanh::lean_dec(v_sz_1212_);
    v_res_1216_ = l_ByteArray_forInUnsafe_loop___redArg___lam__0(
        v_toApplicative_1207_,
        v_i_boxed_1214_,
        v_inst_1209_,
        v_as_1210_,
        v_f_1211_,
        v_sz_boxed_1215_,
        v_____do__lift_1213_,
    );
    return v_res_1216_;
}
pub unsafe fn l_ByteArray_forInUnsafe_loop___redArg(
    mut v_inst_1217_: *mut crate::leanh::LeanObject,
    mut v_as_1218_: *mut crate::leanh::LeanObject,
    mut v_f_1219_: *mut crate::leanh::LeanObject,
    mut v_sz_1220_: usize,
    mut v_i_1221_: usize,
    mut v_b_1222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1223_: u8 = 0;
    v___x_1223_ = lean_usize_dec_lt(v_i_1221_, v_sz_1220_);
    if v___x_1223_ == 0 {
        let mut v_toApplicative_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_1219_);
        crate::leanh::lean_dec_ref(v_as_1218_);
        v_toApplicative_1224_ = crate::leanh::lean_ctor_get(v_inst_1217_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1224_);
        crate::leanh::lean_dec_ref(v_inst_1217_);
        v_toPure_1225_ = crate::leanh::lean_ctor_get(v_toApplicative_1224_, 1);
        crate::leanh::lean_inc(v_toPure_1225_);
        crate::leanh::lean_dec_ref(v_toApplicative_1224_);
        v___x_1226_ =
            crate::leanh::lean_apply_2(v_toPure_1225_, crate::leanh::lean_box(0), v_b_1222_);
        return v___x_1226_;
    } else {
        let mut v_toApplicative_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_1232_: u8 = 0;
        let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1227_ = crate::leanh::lean_ctor_get(v_inst_1217_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1227_);
        v_toBind_1228_ = crate::leanh::lean_ctor_get(v_inst_1217_, 1);
        crate::leanh::lean_inc(v_toBind_1228_);
        v___x_1229_ = crate::leanh::lean_box_usize(v_i_1221_);
        v___x_1230_ = crate::leanh::lean_box_usize(v_sz_1220_);
        crate::leanh::lean_inc(v_f_1219_);
        crate::leanh::lean_inc_ref(v_as_1218_);
        v___f_1231_ = crate::leanh::lean_alloc_closure(
            l_ByteArray_forInUnsafe_loop___redArg___lam__0___boxed as *mut core::ffi::c_void,
            7,
            6,
        );
        crate::leanh::lean_closure_set(v___f_1231_, 0, v_toApplicative_1227_);
        crate::leanh::lean_closure_set(v___f_1231_, 1, v___x_1229_);
        crate::leanh::lean_closure_set(v___f_1231_, 2, v_inst_1217_);
        crate::leanh::lean_closure_set(v___f_1231_, 3, v_as_1218_);
        crate::leanh::lean_closure_set(v___f_1231_, 4, v_f_1219_);
        crate::leanh::lean_closure_set(v___f_1231_, 5, v___x_1230_);
        v_a_1232_ = lean_byte_array_uget(v_as_1218_, v_i_1221_);
        crate::leanh::lean_dec_ref(v_as_1218_);
        v___x_1233_ = crate::leanh::lean_box((v_a_1232_) as usize);
        v___x_1234_ = crate::leanh::lean_apply_2(v_f_1219_, v___x_1233_, v_b_1222_);
        v___x_1235_ = crate::leanh::lean_apply_4(
            v_toBind_1228_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1234_,
            v___f_1231_,
        );
        return v___x_1235_;
    }
}
pub unsafe fn l_ByteArray_forInUnsafe_loop___redArg___lam__0(
    mut v_toApplicative_1236_: *mut crate::leanh::LeanObject,
    mut v_i_1237_: usize,
    mut v_inst_1238_: *mut crate::leanh::LeanObject,
    mut v_as_1239_: *mut crate::leanh::LeanObject,
    mut v_f_1240_: *mut crate::leanh::LeanObject,
    mut v_sz_1241_: usize,
    mut v_____do__lift_1242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_1242_) == 0 {
        let mut v_a_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_1240_);
        crate::leanh::lean_dec_ref(v_as_1239_);
        crate::leanh::lean_dec_ref(v_inst_1238_);
        v_a_1243_ = crate::leanh::lean_ctor_get(v_____do__lift_1242_, 0);
        crate::leanh::lean_inc(v_a_1243_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1242_, 1);
        v_toPure_1244_ = crate::leanh::lean_ctor_get(v_toApplicative_1236_, 1);
        crate::leanh::lean_inc(v_toPure_1244_);
        crate::leanh::lean_dec_ref(v_toApplicative_1236_);
        v___x_1245_ =
            crate::leanh::lean_apply_2(v_toPure_1244_, crate::leanh::lean_box(0), v_a_1243_);
        return v___x_1245_;
    } else {
        let mut v_a_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1247_: usize = 0;
        let mut v___x_1248_: usize = 0;
        let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_toApplicative_1236_);
        v_a_1246_ = crate::leanh::lean_ctor_get(v_____do__lift_1242_, 0);
        crate::leanh::lean_inc(v_a_1246_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1242_, 1);
        v___x_1247_ = 1usize;
        v___x_1248_ = lean_usize_add(v_i_1237_, v___x_1247_);
        v___x_1249_ = l_ByteArray_forInUnsafe_loop___redArg(
            v_inst_1238_,
            v_as_1239_,
            v_f_1240_,
            v_sz_1241_,
            v___x_1248_,
            v_a_1246_,
        );
        return v___x_1249_;
    }
}
pub unsafe fn l_ByteArray_forInUnsafe_loop___redArg___boxed(
    mut v_inst_1250_: *mut crate::leanh::LeanObject,
    mut v_as_1251_: *mut crate::leanh::LeanObject,
    mut v_f_1252_: *mut crate::leanh::LeanObject,
    mut v_sz_1253_: *mut crate::leanh::LeanObject,
    mut v_i_1254_: *mut crate::leanh::LeanObject,
    mut v_b_1255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1256_: usize = 0;
    let mut v_i_boxed_1257_: usize = 0;
    let mut v_res_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1256_ = crate::leanh::lean_unbox_usize(v_sz_1253_);
    crate::leanh::lean_dec(v_sz_1253_);
    v_i_boxed_1257_ = crate::leanh::lean_unbox_usize(v_i_1254_);
    crate::leanh::lean_dec(v_i_1254_);
    v_res_1258_ = l_ByteArray_forInUnsafe_loop___redArg(
        v_inst_1250_,
        v_as_1251_,
        v_f_1252_,
        v_sz_boxed_1256_,
        v_i_boxed_1257_,
        v_b_1255_,
    );
    return v_res_1258_;
}
pub unsafe fn l_ByteArray_forInUnsafe_loop(
    mut v_00_u03b2_1259_: *mut crate::leanh::LeanObject,
    mut v_m_1260_: *mut crate::leanh::LeanObject,
    mut v_inst_1261_: *mut crate::leanh::LeanObject,
    mut v_as_1262_: *mut crate::leanh::LeanObject,
    mut v_f_1263_: *mut crate::leanh::LeanObject,
    mut v_sz_1264_: usize,
    mut v_i_1265_: usize,
    mut v_b_1266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1267_ = l_ByteArray_forInUnsafe_loop___redArg(
        v_inst_1261_,
        v_as_1262_,
        v_f_1263_,
        v_sz_1264_,
        v_i_1265_,
        v_b_1266_,
    );
    return v___x_1267_;
}
pub unsafe fn l_ByteArray_forInUnsafe_loop___boxed(
    mut v_00_u03b2_1268_: *mut crate::leanh::LeanObject,
    mut v_m_1269_: *mut crate::leanh::LeanObject,
    mut v_inst_1270_: *mut crate::leanh::LeanObject,
    mut v_as_1271_: *mut crate::leanh::LeanObject,
    mut v_f_1272_: *mut crate::leanh::LeanObject,
    mut v_sz_1273_: *mut crate::leanh::LeanObject,
    mut v_i_1274_: *mut crate::leanh::LeanObject,
    mut v_b_1275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1276_: usize = 0;
    let mut v_i_boxed_1277_: usize = 0;
    let mut v_res_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1276_ = crate::leanh::lean_unbox_usize(v_sz_1273_);
    crate::leanh::lean_dec(v_sz_1273_);
    v_i_boxed_1277_ = crate::leanh::lean_unbox_usize(v_i_1274_);
    crate::leanh::lean_dec(v_i_1274_);
    v_res_1278_ = l_ByteArray_forInUnsafe_loop(
        v_00_u03b2_1268_,
        v_m_1269_,
        v_inst_1270_,
        v_as_1271_,
        v_f_1272_,
        v_sz_boxed_1276_,
        v_i_boxed_1277_,
        v_b_1275_,
    );
    return v_res_1278_;
}
pub unsafe fn l_ByteArray_forInUnsafe___redArg(
    mut v_inst_1279_: *mut crate::leanh::LeanObject,
    mut v_as_1280_: *mut crate::leanh::LeanObject,
    mut v_b_1281_: *mut crate::leanh::LeanObject,
    mut v_f_1282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_1283_: usize = 0;
    let mut v___x_1284_: usize = 0;
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_1283_ = lean_sarray_size(v_as_1280_);
    v___x_1284_ = 0usize;
    v___x_1285_ = l_ByteArray_forInUnsafe_loop___redArg(
        v_inst_1279_,
        v_as_1280_,
        v_f_1282_,
        v_sz_1283_,
        v___x_1284_,
        v_b_1281_,
    );
    return v___x_1285_;
}
pub unsafe fn l_ByteArray_forInUnsafe(
    mut v_00_u03b2_1286_: *mut crate::leanh::LeanObject,
    mut v_m_1287_: *mut crate::leanh::LeanObject,
    mut v_inst_1288_: *mut crate::leanh::LeanObject,
    mut v_as_1289_: *mut crate::leanh::LeanObject,
    mut v_b_1290_: *mut crate::leanh::LeanObject,
    mut v_f_1291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_1292_: usize = 0;
    let mut v___x_1293_: usize = 0;
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_1292_ = lean_sarray_size(v_as_1289_);
    v___x_1293_ = 0usize;
    v___x_1294_ = l_ByteArray_forInUnsafe_loop___redArg(
        v_inst_1288_,
        v_as_1289_,
        v_f_1291_,
        v_sz_1292_,
        v___x_1293_,
        v_b_1290_,
    );
    return v___x_1294_;
}
pub unsafe fn l_ByteArray_forIn_loop___redArg___lam__0___boxed(
    mut v_toPure_1295_: *mut crate::leanh::LeanObject,
    mut v_inst_1296_: *mut crate::leanh::LeanObject,
    mut v_as_1297_: *mut crate::leanh::LeanObject,
    mut v_f_1298_: *mut crate::leanh::LeanObject,
    mut v_n_1299_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1301_ = l_ByteArray_forIn_loop___redArg___lam__0(
        v_toPure_1295_,
        v_inst_1296_,
        v_as_1297_,
        v_f_1298_,
        v_n_1299_,
        v_____do__lift_1300_,
    );
    crate::leanh::lean_dec(v_n_1299_);
    return v_res_1301_;
}
pub unsafe fn l_ByteArray_forIn_loop___redArg(
    mut v_inst_1302_: *mut crate::leanh::LeanObject,
    mut v_as_1303_: *mut crate::leanh::LeanObject,
    mut v_f_1304_: *mut crate::leanh::LeanObject,
    mut v_i_1305_: *mut crate::leanh::LeanObject,
    mut v_b_1306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1311_: u8 = 0;
    v_toApplicative_1307_ = crate::leanh::lean_ctor_get(v_inst_1302_, 0);
    v_toBind_1308_ = crate::leanh::lean_ctor_get(v_inst_1302_, 1);
    crate::leanh::lean_inc(v_toBind_1308_);
    v_toPure_1309_ = crate::leanh::lean_ctor_get(v_toApplicative_1307_, 1);
    crate::leanh::lean_inc(v_toPure_1309_);
    v_zero_1310_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_1311_ = lean_nat_dec_eq(v_i_1305_, v_zero_1310_);
    if v_isZero_1311_ == 1 {
        let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toBind_1308_);
        crate::leanh::lean_dec(v_f_1304_);
        crate::leanh::lean_dec_ref(v_as_1303_);
        crate::leanh::lean_dec_ref(v_inst_1302_);
        v___x_1312_ =
            crate::leanh::lean_apply_2(v_toPure_1309_, crate::leanh::lean_box(0), v_b_1306_);
        return v___x_1312_;
    } else {
        let mut v_one_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1319_: u8 = 0;
        let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_one_1313_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_1314_ = lean_nat_sub(v_i_1305_, v_one_1313_);
        crate::leanh::lean_inc(v_n_1314_);
        crate::leanh::lean_inc(v_f_1304_);
        crate::leanh::lean_inc_ref(v_as_1303_);
        v___f_1315_ = crate::leanh::lean_alloc_closure(
            l_ByteArray_forIn_loop___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            5,
        );
        crate::leanh::lean_closure_set(v___f_1315_, 0, v_toPure_1309_);
        crate::leanh::lean_closure_set(v___f_1315_, 1, v_inst_1302_);
        crate::leanh::lean_closure_set(v___f_1315_, 2, v_as_1303_);
        crate::leanh::lean_closure_set(v___f_1315_, 3, v_f_1304_);
        crate::leanh::lean_closure_set(v___f_1315_, 4, v_n_1314_);
        v___x_1316_ = lean_byte_array_size(v_as_1303_);
        v___x_1317_ = lean_nat_sub(v___x_1316_, v_one_1313_);
        v___x_1318_ = lean_nat_sub(v___x_1317_, v_n_1314_);
        crate::leanh::lean_dec(v_n_1314_);
        crate::leanh::lean_dec(v___x_1317_);
        v___x_1319_ = lean_byte_array_fget(v_as_1303_, v___x_1318_);
        crate::leanh::lean_dec(v___x_1318_);
        crate::leanh::lean_dec_ref(v_as_1303_);
        v___x_1320_ = crate::leanh::lean_box((v___x_1319_) as usize);
        v___x_1321_ = crate::leanh::lean_apply_2(v_f_1304_, v___x_1320_, v_b_1306_);
        v___x_1322_ = crate::leanh::lean_apply_4(
            v_toBind_1308_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1321_,
            v___f_1315_,
        );
        return v___x_1322_;
    }
}
pub unsafe fn l_ByteArray_forIn_loop___redArg___lam__0(
    mut v_toPure_1323_: *mut crate::leanh::LeanObject,
    mut v_inst_1324_: *mut crate::leanh::LeanObject,
    mut v_as_1325_: *mut crate::leanh::LeanObject,
    mut v_f_1326_: *mut crate::leanh::LeanObject,
    mut v_n_1327_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_1328_) == 0 {
        let mut v_a_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_f_1326_);
        crate::leanh::lean_dec_ref(v_as_1325_);
        crate::leanh::lean_dec_ref(v_inst_1324_);
        v_a_1329_ = crate::leanh::lean_ctor_get(v_____do__lift_1328_, 0);
        crate::leanh::lean_inc(v_a_1329_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1328_, 1);
        v___x_1330_ =
            crate::leanh::lean_apply_2(v_toPure_1323_, crate::leanh::lean_box(0), v_a_1329_);
        return v___x_1330_;
    } else {
        let mut v_a_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_1323_);
        v_a_1331_ = crate::leanh::lean_ctor_get(v_____do__lift_1328_, 0);
        crate::leanh::lean_inc(v_a_1331_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1328_, 1);
        v___x_1332_ = l_ByteArray_forIn_loop___redArg(
            v_inst_1324_,
            v_as_1325_,
            v_f_1326_,
            v_n_1327_,
            v_a_1331_,
        );
        return v___x_1332_;
    }
}
pub unsafe fn l_ByteArray_forIn_loop___redArg___boxed(
    mut v_inst_1333_: *mut crate::leanh::LeanObject,
    mut v_as_1334_: *mut crate::leanh::LeanObject,
    mut v_f_1335_: *mut crate::leanh::LeanObject,
    mut v_i_1336_: *mut crate::leanh::LeanObject,
    mut v_b_1337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1338_ =
        l_ByteArray_forIn_loop___redArg(v_inst_1333_, v_as_1334_, v_f_1335_, v_i_1336_, v_b_1337_);
    crate::leanh::lean_dec(v_i_1336_);
    return v_res_1338_;
}
pub unsafe fn l_ByteArray_forIn_loop(
    mut v_00_u03b2_1339_: *mut crate::leanh::LeanObject,
    mut v_m_1340_: *mut crate::leanh::LeanObject,
    mut v_inst_1341_: *mut crate::leanh::LeanObject,
    mut v_as_1342_: *mut crate::leanh::LeanObject,
    mut v_f_1343_: *mut crate::leanh::LeanObject,
    mut v_i_1344_: *mut crate::leanh::LeanObject,
    mut v_h_1345_: *mut crate::leanh::LeanObject,
    mut v_b_1346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1347_ =
        l_ByteArray_forIn_loop___redArg(v_inst_1341_, v_as_1342_, v_f_1343_, v_i_1344_, v_b_1346_);
    return v___x_1347_;
}
pub unsafe fn l_ByteArray_forIn_loop___boxed(
    mut v_00_u03b2_1348_: *mut crate::leanh::LeanObject,
    mut v_m_1349_: *mut crate::leanh::LeanObject,
    mut v_inst_1350_: *mut crate::leanh::LeanObject,
    mut v_as_1351_: *mut crate::leanh::LeanObject,
    mut v_f_1352_: *mut crate::leanh::LeanObject,
    mut v_i_1353_: *mut crate::leanh::LeanObject,
    mut v_h_1354_: *mut crate::leanh::LeanObject,
    mut v_b_1355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1356_ = l_ByteArray_forIn_loop(
        v_00_u03b2_1348_,
        v_m_1349_,
        v_inst_1350_,
        v_as_1351_,
        v_f_1352_,
        v_i_1353_,
        v_h_1354_,
        v_b_1355_,
    );
    crate::leanh::lean_dec(v_i_1353_);
    return v_res_1356_;
}
pub unsafe fn l_ByteArray_instForInUInt8OfMonad___redArg___lam__0(
    mut v_inst_1357_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1358_: *mut crate::leanh::LeanObject,
    mut v___y_1359_: *mut crate::leanh::LeanObject,
    mut v___y_1360_: *mut crate::leanh::LeanObject,
    mut v___y_1361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_1362_: usize = 0;
    let mut v___x_1363_: usize = 0;
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_1362_ = lean_sarray_size(v___y_1359_);
    v___x_1363_ = 0usize;
    v___x_1364_ = l_ByteArray_forInUnsafe_loop___redArg(
        v_inst_1357_,
        v___y_1359_,
        v___y_1361_,
        v_sz_1362_,
        v___x_1363_,
        v___y_1360_,
    );
    return v___x_1364_;
}
pub unsafe fn l_ByteArray_instForInUInt8OfMonad___redArg(
    mut v_inst_1365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1366_ = crate::leanh::lean_alloc_closure(
        l_ByteArray_instForInUInt8OfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1366_, 0, v_inst_1365_);
    return v___f_1366_;
}
pub unsafe fn l_ByteArray_instForInUInt8OfMonad(
    mut v_m_1367_: *mut crate::leanh::LeanObject,
    mut v_inst_1368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1369_ = crate::leanh::lean_alloc_closure(
        l_ByteArray_instForInUInt8OfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1369_, 0, v_inst_1368_);
    return v___f_1369_;
}
pub unsafe fn l_ByteArray_foldlMUnsafe_fold___redArg___lam__0___boxed(
    mut v_i_1370_: *mut crate::leanh::LeanObject,
    mut v_inst_1371_: *mut crate::leanh::LeanObject,
    mut v_f_1372_: *mut crate::leanh::LeanObject,
    mut v_as_1373_: *mut crate::leanh::LeanObject,
    mut v_stop_1374_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1376_: usize = 0;
    let mut v_stop_boxed_1377_: usize = 0;
    let mut v_res_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1376_ = crate::leanh::lean_unbox_usize(v_i_1370_);
    crate::leanh::lean_dec(v_i_1370_);
    v_stop_boxed_1377_ = crate::leanh::lean_unbox_usize(v_stop_1374_);
    crate::leanh::lean_dec(v_stop_1374_);
    v_res_1378_ = l_ByteArray_foldlMUnsafe_fold___redArg___lam__0(
        v_i_boxed_1376_,
        v_inst_1371_,
        v_f_1372_,
        v_as_1373_,
        v_stop_boxed_1377_,
        v_____do__lift_1375_,
    );
    return v_res_1378_;
}
pub unsafe fn l_ByteArray_foldlMUnsafe_fold___redArg(
    mut v_inst_1379_: *mut crate::leanh::LeanObject,
    mut v_f_1380_: *mut crate::leanh::LeanObject,
    mut v_as_1381_: *mut crate::leanh::LeanObject,
    mut v_i_1382_: usize,
    mut v_stop_1383_: usize,
    mut v_b_1384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1385_: u8 = 0;
    v___x_1385_ = lean_usize_dec_eq(v_i_1382_, v_stop_1383_);
    if v___x_1385_ == 0 {
        let mut v_toBind_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1390_: u8 = 0;
        let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1386_ = crate::leanh::lean_ctor_get(v_inst_1379_, 1);
        crate::leanh::lean_inc(v_toBind_1386_);
        v___x_1387_ = crate::leanh::lean_box_usize(v_i_1382_);
        v___x_1388_ = crate::leanh::lean_box_usize(v_stop_1383_);
        crate::leanh::lean_inc_ref(v_as_1381_);
        crate::leanh::lean_inc(v_f_1380_);
        v___f_1389_ = crate::leanh::lean_alloc_closure(
            l_ByteArray_foldlMUnsafe_fold___redArg___lam__0___boxed as *mut core::ffi::c_void,
            6,
            5,
        );
        crate::leanh::lean_closure_set(v___f_1389_, 0, v___x_1387_);
        crate::leanh::lean_closure_set(v___f_1389_, 1, v_inst_1379_);
        crate::leanh::lean_closure_set(v___f_1389_, 2, v_f_1380_);
        crate::leanh::lean_closure_set(v___f_1389_, 3, v_as_1381_);
        crate::leanh::lean_closure_set(v___f_1389_, 4, v___x_1388_);
        v___x_1390_ = lean_byte_array_uget(v_as_1381_, v_i_1382_);
        crate::leanh::lean_dec_ref(v_as_1381_);
        v___x_1391_ = crate::leanh::lean_box((v___x_1390_) as usize);
        v___x_1392_ = crate::leanh::lean_apply_2(v_f_1380_, v_b_1384_, v___x_1391_);
        v___x_1393_ = crate::leanh::lean_apply_4(
            v_toBind_1386_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1392_,
            v___f_1389_,
        );
        return v___x_1393_;
    } else {
        let mut v_toApplicative_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_as_1381_);
        crate::leanh::lean_dec(v_f_1380_);
        v_toApplicative_1394_ = crate::leanh::lean_ctor_get(v_inst_1379_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1394_);
        crate::leanh::lean_dec_ref(v_inst_1379_);
        v_toPure_1395_ = crate::leanh::lean_ctor_get(v_toApplicative_1394_, 1);
        crate::leanh::lean_inc(v_toPure_1395_);
        crate::leanh::lean_dec_ref(v_toApplicative_1394_);
        v___x_1396_ =
            crate::leanh::lean_apply_2(v_toPure_1395_, crate::leanh::lean_box(0), v_b_1384_);
        return v___x_1396_;
    }
}
pub unsafe fn l_ByteArray_foldlMUnsafe_fold___redArg___lam__0(
    mut v_i_1397_: usize,
    mut v_inst_1398_: *mut crate::leanh::LeanObject,
    mut v_f_1399_: *mut crate::leanh::LeanObject,
    mut v_as_1400_: *mut crate::leanh::LeanObject,
    mut v_stop_1401_: usize,
    mut v_____do__lift_1402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1403_: usize = 0;
    let mut v___x_1404_: usize = 0;
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1403_ = 1usize;
    v___x_1404_ = lean_usize_add(v_i_1397_, v___x_1403_);
    v___x_1405_ = l_ByteArray_foldlMUnsafe_fold___redArg(
        v_inst_1398_,
        v_f_1399_,
        v_as_1400_,
        v___x_1404_,
        v_stop_1401_,
        v_____do__lift_1402_,
    );
    return v___x_1405_;
}
pub unsafe fn l_ByteArray_foldlMUnsafe_fold___redArg___boxed(
    mut v_inst_1406_: *mut crate::leanh::LeanObject,
    mut v_f_1407_: *mut crate::leanh::LeanObject,
    mut v_as_1408_: *mut crate::leanh::LeanObject,
    mut v_i_1409_: *mut crate::leanh::LeanObject,
    mut v_stop_1410_: *mut crate::leanh::LeanObject,
    mut v_b_1411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1412_: usize = 0;
    let mut v_stop_boxed_1413_: usize = 0;
    let mut v_res_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1412_ = crate::leanh::lean_unbox_usize(v_i_1409_);
    crate::leanh::lean_dec(v_i_1409_);
    v_stop_boxed_1413_ = crate::leanh::lean_unbox_usize(v_stop_1410_);
    crate::leanh::lean_dec(v_stop_1410_);
    v_res_1414_ = l_ByteArray_foldlMUnsafe_fold___redArg(
        v_inst_1406_,
        v_f_1407_,
        v_as_1408_,
        v_i_boxed_1412_,
        v_stop_boxed_1413_,
        v_b_1411_,
    );
    return v_res_1414_;
}
pub unsafe fn l_ByteArray_foldlMUnsafe_fold(
    mut v_00_u03b2_1415_: *mut crate::leanh::LeanObject,
    mut v_m_1416_: *mut crate::leanh::LeanObject,
    mut v_inst_1417_: *mut crate::leanh::LeanObject,
    mut v_f_1418_: *mut crate::leanh::LeanObject,
    mut v_as_1419_: *mut crate::leanh::LeanObject,
    mut v_i_1420_: usize,
    mut v_stop_1421_: usize,
    mut v_b_1422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1423_ = l_ByteArray_foldlMUnsafe_fold___redArg(
        v_inst_1417_,
        v_f_1418_,
        v_as_1419_,
        v_i_1420_,
        v_stop_1421_,
        v_b_1422_,
    );
    return v___x_1423_;
}
pub unsafe fn l_ByteArray_foldlMUnsafe_fold___boxed(
    mut v_00_u03b2_1424_: *mut crate::leanh::LeanObject,
    mut v_m_1425_: *mut crate::leanh::LeanObject,
    mut v_inst_1426_: *mut crate::leanh::LeanObject,
    mut v_f_1427_: *mut crate::leanh::LeanObject,
    mut v_as_1428_: *mut crate::leanh::LeanObject,
    mut v_i_1429_: *mut crate::leanh::LeanObject,
    mut v_stop_1430_: *mut crate::leanh::LeanObject,
    mut v_b_1431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1432_: usize = 0;
    let mut v_stop_boxed_1433_: usize = 0;
    let mut v_res_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1432_ = crate::leanh::lean_unbox_usize(v_i_1429_);
    crate::leanh::lean_dec(v_i_1429_);
    v_stop_boxed_1433_ = crate::leanh::lean_unbox_usize(v_stop_1430_);
    crate::leanh::lean_dec(v_stop_1430_);
    v_res_1434_ = l_ByteArray_foldlMUnsafe_fold(
        v_00_u03b2_1424_,
        v_m_1425_,
        v_inst_1426_,
        v_f_1427_,
        v_as_1428_,
        v_i_boxed_1432_,
        v_stop_boxed_1433_,
        v_b_1431_,
    );
    return v_res_1434_;
}
pub unsafe fn l_ByteArray_foldlMUnsafe___redArg(
    mut v_inst_1435_: *mut crate::leanh::LeanObject,
    mut v_f_1436_: *mut crate::leanh::LeanObject,
    mut v_init_1437_: *mut crate::leanh::LeanObject,
    mut v_as_1438_: *mut crate::leanh::LeanObject,
    mut v_start_1439_: *mut crate::leanh::LeanObject,
    mut v_stop_1440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1441_: u8 = 0;
    v___x_1441_ = lean_nat_dec_lt(v_start_1439_, v_stop_1440_);
    if v___x_1441_ == 0 {
        let mut v_toApplicative_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_as_1438_);
        crate::leanh::lean_dec(v_f_1436_);
        v_toApplicative_1442_ = crate::leanh::lean_ctor_get(v_inst_1435_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1442_);
        crate::leanh::lean_dec_ref(v_inst_1435_);
        v_toPure_1443_ = crate::leanh::lean_ctor_get(v_toApplicative_1442_, 1);
        crate::leanh::lean_inc(v_toPure_1443_);
        crate::leanh::lean_dec_ref(v_toApplicative_1442_);
        v___x_1444_ =
            crate::leanh::lean_apply_2(v_toPure_1443_, crate::leanh::lean_box(0), v_init_1437_);
        return v___x_1444_;
    } else {
        let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1446_: u8 = 0;
        v___x_1445_ = lean_byte_array_size(v_as_1438_);
        v___x_1446_ = lean_nat_dec_le(v_stop_1440_, v___x_1445_);
        if v___x_1446_ == 0 {
            let mut v___x_1447_: u8 = 0;
            v___x_1447_ = lean_nat_dec_lt(v_start_1439_, v___x_1445_);
            if v___x_1447_ == 0 {
                let mut v_toApplicative_1448_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_as_1438_);
                crate::leanh::lean_dec(v_f_1436_);
                v_toApplicative_1448_ = crate::leanh::lean_ctor_get(v_inst_1435_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_1448_);
                crate::leanh::lean_dec_ref(v_inst_1435_);
                v_toPure_1449_ = crate::leanh::lean_ctor_get(v_toApplicative_1448_, 1);
                crate::leanh::lean_inc(v_toPure_1449_);
                crate::leanh::lean_dec_ref(v_toApplicative_1448_);
                v___x_1450_ = crate::leanh::lean_apply_2(
                    v_toPure_1449_,
                    crate::leanh::lean_box(0),
                    v_init_1437_,
                );
                return v___x_1450_;
            } else {
                let mut v___x_1451_: usize = 0;
                let mut v___x_1452_: usize = 0;
                let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1451_ = lean_usize_of_nat(v_start_1439_);
                v___x_1452_ = lean_usize_of_nat(v___x_1445_);
                v___x_1453_ = l_ByteArray_foldlMUnsafe_fold___redArg(
                    v_inst_1435_,
                    v_f_1436_,
                    v_as_1438_,
                    v___x_1451_,
                    v___x_1452_,
                    v_init_1437_,
                );
                return v___x_1453_;
            }
        } else {
            let mut v___x_1454_: usize = 0;
            let mut v___x_1455_: usize = 0;
            let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1454_ = lean_usize_of_nat(v_start_1439_);
            v___x_1455_ = lean_usize_of_nat(v_stop_1440_);
            v___x_1456_ = l_ByteArray_foldlMUnsafe_fold___redArg(
                v_inst_1435_,
                v_f_1436_,
                v_as_1438_,
                v___x_1454_,
                v___x_1455_,
                v_init_1437_,
            );
            return v___x_1456_;
        }
    }
}
pub unsafe fn l_ByteArray_foldlMUnsafe___redArg___boxed(
    mut v_inst_1457_: *mut crate::leanh::LeanObject,
    mut v_f_1458_: *mut crate::leanh::LeanObject,
    mut v_init_1459_: *mut crate::leanh::LeanObject,
    mut v_as_1460_: *mut crate::leanh::LeanObject,
    mut v_start_1461_: *mut crate::leanh::LeanObject,
    mut v_stop_1462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1463_ = l_ByteArray_foldlMUnsafe___redArg(
        v_inst_1457_,
        v_f_1458_,
        v_init_1459_,
        v_as_1460_,
        v_start_1461_,
        v_stop_1462_,
    );
    crate::leanh::lean_dec(v_stop_1462_);
    crate::leanh::lean_dec(v_start_1461_);
    return v_res_1463_;
}
pub unsafe fn l_ByteArray_foldlMUnsafe(
    mut v_00_u03b2_1464_: *mut crate::leanh::LeanObject,
    mut v_m_1465_: *mut crate::leanh::LeanObject,
    mut v_inst_1466_: *mut crate::leanh::LeanObject,
    mut v_f_1467_: *mut crate::leanh::LeanObject,
    mut v_init_1468_: *mut crate::leanh::LeanObject,
    mut v_as_1469_: *mut crate::leanh::LeanObject,
    mut v_start_1470_: *mut crate::leanh::LeanObject,
    mut v_stop_1471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1472_: u8 = 0;
    v___x_1472_ = lean_nat_dec_lt(v_start_1470_, v_stop_1471_);
    if v___x_1472_ == 0 {
        let mut v_toApplicative_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_as_1469_);
        crate::leanh::lean_dec(v_f_1467_);
        v_toApplicative_1473_ = crate::leanh::lean_ctor_get(v_inst_1466_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1473_);
        crate::leanh::lean_dec_ref(v_inst_1466_);
        v_toPure_1474_ = crate::leanh::lean_ctor_get(v_toApplicative_1473_, 1);
        crate::leanh::lean_inc(v_toPure_1474_);
        crate::leanh::lean_dec_ref(v_toApplicative_1473_);
        v___x_1475_ =
            crate::leanh::lean_apply_2(v_toPure_1474_, crate::leanh::lean_box(0), v_init_1468_);
        return v___x_1475_;
    } else {
        let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1477_: u8 = 0;
        v___x_1476_ = lean_byte_array_size(v_as_1469_);
        v___x_1477_ = lean_nat_dec_le(v_stop_1471_, v___x_1476_);
        if v___x_1477_ == 0 {
            let mut v___x_1478_: u8 = 0;
            v___x_1478_ = lean_nat_dec_lt(v_start_1470_, v___x_1476_);
            if v___x_1478_ == 0 {
                let mut v_toApplicative_1479_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v_toPure_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v_as_1469_);
                crate::leanh::lean_dec(v_f_1467_);
                v_toApplicative_1479_ = crate::leanh::lean_ctor_get(v_inst_1466_, 0);
                crate::leanh::lean_inc_ref(v_toApplicative_1479_);
                crate::leanh::lean_dec_ref(v_inst_1466_);
                v_toPure_1480_ = crate::leanh::lean_ctor_get(v_toApplicative_1479_, 1);
                crate::leanh::lean_inc(v_toPure_1480_);
                crate::leanh::lean_dec_ref(v_toApplicative_1479_);
                v___x_1481_ = crate::leanh::lean_apply_2(
                    v_toPure_1480_,
                    crate::leanh::lean_box(0),
                    v_init_1468_,
                );
                return v___x_1481_;
            } else {
                let mut v___x_1482_: usize = 0;
                let mut v___x_1483_: usize = 0;
                let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1482_ = lean_usize_of_nat(v_start_1470_);
                v___x_1483_ = lean_usize_of_nat(v___x_1476_);
                v___x_1484_ = l_ByteArray_foldlMUnsafe_fold___redArg(
                    v_inst_1466_,
                    v_f_1467_,
                    v_as_1469_,
                    v___x_1482_,
                    v___x_1483_,
                    v_init_1468_,
                );
                return v___x_1484_;
            }
        } else {
            let mut v___x_1485_: usize = 0;
            let mut v___x_1486_: usize = 0;
            let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1485_ = lean_usize_of_nat(v_start_1470_);
            v___x_1486_ = lean_usize_of_nat(v_stop_1471_);
            v___x_1487_ = l_ByteArray_foldlMUnsafe_fold___redArg(
                v_inst_1466_,
                v_f_1467_,
                v_as_1469_,
                v___x_1485_,
                v___x_1486_,
                v_init_1468_,
            );
            return v___x_1487_;
        }
    }
}
pub unsafe fn l_ByteArray_foldlMUnsafe___boxed(
    mut v_00_u03b2_1488_: *mut crate::leanh::LeanObject,
    mut v_m_1489_: *mut crate::leanh::LeanObject,
    mut v_inst_1490_: *mut crate::leanh::LeanObject,
    mut v_f_1491_: *mut crate::leanh::LeanObject,
    mut v_init_1492_: *mut crate::leanh::LeanObject,
    mut v_as_1493_: *mut crate::leanh::LeanObject,
    mut v_start_1494_: *mut crate::leanh::LeanObject,
    mut v_stop_1495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1496_ = l_ByteArray_foldlMUnsafe(
        v_00_u03b2_1488_,
        v_m_1489_,
        v_inst_1490_,
        v_f_1491_,
        v_init_1492_,
        v_as_1493_,
        v_start_1494_,
        v_stop_1495_,
    );
    crate::leanh::lean_dec(v_stop_1495_);
    crate::leanh::lean_dec(v_start_1494_);
    return v_res_1496_;
}
pub unsafe fn l_ByteArray_foldlM_loop___redArg___lam__0___boxed(
    mut v_j_1497_: *mut crate::leanh::LeanObject,
    mut v_inst_1498_: *mut crate::leanh::LeanObject,
    mut v_f_1499_: *mut crate::leanh::LeanObject,
    mut v_as_1500_: *mut crate::leanh::LeanObject,
    mut v_stop_1501_: *mut crate::leanh::LeanObject,
    mut v_n_1502_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1504_ = l_ByteArray_foldlM_loop___redArg___lam__0(
        v_j_1497_,
        v_inst_1498_,
        v_f_1499_,
        v_as_1500_,
        v_stop_1501_,
        v_n_1502_,
        v_____do__lift_1503_,
    );
    crate::leanh::lean_dec(v_n_1502_);
    crate::leanh::lean_dec(v_j_1497_);
    return v_res_1504_;
}
pub unsafe fn l_ByteArray_foldlM_loop___redArg(
    mut v_inst_1505_: *mut crate::leanh::LeanObject,
    mut v_f_1506_: *mut crate::leanh::LeanObject,
    mut v_as_1507_: *mut crate::leanh::LeanObject,
    mut v_stop_1508_: *mut crate::leanh::LeanObject,
    mut v_i_1509_: *mut crate::leanh::LeanObject,
    mut v_j_1510_: *mut crate::leanh::LeanObject,
    mut v_b_1511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1512_: u8 = 0;
    v___x_1512_ = lean_nat_dec_lt(v_j_1510_, v_stop_1508_);
    if v___x_1512_ == 0 {
        let mut v_toApplicative_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_j_1510_);
        crate::leanh::lean_dec(v_stop_1508_);
        crate::leanh::lean_dec_ref(v_as_1507_);
        crate::leanh::lean_dec(v_f_1506_);
        v_toApplicative_1513_ = crate::leanh::lean_ctor_get(v_inst_1505_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1513_);
        crate::leanh::lean_dec_ref(v_inst_1505_);
        v_toPure_1514_ = crate::leanh::lean_ctor_get(v_toApplicative_1513_, 1);
        crate::leanh::lean_inc(v_toPure_1514_);
        crate::leanh::lean_dec_ref(v_toApplicative_1513_);
        v___x_1515_ =
            crate::leanh::lean_apply_2(v_toPure_1514_, crate::leanh::lean_box(0), v_b_1511_);
        return v___x_1515_;
    } else {
        let mut v_zero_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_1517_: u8 = 0;
        v_zero_1516_ = crate::leanh::lean_unsigned_to_nat(0);
        v_isZero_1517_ = lean_nat_dec_eq(v_i_1509_, v_zero_1516_);
        if v_isZero_1517_ == 1 {
            let mut v_toApplicative_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_j_1510_);
            crate::leanh::lean_dec(v_stop_1508_);
            crate::leanh::lean_dec_ref(v_as_1507_);
            crate::leanh::lean_dec(v_f_1506_);
            v_toApplicative_1518_ = crate::leanh::lean_ctor_get(v_inst_1505_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_1518_);
            crate::leanh::lean_dec_ref(v_inst_1505_);
            v_toPure_1519_ = crate::leanh::lean_ctor_get(v_toApplicative_1518_, 1);
            crate::leanh::lean_inc(v_toPure_1519_);
            crate::leanh::lean_dec_ref(v_toApplicative_1518_);
            v___x_1520_ =
                crate::leanh::lean_apply_2(v_toPure_1519_, crate::leanh::lean_box(0), v_b_1511_);
            return v___x_1520_;
        } else {
            let mut v_toBind_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_one_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1525_: u8 = 0;
            let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toBind_1521_ = crate::leanh::lean_ctor_get(v_inst_1505_, 1);
            crate::leanh::lean_inc(v_toBind_1521_);
            v_one_1522_ = crate::leanh::lean_unsigned_to_nat(1);
            v_n_1523_ = lean_nat_sub(v_i_1509_, v_one_1522_);
            crate::leanh::lean_inc_ref(v_as_1507_);
            crate::leanh::lean_inc(v_f_1506_);
            crate::leanh::lean_inc(v_j_1510_);
            v___f_1524_ = crate::leanh::lean_alloc_closure(
                l_ByteArray_foldlM_loop___redArg___lam__0___boxed as *mut core::ffi::c_void,
                7,
                6,
            );
            crate::leanh::lean_closure_set(v___f_1524_, 0, v_j_1510_);
            crate::leanh::lean_closure_set(v___f_1524_, 1, v_inst_1505_);
            crate::leanh::lean_closure_set(v___f_1524_, 2, v_f_1506_);
            crate::leanh::lean_closure_set(v___f_1524_, 3, v_as_1507_);
            crate::leanh::lean_closure_set(v___f_1524_, 4, v_stop_1508_);
            crate::leanh::lean_closure_set(v___f_1524_, 5, v_n_1523_);
            v___x_1525_ = lean_byte_array_fget(v_as_1507_, v_j_1510_);
            crate::leanh::lean_dec(v_j_1510_);
            crate::leanh::lean_dec_ref(v_as_1507_);
            v___x_1526_ = crate::leanh::lean_box((v___x_1525_) as usize);
            v___x_1527_ = crate::leanh::lean_apply_2(v_f_1506_, v_b_1511_, v___x_1526_);
            v___x_1528_ = crate::leanh::lean_apply_4(
                v_toBind_1521_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1527_,
                v___f_1524_,
            );
            return v___x_1528_;
        }
    }
}
pub unsafe fn l_ByteArray_foldlM_loop___redArg___lam__0(
    mut v_j_1529_: *mut crate::leanh::LeanObject,
    mut v_inst_1530_: *mut crate::leanh::LeanObject,
    mut v_f_1531_: *mut crate::leanh::LeanObject,
    mut v_as_1532_: *mut crate::leanh::LeanObject,
    mut v_stop_1533_: *mut crate::leanh::LeanObject,
    mut v_n_1534_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1536_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1537_ = lean_nat_add(v_j_1529_, v___x_1536_);
    v___x_1538_ = l_ByteArray_foldlM_loop___redArg(
        v_inst_1530_,
        v_f_1531_,
        v_as_1532_,
        v_stop_1533_,
        v_n_1534_,
        v___x_1537_,
        v_____do__lift_1535_,
    );
    return v___x_1538_;
}
pub unsafe fn l_ByteArray_foldlM_loop___redArg___boxed(
    mut v_inst_1539_: *mut crate::leanh::LeanObject,
    mut v_f_1540_: *mut crate::leanh::LeanObject,
    mut v_as_1541_: *mut crate::leanh::LeanObject,
    mut v_stop_1542_: *mut crate::leanh::LeanObject,
    mut v_i_1543_: *mut crate::leanh::LeanObject,
    mut v_j_1544_: *mut crate::leanh::LeanObject,
    mut v_b_1545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1546_ = l_ByteArray_foldlM_loop___redArg(
        v_inst_1539_,
        v_f_1540_,
        v_as_1541_,
        v_stop_1542_,
        v_i_1543_,
        v_j_1544_,
        v_b_1545_,
    );
    crate::leanh::lean_dec(v_i_1543_);
    return v_res_1546_;
}
pub unsafe fn l_ByteArray_foldlM_loop(
    mut v_00_u03b2_1547_: *mut crate::leanh::LeanObject,
    mut v_m_1548_: *mut crate::leanh::LeanObject,
    mut v_inst_1549_: *mut crate::leanh::LeanObject,
    mut v_f_1550_: *mut crate::leanh::LeanObject,
    mut v_as_1551_: *mut crate::leanh::LeanObject,
    mut v_stop_1552_: *mut crate::leanh::LeanObject,
    mut v_h_1553_: *mut crate::leanh::LeanObject,
    mut v_i_1554_: *mut crate::leanh::LeanObject,
    mut v_j_1555_: *mut crate::leanh::LeanObject,
    mut v_b_1556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1557_ = l_ByteArray_foldlM_loop___redArg(
        v_inst_1549_,
        v_f_1550_,
        v_as_1551_,
        v_stop_1552_,
        v_i_1554_,
        v_j_1555_,
        v_b_1556_,
    );
    return v___x_1557_;
}
pub unsafe fn l_ByteArray_foldlM_loop___boxed(
    mut v_00_u03b2_1558_: *mut crate::leanh::LeanObject,
    mut v_m_1559_: *mut crate::leanh::LeanObject,
    mut v_inst_1560_: *mut crate::leanh::LeanObject,
    mut v_f_1561_: *mut crate::leanh::LeanObject,
    mut v_as_1562_: *mut crate::leanh::LeanObject,
    mut v_stop_1563_: *mut crate::leanh::LeanObject,
    mut v_h_1564_: *mut crate::leanh::LeanObject,
    mut v_i_1565_: *mut crate::leanh::LeanObject,
    mut v_j_1566_: *mut crate::leanh::LeanObject,
    mut v_b_1567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1568_ = l_ByteArray_foldlM_loop(
        v_00_u03b2_1558_,
        v_m_1559_,
        v_inst_1560_,
        v_f_1561_,
        v_as_1562_,
        v_stop_1563_,
        v_h_1564_,
        v_i_1565_,
        v_j_1566_,
        v_b_1567_,
    );
    crate::leanh::lean_dec(v_i_1565_);
    return v_res_1568_;
}
pub unsafe fn l_ByteArray_foldl___redArg___lam__0(
    mut v_f_1569_: *mut crate::leanh::LeanObject,
    mut v_x1_1570_: *mut crate::leanh::LeanObject,
    mut v_x2_1571_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1572_ = crate::leanh::lean_box((v_x2_1571_) as usize);
    v___x_1573_ = crate::leanh::lean_apply_2(v_f_1569_, v_x1_1570_, v___x_1572_);
    return v___x_1573_;
}
pub unsafe fn l_ByteArray_foldl___redArg___lam__0___boxed(
    mut v_f_1574_: *mut crate::leanh::LeanObject,
    mut v_x1_1575_: *mut crate::leanh::LeanObject,
    mut v_x2_1576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x2_190__boxed_1577_: u8 = 0;
    let mut v_res_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x2_190__boxed_1577_ = (crate::leanh::lean_unbox(v_x2_1576_) as u8);
    v_res_1578_ = l_ByteArray_foldl___redArg___lam__0(v_f_1574_, v_x1_1575_, v_x2_190__boxed_1577_);
    return v_res_1578_;
}
pub unsafe fn l_ByteArray_foldl___redArg(
    mut v_f_1598_: *mut crate::leanh::LeanObject,
    mut v_init_1599_: *mut crate::leanh::LeanObject,
    mut v_as_1600_: *mut crate::leanh::LeanObject,
    mut v_start_1601_: *mut crate::leanh::LeanObject,
    mut v_stop_1602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: u8 = 0;
    v___x_1603_ = l_ByteArray_foldl___redArg___closed__9;
    v___x_1604_ = lean_nat_dec_lt(v_start_1601_, v_stop_1602_);
    if v___x_1604_ == 0 {
        crate::leanh::lean_dec_ref(v_as_1600_);
        crate::leanh::lean_dec(v_f_1598_);
        return v_init_1599_;
    } else {
        let mut v___f_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1607_: u8 = 0;
        v___f_1605_ = crate::leanh::lean_alloc_closure(
            l_ByteArray_foldl___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_1605_, 0, v_f_1598_);
        v___x_1606_ = lean_byte_array_size(v_as_1600_);
        v___x_1607_ = lean_nat_dec_le(v_stop_1602_, v___x_1606_);
        if v___x_1607_ == 0 {
            let mut v___x_1608_: u8 = 0;
            v___x_1608_ = lean_nat_dec_lt(v_start_1601_, v___x_1606_);
            if v___x_1608_ == 0 {
                crate::leanh::lean_dec_ref(v___f_1605_);
                crate::leanh::lean_dec_ref(v_as_1600_);
                return v_init_1599_;
            } else {
                let mut v___x_1609_: usize = 0;
                let mut v___x_1610_: usize = 0;
                let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1609_ = lean_usize_of_nat(v_start_1601_);
                v___x_1610_ = lean_usize_of_nat(v___x_1606_);
                v___x_1611_ = l_ByteArray_foldlMUnsafe_fold___redArg(
                    v___x_1603_,
                    v___f_1605_,
                    v_as_1600_,
                    v___x_1609_,
                    v___x_1610_,
                    v_init_1599_,
                );
                return v___x_1611_;
            }
        } else {
            let mut v___x_1612_: usize = 0;
            let mut v___x_1613_: usize = 0;
            let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1612_ = lean_usize_of_nat(v_start_1601_);
            v___x_1613_ = lean_usize_of_nat(v_stop_1602_);
            v___x_1614_ = l_ByteArray_foldlMUnsafe_fold___redArg(
                v___x_1603_,
                v___f_1605_,
                v_as_1600_,
                v___x_1612_,
                v___x_1613_,
                v_init_1599_,
            );
            return v___x_1614_;
        }
    }
}
pub unsafe fn l_ByteArray_foldl___redArg___boxed(
    mut v_f_1615_: *mut crate::leanh::LeanObject,
    mut v_init_1616_: *mut crate::leanh::LeanObject,
    mut v_as_1617_: *mut crate::leanh::LeanObject,
    mut v_start_1618_: *mut crate::leanh::LeanObject,
    mut v_stop_1619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1620_ = l_ByteArray_foldl___redArg(
        v_f_1615_,
        v_init_1616_,
        v_as_1617_,
        v_start_1618_,
        v_stop_1619_,
    );
    crate::leanh::lean_dec(v_stop_1619_);
    crate::leanh::lean_dec(v_start_1618_);
    return v_res_1620_;
}
pub unsafe fn l_ByteArray_foldl(
    mut v_00_u03b2_1621_: *mut crate::leanh::LeanObject,
    mut v_f_1622_: *mut crate::leanh::LeanObject,
    mut v_init_1623_: *mut crate::leanh::LeanObject,
    mut v_as_1624_: *mut crate::leanh::LeanObject,
    mut v_start_1625_: *mut crate::leanh::LeanObject,
    mut v_stop_1626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: u8 = 0;
    v___x_1627_ = l_ByteArray_foldl___redArg___closed__9;
    v___x_1628_ = lean_nat_dec_lt(v_start_1625_, v_stop_1626_);
    if v___x_1628_ == 0 {
        crate::leanh::lean_dec_ref(v_as_1624_);
        crate::leanh::lean_dec(v_f_1622_);
        return v_init_1623_;
    } else {
        let mut v___f_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1631_: u8 = 0;
        v___f_1629_ = crate::leanh::lean_alloc_closure(
            l_ByteArray_foldl___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_1629_, 0, v_f_1622_);
        v___x_1630_ = lean_byte_array_size(v_as_1624_);
        v___x_1631_ = lean_nat_dec_le(v_stop_1626_, v___x_1630_);
        if v___x_1631_ == 0 {
            let mut v___x_1632_: u8 = 0;
            v___x_1632_ = lean_nat_dec_lt(v_start_1625_, v___x_1630_);
            if v___x_1632_ == 0 {
                crate::leanh::lean_dec_ref(v___f_1629_);
                crate::leanh::lean_dec_ref(v_as_1624_);
                return v_init_1623_;
            } else {
                let mut v___x_1633_: usize = 0;
                let mut v___x_1634_: usize = 0;
                let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1633_ = lean_usize_of_nat(v_start_1625_);
                v___x_1634_ = lean_usize_of_nat(v___x_1630_);
                v___x_1635_ = l_ByteArray_foldlMUnsafe_fold___redArg(
                    v___x_1627_,
                    v___f_1629_,
                    v_as_1624_,
                    v___x_1633_,
                    v___x_1634_,
                    v_init_1623_,
                );
                return v___x_1635_;
            }
        } else {
            let mut v___x_1636_: usize = 0;
            let mut v___x_1637_: usize = 0;
            let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1636_ = lean_usize_of_nat(v_start_1625_);
            v___x_1637_ = lean_usize_of_nat(v_stop_1626_);
            v___x_1638_ = l_ByteArray_foldlMUnsafe_fold___redArg(
                v___x_1627_,
                v___f_1629_,
                v_as_1624_,
                v___x_1636_,
                v___x_1637_,
                v_init_1623_,
            );
            return v___x_1638_;
        }
    }
}
pub unsafe fn l_ByteArray_foldl___boxed(
    mut v_00_u03b2_1639_: *mut crate::leanh::LeanObject,
    mut v_f_1640_: *mut crate::leanh::LeanObject,
    mut v_init_1641_: *mut crate::leanh::LeanObject,
    mut v_as_1642_: *mut crate::leanh::LeanObject,
    mut v_start_1643_: *mut crate::leanh::LeanObject,
    mut v_stop_1644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1645_ = l_ByteArray_foldl(
        v_00_u03b2_1639_,
        v_f_1640_,
        v_init_1641_,
        v_as_1642_,
        v_start_1643_,
        v_stop_1644_,
    );
    crate::leanh::lean_dec(v_stop_1644_);
    crate::leanh::lean_dec(v_start_1643_);
    return v_res_1645_;
}
pub unsafe fn _init_l_ByteArray_instInhabitedIterator_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1646_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1647_ = l_ByteArray_empty;
    v___x_1648_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1648_, 0, v___x_1647_);
    crate::leanh::lean_ctor_set(v___x_1648_, 1, v___x_1646_);
    return v___x_1648_;
}
pub unsafe fn _init_l_ByteArray_instInhabitedIterator_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1649_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_ByteArray_instInhabitedIterator_default___closed__0),
        core::ptr::addr_of_mut!(l_ByteArray_instInhabitedIterator_default___closed__0_once),
        _init_l_ByteArray_instInhabitedIterator_default___closed__0,
    );
    return v___x_1649_;
}
pub unsafe fn _init_l_ByteArray_instInhabitedIterator() -> *mut crate::leanh::LeanObject {
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1650_ = l_ByteArray_instInhabitedIterator_default;
    return v___x_1650_;
}
pub unsafe fn l_ByteArray_mkIterator(
    mut v_arr_1651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1652_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1653_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1653_, 0, v_arr_1651_);
    crate::leanh::lean_ctor_set(v___x_1653_, 1, v___x_1652_);
    return v___x_1653_;
}
pub unsafe fn l_ByteArray_iter(
    mut v_arr_1654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1655_ = l_ByteArray_mkIterator(v_arr_1654_);
    return v___x_1655_;
}
pub unsafe fn l_ByteArray_instSizeOfIterator___lam__0(
    mut v_i_1656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_array_1657_ = crate::leanh::lean_ctor_get(v_i_1656_, 0);
    v_idx_1658_ = crate::leanh::lean_ctor_get(v_i_1656_, 1);
    v___x_1659_ = lean_byte_array_size(v_array_1657_);
    v___x_1660_ = lean_nat_sub(v___x_1659_, v_idx_1658_);
    return v___x_1660_;
}
pub unsafe fn l_ByteArray_instSizeOfIterator___lam__0___boxed(
    mut v_i_1661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1662_ = l_ByteArray_instSizeOfIterator___lam__0(v_i_1661_);
    crate::leanh::lean_dec_ref(v_i_1661_);
    return v_res_1662_;
}
pub unsafe fn l_ByteArray_Iterator_remainingBytes(
    mut v_x_1665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_array_1666_ = crate::leanh::lean_ctor_get(v_x_1665_, 0);
    v_idx_1667_ = crate::leanh::lean_ctor_get(v_x_1665_, 1);
    v___x_1668_ = lean_byte_array_size(v_array_1666_);
    v___x_1669_ = lean_nat_sub(v___x_1668_, v_idx_1667_);
    return v___x_1669_;
}
pub unsafe fn l_ByteArray_Iterator_remainingBytes___boxed(
    mut v_x_1670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1671_ = l_ByteArray_Iterator_remainingBytes(v_x_1670_);
    crate::leanh::lean_dec_ref(v_x_1670_);
    return v_res_1671_;
}
pub unsafe fn l_ByteArray_Iterator_pos(
    mut v_self_1672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_idx_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_idx_1673_ = crate::leanh::lean_ctor_get(v_self_1672_, 1);
    crate::leanh::lean_inc(v_idx_1673_);
    return v_idx_1673_;
}
pub unsafe fn l_ByteArray_Iterator_pos___boxed(
    mut v_self_1674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1675_ = l_ByteArray_Iterator_pos(v_self_1674_);
    crate::leanh::lean_dec_ref(v_self_1674_);
    return v_res_1675_;
}
pub unsafe fn l_ByteArray_Iterator_atEnd(mut v_x_1676_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_array_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: u8 = 0;
    v_array_1677_ = crate::leanh::lean_ctor_get(v_x_1676_, 0);
    v_idx_1678_ = crate::leanh::lean_ctor_get(v_x_1676_, 1);
    v___x_1679_ = lean_byte_array_size(v_array_1677_);
    v___x_1680_ = lean_nat_dec_le(v___x_1679_, v_idx_1678_);
    return v___x_1680_;
}
pub unsafe fn l_ByteArray_Iterator_atEnd___boxed(
    mut v_x_1681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1682_: u8 = 0;
    let mut v_r_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1682_ = l_ByteArray_Iterator_atEnd(v_x_1681_);
    crate::leanh::lean_dec_ref(v_x_1681_);
    v_r_1683_ = crate::leanh::lean_box((v_res_1682_) as usize);
    return v_r_1683_;
}
pub unsafe fn _init_l_ByteArray_Iterator_curr___closed__0() -> u8 {
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: u8 = 0;
    v___x_1684_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1685_ = lean_uint8_of_nat(v___x_1684_);
    return v___x_1685_;
}
pub unsafe fn l_ByteArray_Iterator_curr(mut v_x_1686_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_array_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: u8 = 0;
    v_array_1687_ = crate::leanh::lean_ctor_get(v_x_1686_, 0);
    v_idx_1688_ = crate::leanh::lean_ctor_get(v_x_1686_, 1);
    v___x_1689_ = lean_byte_array_size(v_array_1687_);
    v___x_1690_ = lean_nat_dec_lt(v_idx_1688_, v___x_1689_);
    if v___x_1690_ == 0 {
        let mut v___x_1691_: u8 = 0;
        v___x_1691_ = crate::leanh::lean_uint8_once(
            core::ptr::addr_of_mut!(l_ByteArray_Iterator_curr___closed__0),
            core::ptr::addr_of_mut!(l_ByteArray_Iterator_curr___closed__0_once),
            _init_l_ByteArray_Iterator_curr___closed__0,
        );
        return v___x_1691_;
    } else {
        let mut v___x_1692_: u8 = 0;
        v___x_1692_ = lean_byte_array_fget(v_array_1687_, v_idx_1688_);
        return v___x_1692_;
    }
}
pub unsafe fn l_ByteArray_Iterator_curr___boxed(
    mut v_x_1693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1694_: u8 = 0;
    let mut v_r_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1694_ = l_ByteArray_Iterator_curr(v_x_1693_);
    crate::leanh::lean_dec_ref(v_x_1693_);
    v_r_1695_ = crate::leanh::lean_box((v_res_1694_) as usize);
    return v_r_1695_;
}
pub unsafe fn l_ByteArray_Iterator_next(
    mut v_x_1696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1701_: u8 = 0;
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1707_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1697_ = crate::leanh::lean_ctor_get(v_x_1696_, 0);
                v_idx_1698_ = crate::leanh::lean_ctor_get(v_x_1696_, 1);
                v_isSharedCheck_1707_ = (!crate::leanh::lean_is_exclusive(v_x_1696_)) as u8;
                if v_isSharedCheck_1707_ == 0 {
                    v___x_1700_ = v_x_1696_;
                    v_isShared_1701_ = v_isSharedCheck_1707_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_1698_);
                    crate::leanh::lean_inc(v_array_1697_);
                    crate::leanh::lean_dec(v_x_1696_);
                    v___x_1700_ = crate::leanh::lean_box(0);
                    v_isShared_1701_ = v_isSharedCheck_1707_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1702_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1703_ = lean_nat_add(v_idx_1698_, v___x_1702_);
                crate::leanh::lean_dec(v_idx_1698_);
                if v_isShared_1701_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1700_, 1, v___x_1703_);
                    v___x_1705_ = v___x_1700_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1706_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_array_1697_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1706_, 1, v___x_1703_);
                    v___x_1705_ = v_reuseFailAlloc_1706_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1705_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_Iterator_prev(
    mut v_x_1708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1713_: u8 = 0;
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1719_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1709_ = crate::leanh::lean_ctor_get(v_x_1708_, 0);
                v_idx_1710_ = crate::leanh::lean_ctor_get(v_x_1708_, 1);
                v_isSharedCheck_1719_ = (!crate::leanh::lean_is_exclusive(v_x_1708_)) as u8;
                if v_isSharedCheck_1719_ == 0 {
                    v___x_1712_ = v_x_1708_;
                    v_isShared_1713_ = v_isSharedCheck_1719_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_1710_);
                    crate::leanh::lean_inc(v_array_1709_);
                    crate::leanh::lean_dec(v_x_1708_);
                    v___x_1712_ = crate::leanh::lean_box(0);
                    v_isShared_1713_ = v_isSharedCheck_1719_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1714_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1715_ = lean_nat_sub(v_idx_1710_, v___x_1714_);
                crate::leanh::lean_dec(v_idx_1710_);
                if v_isShared_1713_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1712_, 1, v___x_1715_);
                    v___x_1717_ = v___x_1712_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1718_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_array_1709_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1718_, 1, v___x_1715_);
                    v___x_1717_ = v_reuseFailAlloc_1718_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1717_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_Iterator_hasNext(mut v_x_1720_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_array_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: u8 = 0;
    v_array_1721_ = crate::leanh::lean_ctor_get(v_x_1720_, 0);
    v_idx_1722_ = crate::leanh::lean_ctor_get(v_x_1720_, 1);
    v___x_1723_ = lean_byte_array_size(v_array_1721_);
    v___x_1724_ = lean_nat_dec_lt(v_idx_1722_, v___x_1723_);
    return v___x_1724_;
}
pub unsafe fn l_ByteArray_Iterator_hasNext___boxed(
    mut v_x_1725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1726_: u8 = 0;
    let mut v_r_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1726_ = l_ByteArray_Iterator_hasNext(v_x_1725_);
    crate::leanh::lean_dec_ref(v_x_1725_);
    v_r_1727_ = crate::leanh::lean_box((v_res_1726_) as usize);
    return v_r_1727_;
}
pub unsafe fn l___private_Init_Data_ByteArray_Basic_0__ByteArray_Iterator_remainingBytes_match__1_splitter___redArg(
    mut v_x_1728_: *mut crate::leanh::LeanObject,
    mut v_h__1_1729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_array_1730_ = crate::leanh::lean_ctor_get(v_x_1728_, 0);
    crate::leanh::lean_inc_ref(v_array_1730_);
    v_idx_1731_ = crate::leanh::lean_ctor_get(v_x_1728_, 1);
    crate::leanh::lean_inc(v_idx_1731_);
    crate::leanh::lean_dec_ref(v_x_1728_);
    v___x_1732_ = crate::leanh::lean_apply_2(v_h__1_1729_, v_array_1730_, v_idx_1731_);
    return v___x_1732_;
}
pub unsafe fn l___private_Init_Data_ByteArray_Basic_0__ByteArray_Iterator_remainingBytes_match__1_splitter(
    mut v_motive_1733_: *mut crate::leanh::LeanObject,
    mut v_x_1734_: *mut crate::leanh::LeanObject,
    mut v_h__1_1735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_array_1736_ = crate::leanh::lean_ctor_get(v_x_1734_, 0);
    crate::leanh::lean_inc_ref(v_array_1736_);
    v_idx_1737_ = crate::leanh::lean_ctor_get(v_x_1734_, 1);
    crate::leanh::lean_inc(v_idx_1737_);
    crate::leanh::lean_dec_ref(v_x_1734_);
    v___x_1738_ = crate::leanh::lean_apply_2(v_h__1_1735_, v_array_1736_, v_idx_1737_);
    return v___x_1738_;
}
pub unsafe fn l_ByteArray_Iterator_curr_x27___redArg(
    mut v_it_1739_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_array_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: u8 = 0;
    v_array_1740_ = crate::leanh::lean_ctor_get(v_it_1739_, 0);
    v_idx_1741_ = crate::leanh::lean_ctor_get(v_it_1739_, 1);
    v___x_1742_ = lean_byte_array_fget(v_array_1740_, v_idx_1741_);
    return v___x_1742_;
}
pub unsafe fn l_ByteArray_Iterator_curr_x27___redArg___boxed(
    mut v_it_1743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1744_: u8 = 0;
    let mut v_r_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1744_ = l_ByteArray_Iterator_curr_x27___redArg(v_it_1743_);
    crate::leanh::lean_dec_ref(v_it_1743_);
    v_r_1745_ = crate::leanh::lean_box((v_res_1744_) as usize);
    return v_r_1745_;
}
pub unsafe fn l_ByteArray_Iterator_curr_x27(
    mut v_it_1746_: *mut crate::leanh::LeanObject,
    mut v_h_1747_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_array_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: u8 = 0;
    v_array_1748_ = crate::leanh::lean_ctor_get(v_it_1746_, 0);
    v_idx_1749_ = crate::leanh::lean_ctor_get(v_it_1746_, 1);
    v___x_1750_ = lean_byte_array_fget(v_array_1748_, v_idx_1749_);
    return v___x_1750_;
}
pub unsafe fn l_ByteArray_Iterator_curr_x27___boxed(
    mut v_it_1751_: *mut crate::leanh::LeanObject,
    mut v_h_1752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1753_: u8 = 0;
    let mut v_r_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1753_ = l_ByteArray_Iterator_curr_x27(v_it_1751_, v_h_1752_);
    crate::leanh::lean_dec_ref(v_it_1751_);
    v_r_1754_ = crate::leanh::lean_box((v_res_1753_) as usize);
    return v_r_1754_;
}
pub unsafe fn l_ByteArray_Iterator_next_x27___redArg(
    mut v_it_1755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1760_: u8 = 0;
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1766_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1756_ = crate::leanh::lean_ctor_get(v_it_1755_, 0);
                v_idx_1757_ = crate::leanh::lean_ctor_get(v_it_1755_, 1);
                v_isSharedCheck_1766_ = (!crate::leanh::lean_is_exclusive(v_it_1755_)) as u8;
                if v_isSharedCheck_1766_ == 0 {
                    v___x_1759_ = v_it_1755_;
                    v_isShared_1760_ = v_isSharedCheck_1766_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_1757_);
                    crate::leanh::lean_inc(v_array_1756_);
                    crate::leanh::lean_dec(v_it_1755_);
                    v___x_1759_ = crate::leanh::lean_box(0);
                    v_isShared_1760_ = v_isSharedCheck_1766_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1761_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1762_ = lean_nat_add(v_idx_1757_, v___x_1761_);
                crate::leanh::lean_dec(v_idx_1757_);
                if v_isShared_1760_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1759_, 1, v___x_1762_);
                    v___x_1764_ = v___x_1759_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1765_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_array_1756_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1765_, 1, v___x_1762_);
                    v___x_1764_ = v_reuseFailAlloc_1765_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1764_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_Iterator_next_x27(
    mut v_it_1767_: *mut crate::leanh::LeanObject,
    mut v___h_1768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1773_: u8 = 0;
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1769_ = crate::leanh::lean_ctor_get(v_it_1767_, 0);
                v_idx_1770_ = crate::leanh::lean_ctor_get(v_it_1767_, 1);
                v_isSharedCheck_1779_ = (!crate::leanh::lean_is_exclusive(v_it_1767_)) as u8;
                if v_isSharedCheck_1779_ == 0 {
                    v___x_1772_ = v_it_1767_;
                    v_isShared_1773_ = v_isSharedCheck_1779_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_1770_);
                    crate::leanh::lean_inc(v_array_1769_);
                    crate::leanh::lean_dec(v_it_1767_);
                    v___x_1772_ = crate::leanh::lean_box(0);
                    v_isShared_1773_ = v_isSharedCheck_1779_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1774_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1775_ = lean_nat_add(v_idx_1770_, v___x_1774_);
                crate::leanh::lean_dec(v_idx_1770_);
                if v_isShared_1773_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1772_, 1, v___x_1775_);
                    v___x_1777_ = v___x_1772_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1778_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_array_1769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1778_, 1, v___x_1775_);
                    v___x_1777_ = v_reuseFailAlloc_1778_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1777_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_Iterator_hasPrev(mut v_x_1780_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_idx_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: u8 = 0;
    v_idx_1781_ = crate::leanh::lean_ctor_get(v_x_1780_, 1);
    v___x_1782_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1783_ = lean_nat_dec_lt(v___x_1782_, v_idx_1781_);
    return v___x_1783_;
}
pub unsafe fn l_ByteArray_Iterator_hasPrev___boxed(
    mut v_x_1784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1785_: u8 = 0;
    let mut v_r_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1785_ = l_ByteArray_Iterator_hasPrev(v_x_1784_);
    crate::leanh::lean_dec_ref(v_x_1784_);
    v_r_1786_ = crate::leanh::lean_box((v_res_1785_) as usize);
    return v_r_1786_;
}
pub unsafe fn l_ByteArray_Iterator_toEnd(
    mut v_x_1787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1791_: u8 = 0;
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1796_: u8 = 0;
    let mut v_unused_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1788_ = crate::leanh::lean_ctor_get(v_x_1787_, 0);
                v_isSharedCheck_1796_ = (!crate::leanh::lean_is_exclusive(v_x_1787_)) as u8;
                if v_isSharedCheck_1796_ == 0 {
                    v_unused_1797_ = crate::leanh::lean_ctor_get(v_x_1787_, 1);
                    crate::leanh::lean_dec(v_unused_1797_);
                    v___x_1790_ = v_x_1787_;
                    v_isShared_1791_ = v_isSharedCheck_1796_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_array_1788_);
                    crate::leanh::lean_dec(v_x_1787_);
                    v___x_1790_ = crate::leanh::lean_box(0);
                    v_isShared_1791_ = v_isSharedCheck_1796_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1792_ = lean_byte_array_size(v_array_1788_);
                if v_isShared_1791_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1790_, 1, v___x_1792_);
                    v___x_1794_ = v___x_1790_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1795_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_array_1788_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1795_, 1, v___x_1792_);
                    v___x_1794_ = v_reuseFailAlloc_1795_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1794_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_Iterator_forward(
    mut v_x_1798_: *mut crate::leanh::LeanObject,
    mut v_x_1799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1804_: u8 = 0;
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1809_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1800_ = crate::leanh::lean_ctor_get(v_x_1798_, 0);
                v_idx_1801_ = crate::leanh::lean_ctor_get(v_x_1798_, 1);
                v_isSharedCheck_1809_ = (!crate::leanh::lean_is_exclusive(v_x_1798_)) as u8;
                if v_isSharedCheck_1809_ == 0 {
                    v___x_1803_ = v_x_1798_;
                    v_isShared_1804_ = v_isSharedCheck_1809_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_1801_);
                    crate::leanh::lean_inc(v_array_1800_);
                    crate::leanh::lean_dec(v_x_1798_);
                    v___x_1803_ = crate::leanh::lean_box(0);
                    v_isShared_1804_ = v_isSharedCheck_1809_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1805_ = lean_nat_add(v_idx_1801_, v_x_1799_);
                crate::leanh::lean_dec(v_idx_1801_);
                if v_isShared_1804_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1803_, 1, v___x_1805_);
                    v___x_1807_ = v___x_1803_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1808_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_array_1800_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 1, v___x_1805_);
                    v___x_1807_ = v_reuseFailAlloc_1808_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1807_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_Iterator_forward___boxed(
    mut v_x_1810_: *mut crate::leanh::LeanObject,
    mut v_x_1811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1812_ = l_ByteArray_Iterator_forward(v_x_1810_, v_x_1811_);
    crate::leanh::lean_dec(v_x_1811_);
    return v_res_1812_;
}
pub unsafe fn l_ByteArray_Iterator_nextn(
    mut v_a_1813_: *mut crate::leanh::LeanObject,
    mut v_a_1814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1819_: u8 = 0;
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1824_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1815_ = crate::leanh::lean_ctor_get(v_a_1813_, 0);
                v_idx_1816_ = crate::leanh::lean_ctor_get(v_a_1813_, 1);
                v_isSharedCheck_1824_ = (!crate::leanh::lean_is_exclusive(v_a_1813_)) as u8;
                if v_isSharedCheck_1824_ == 0 {
                    v___x_1818_ = v_a_1813_;
                    v_isShared_1819_ = v_isSharedCheck_1824_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_1816_);
                    crate::leanh::lean_inc(v_array_1815_);
                    crate::leanh::lean_dec(v_a_1813_);
                    v___x_1818_ = crate::leanh::lean_box(0);
                    v_isShared_1819_ = v_isSharedCheck_1824_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1820_ = lean_nat_add(v_idx_1816_, v_a_1814_);
                crate::leanh::lean_dec(v_idx_1816_);
                if v_isShared_1819_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1818_, 1, v___x_1820_);
                    v___x_1822_ = v___x_1818_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1823_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_array_1815_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1823_, 1, v___x_1820_);
                    v___x_1822_ = v_reuseFailAlloc_1823_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1822_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_Iterator_nextn___boxed(
    mut v_a_1825_: *mut crate::leanh::LeanObject,
    mut v_a_1826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1827_ = l_ByteArray_Iterator_nextn(v_a_1825_, v_a_1826_);
    crate::leanh::lean_dec(v_a_1826_);
    return v_res_1827_;
}
pub unsafe fn l_ByteArray_Iterator_prevn(
    mut v_x_1828_: *mut crate::leanh::LeanObject,
    mut v_x_1829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1834_: u8 = 0;
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1839_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1830_ = crate::leanh::lean_ctor_get(v_x_1828_, 0);
                v_idx_1831_ = crate::leanh::lean_ctor_get(v_x_1828_, 1);
                v_isSharedCheck_1839_ = (!crate::leanh::lean_is_exclusive(v_x_1828_)) as u8;
                if v_isSharedCheck_1839_ == 0 {
                    v___x_1833_ = v_x_1828_;
                    v_isShared_1834_ = v_isSharedCheck_1839_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_1831_);
                    crate::leanh::lean_inc(v_array_1830_);
                    crate::leanh::lean_dec(v_x_1828_);
                    v___x_1833_ = crate::leanh::lean_box(0);
                    v_isShared_1834_ = v_isSharedCheck_1839_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1835_ = lean_nat_sub(v_idx_1831_, v_x_1829_);
                crate::leanh::lean_dec(v_idx_1831_);
                if v_isShared_1834_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1833_, 1, v___x_1835_);
                    v___x_1837_ = v___x_1833_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1838_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_array_1830_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1838_, 1, v___x_1835_);
                    v___x_1837_ = v_reuseFailAlloc_1838_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1837_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ByteArray_Iterator_prevn___boxed(
    mut v_x_1840_: *mut crate::leanh::LeanObject,
    mut v_x_1841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1842_ = l_ByteArray_Iterator_prevn(v_x_1840_, v_x_1841_);
    crate::leanh::lean_dec(v_x_1841_);
    return v_res_1842_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_ByteArray_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_UInt_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_DecidableEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_ByteArray_instInhabited = _init_l_ByteArray_instInhabited();
    crate::leanh::lean_mark_persistent(l_ByteArray_instInhabited);
    l_ByteArray_instEmptyCollection = _init_l_ByteArray_instEmptyCollection();
    crate::leanh::lean_mark_persistent(l_ByteArray_instEmptyCollection);
    l_ByteArray_instInhabitedIterator_default = _init_l_ByteArray_instInhabitedIterator_default();
    crate::leanh::lean_mark_persistent(l_ByteArray_instInhabitedIterator_default);
    l_ByteArray_instInhabitedIterator = _init_l_ByteArray_instInhabitedIterator();
    crate::leanh::lean_mark_persistent(l_ByteArray_instInhabitedIterator);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_ByteArray_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_ByteArray_uget___auto__1 = _init_l_ByteArray_uget___auto__1();
    crate::leanh::lean_mark_persistent(l_ByteArray_uget___auto__1);
    l_ByteArray_get___auto__1 = _init_l_ByteArray_get___auto__1();
    crate::leanh::lean_mark_persistent(l_ByteArray_get___auto__1);
    l_ByteArray_set___auto__1 = _init_l_ByteArray_set___auto__1();
    crate::leanh::lean_mark_persistent(l_ByteArray_set___auto__1);
    l_ByteArray_uset___auto__1 = _init_l_ByteArray_uset___auto__1();
    crate::leanh::lean_mark_persistent(l_ByteArray_uset___auto__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_ByteArray_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_UInt_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_DecidableEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ByteArray_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_ByteArray_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_ByteArray_Basic(builtin);
}

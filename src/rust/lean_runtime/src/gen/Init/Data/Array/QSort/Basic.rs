// Lean compiler output
// Module: Init.Data.Array.QSort.Basic
// Imports: Init.Data.Vector.Basic Init.Data.Ord.Basic Init.Omega
use crate::r#gen::Init::Data::Ord::Basic::{
    initialize_Init_Data_Ord_Basic, runtime_initialize_Init_Data_Ord_Basic,
};
use crate::r#gen::Init::Data::Vector::Basic::{
    initialize_Init_Data_Vector_Basic, runtime_initialize_Init_Data_Vector_Basic,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_fswap;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_string_utf8_byte_size,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_3, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_mark_persistent, lean_obj_once, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Array_qpartition___auto__1___closed__0_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Array_qpartition___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value) as *mut LeanObject;
pub static l_Array_qpartition___auto__1___closed__1_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Array_qpartition___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value) as *mut LeanObject;
pub static l_Array_qpartition___auto__1___closed__2_value: LeanStringObject<7> = LeanStringObject {
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
static mut l_Array_qpartition___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__2_value) as *mut LeanObject;
pub static l_Array_qpartition___auto__1___closed__3_value: LeanStringObject<10> =
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
static mut l_Array_qpartition___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__3_value) as *mut LeanObject;
static l_Array_qpartition___auto__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Array_qpartition___auto__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__4_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Array_qpartition___auto__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__4_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Array_qpartition___auto__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__4_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__3_value) as *mut LeanObject,
        8504843326314613972 as *mut LeanObject,
    ],
};
static mut l_Array_qpartition___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__4_value) as *mut LeanObject;
pub static l_Array_qpartition___auto__1___closed__5_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Array_qpartition___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__5_value) as *mut LeanObject;
pub static l_Array_qpartition___auto__1___closed__6_value: LeanStringObject<19> =
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
static mut l_Array_qpartition___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__6_value) as *mut LeanObject;
static l_Array_qpartition___auto__1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Array_qpartition___auto__1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__7_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Array_qpartition___auto__1___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__7_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Array_qpartition___auto__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__7_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__6_value) as *mut LeanObject,
        17228437386856258271 as *mut LeanObject,
    ],
};
static mut l_Array_qpartition___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__7_value) as *mut LeanObject;
pub static l_Array_qpartition___auto__1___closed__8_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Array_qpartition___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__8_value) as *mut LeanObject;
pub static l_Array_qpartition___auto__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__8_value) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l_Array_qpartition___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__9_value) as *mut LeanObject;
pub static l_Array_qpartition___auto__1___closed__10_value: LeanStringObject<6> =
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
        m_data: [111, 109, 101, 103, 97, 0],
    };
static mut l_Array_qpartition___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__10_value) as *mut LeanObject;
static l_Array_qpartition___auto__1___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Array_qpartition___auto__1___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__11_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Array_qpartition___auto__1___closed__11_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__11_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Array_qpartition___auto__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__11_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__10_value) as *mut LeanObject,
        14893461734720614794 as *mut LeanObject,
    ],
};
static mut l_Array_qpartition___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__11_value) as *mut LeanObject;
static mut l_Array_qpartition___auto__1___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qpartition___auto__1___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qpartition___auto__1___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_qpartition___auto__1___closed__14_value: LeanStringObject<10> =
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
static mut l_Array_qpartition___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__14_value) as *mut LeanObject;
static l_Array_qpartition___auto__1___closed__15_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Array_qpartition___auto__1___closed__15_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__15_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Array_qpartition___auto__1___closed__15_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__15_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Array_qpartition___auto__1___closed__15_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__15_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__14_value) as *mut LeanObject,
        3488656302031949961 as *mut LeanObject,
    ],
};
static mut l_Array_qpartition___auto__1___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__15_value) as *mut LeanObject;
pub static l_Array_qpartition___auto__1___closed__16_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__9_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Array_qpartition___auto__1___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__16_value) as *mut LeanObject;
static mut l_Array_qpartition___auto__1___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qpartition___auto__1___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qpartition___auto__1___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qpartition___auto__1___closed__19: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qpartition___auto__1___closed__20: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qpartition___auto__1___closed__21: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qpartition___auto__1___closed__22: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qpartition___auto__1___closed__23: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qpartition___auto__1___closed__24: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qpartition___auto__1___closed__25: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qpartition___auto__1___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qpartition___auto__1___closed__26: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Array_qpartition___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Array_qpartition___auto__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Array_qpartition___auto__5: *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__2:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__4:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__6:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Array_qsort___auto__1___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Array_qsort___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__0_value) as *mut LeanObject;
static l_Array_qsort___auto__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Array_qsort___auto__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_qsort___auto__1___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Array_qsort___auto__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_qsort___auto__1___closed__1_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_Array_qsort___auto__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_qsort___auto__1___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_qsort___auto__1___closed__0_value) as *mut LeanObject,
        14997215300048349804 as *mut LeanObject,
    ],
};
static mut l_Array_qsort___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__1_value) as *mut LeanObject;
static mut l_Array_qsort___auto__1___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_qsort___auto__1___closed__4_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Array_qsort___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__4_value) as *mut LeanObject;
pub static l_Array_qsort___auto__1___closed__5_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Array_qsort___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__5_value) as *mut LeanObject;
static l_Array_qsort___auto__1___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Array_qsort___auto__1___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_qsort___auto__1___closed__6_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Array_qsort___auto__1___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_qsort___auto__1___closed__6_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_qsort___auto__1___closed__4_value) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Array_qsort___auto__1___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_qsort___auto__1___closed__6_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_qsort___auto__1___closed__5_value) as *mut LeanObject,
        7932075773091973500 as *mut LeanObject,
    ],
};
static mut l_Array_qsort___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__6_value) as *mut LeanObject;
pub static l_Array_qsort___auto__1___closed__7_value: LeanStringObject<15> = LeanStringObject {
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
static mut l_Array_qsort___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__7_value) as *mut LeanObject;
static l_Array_qsort___auto__1___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Array_qsort___auto__1___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_qsort___auto__1___closed__8_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Array_qsort___auto__1___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_qsort___auto__1___closed__8_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_qsort___auto__1___closed__4_value) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Array_qsort___auto__1___closed__8_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_qsort___auto__1___closed__8_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_qsort___auto__1___closed__7_value) as *mut LeanObject,
        7306243862518720553 as *mut LeanObject,
    ],
};
static mut l_Array_qsort___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__8_value) as *mut LeanObject;
pub static l_Array_qsort___auto__1___closed__9_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Array_qsort___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__9_value) as *mut LeanObject;
static mut l_Array_qsort___auto__1___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_qsort___auto__1___closed__12_value: LeanStringObject<12> = LeanStringObject {
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
static mut l_Array_qsort___auto__1___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__12_value) as *mut LeanObject;
pub static l_Array_qsort___auto__1___closed__13_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Array_qsort___auto__1___closed__12_value) as *mut LeanObject,
        9871775667037945883 as *mut LeanObject,
    ],
};
static mut l_Array_qsort___auto__1___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__13_value) as *mut LeanObject;
pub static l_Array_qsort___auto__1___closed__14_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Array_qsort___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__14_value) as *mut LeanObject;
static mut l_Array_qsort___auto__1___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__16: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__19: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__20: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__21: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__22: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_qsort___auto__1___closed__23_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Array_qsort___auto__1___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__23_value) as *mut LeanObject;
pub static l_Array_qsort___auto__1___closed__24_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Array_qsort___auto__1___closed__23_value) as *mut LeanObject,
        6883052497475924672 as *mut LeanObject,
    ],
};
static mut l_Array_qsort___auto__1___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__24_value) as *mut LeanObject;
pub static l_Array_qsort___auto__1___closed__25_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Array_qsort___auto__1___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__25_value) as *mut LeanObject;
static l_Array_qsort___auto__1___closed__26_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Array_qsort___auto__1___closed__26_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_qsort___auto__1___closed__26_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_qpartition___auto__1___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Array_qsort___auto__1___closed__26_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_qsort___auto__1___closed__26_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_qsort___auto__1___closed__4_value) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Array_qsort___auto__1___closed__26_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_qsort___auto__1___closed__26_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_qsort___auto__1___closed__25_value) as *mut LeanObject,
        6167508377434939095 as *mut LeanObject,
    ],
};
static mut l_Array_qsort___auto__1___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__26_value) as *mut LeanObject;
pub static l_Array_qsort___auto__1___closed__27_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Array_qsort___auto__1___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__27_value) as *mut LeanObject;
static mut l_Array_qsort___auto__1___closed__28_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__28: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__29_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__29: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__30_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__30: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__31_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__31: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__32_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__32: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_qsort___auto__1___closed__33_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Array_qsort___auto__1___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__33_value) as *mut LeanObject;
static mut l_Array_qsort___auto__1___closed__34_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__34: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__35_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__35: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__36_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__36: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__37_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__37: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__38_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__38: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_qsort___auto__1___closed__39_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Array_qsort___auto__1___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l_Array_qsort___auto__1___closed__39_value) as *mut LeanObject;
static mut l_Array_qsort___auto__1___closed__40_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__40: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__41_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__41: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__42_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__42: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__43_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__43: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__44_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__44: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__45_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__45: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__46_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__46: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__47_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__47: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__48_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__48: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__49_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__49: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_qsort___auto__1___closed__50_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_qsort___auto__1___closed__50: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Array_qsort___auto__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__2: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__4: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__6: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__12() -> *mut LeanObject {
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    v___x_547_ = l_Array_qpartition___auto__1___closed__10;
    v___x_548_ = l_Lean_mkAtom(v___x_547_);
    return v___x_548_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__13() -> *mut LeanObject {
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    v___x_549_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__12_once),
        _init_l_Array_qpartition___auto__1___closed__12,
    );
    v___x_550_ = l_Array_qpartition___auto__1___closed__5;
    v___x_551_ = lean_array_push(v___x_550_, v___x_549_);
    return v___x_551_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__17() -> *mut LeanObject {
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    v___x_562_ = l_Array_qpartition___auto__1___closed__16;
    v___x_563_ = l_Array_qpartition___auto__1___closed__5;
    v___x_564_ = lean_array_push(v___x_563_, v___x_562_);
    return v___x_564_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__18() -> *mut LeanObject {
    let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    v___x_565_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__17_once),
        _init_l_Array_qpartition___auto__1___closed__17,
    );
    v___x_566_ = l_Array_qpartition___auto__1___closed__15;
    v___x_567_ = lean_box(2);
    v___x_568_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_568_, 0, v___x_567_);
    lean_ctor_set(v___x_568_, 1, v___x_566_);
    lean_ctor_set(v___x_568_, 2, v___x_565_);
    return v___x_568_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__19() -> *mut LeanObject {
    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    v___x_569_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__18_once),
        _init_l_Array_qpartition___auto__1___closed__18,
    );
    v___x_570_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__13_once),
        _init_l_Array_qpartition___auto__1___closed__13,
    );
    v___x_571_ = lean_array_push(v___x_570_, v___x_569_);
    return v___x_571_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__20() -> *mut LeanObject {
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    v___x_572_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__19_once),
        _init_l_Array_qpartition___auto__1___closed__19,
    );
    v___x_573_ = l_Array_qpartition___auto__1___closed__11;
    v___x_574_ = lean_box(2);
    v___x_575_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_575_, 0, v___x_574_);
    lean_ctor_set(v___x_575_, 1, v___x_573_);
    lean_ctor_set(v___x_575_, 2, v___x_572_);
    return v___x_575_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__21() -> *mut LeanObject {
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    v___x_576_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__20_once),
        _init_l_Array_qpartition___auto__1___closed__20,
    );
    v___x_577_ = l_Array_qpartition___auto__1___closed__5;
    v___x_578_ = lean_array_push(v___x_577_, v___x_576_);
    return v___x_578_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__22() -> *mut LeanObject {
    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    v___x_579_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__21_once),
        _init_l_Array_qpartition___auto__1___closed__21,
    );
    v___x_580_ = l_Array_qpartition___auto__1___closed__9;
    v___x_581_ = lean_box(2);
    v___x_582_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_582_, 0, v___x_581_);
    lean_ctor_set(v___x_582_, 1, v___x_580_);
    lean_ctor_set(v___x_582_, 2, v___x_579_);
    return v___x_582_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__23() -> *mut LeanObject {
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    v___x_583_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__22_once),
        _init_l_Array_qpartition___auto__1___closed__22,
    );
    v___x_584_ = l_Array_qpartition___auto__1___closed__5;
    v___x_585_ = lean_array_push(v___x_584_, v___x_583_);
    return v___x_585_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__24() -> *mut LeanObject {
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    v___x_586_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__23_once),
        _init_l_Array_qpartition___auto__1___closed__23,
    );
    v___x_587_ = l_Array_qpartition___auto__1___closed__7;
    v___x_588_ = lean_box(2);
    v___x_589_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_589_, 0, v___x_588_);
    lean_ctor_set(v___x_589_, 1, v___x_587_);
    lean_ctor_set(v___x_589_, 2, v___x_586_);
    return v___x_589_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__25() -> *mut LeanObject {
    let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    v___x_590_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__24_once),
        _init_l_Array_qpartition___auto__1___closed__24,
    );
    v___x_591_ = l_Array_qpartition___auto__1___closed__5;
    v___x_592_ = lean_array_push(v___x_591_, v___x_590_);
    return v___x_592_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1___closed__26() -> *mut LeanObject {
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    v___x_593_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__25_once),
        _init_l_Array_qpartition___auto__1___closed__25,
    );
    v___x_594_ = l_Array_qpartition___auto__1___closed__4;
    v___x_595_ = lean_box(2);
    v___x_596_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_596_, 0, v___x_595_);
    lean_ctor_set(v___x_596_, 1, v___x_594_);
    lean_ctor_set(v___x_596_, 2, v___x_593_);
    return v___x_596_;
}
pub unsafe fn _init_l_Array_qpartition___auto__1() -> *mut LeanObject {
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    v___x_597_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_597_;
}
pub unsafe fn _init_l_Array_qpartition___auto__3() -> *mut LeanObject {
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    v___x_598_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_598_;
}
pub unsafe fn _init_l_Array_qpartition___auto__5() -> *mut LeanObject {
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    v___x_599_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_599_;
}
pub unsafe fn _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__2()
-> *mut LeanObject {
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    v___x_600_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_600_;
}
pub unsafe fn _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__4()
-> *mut LeanObject {
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    v___x_601_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_601_;
}
pub unsafe fn _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__6()
-> *mut LeanObject {
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    v___x_602_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_602_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg(
    mut v_lt_603_: *mut LeanObject,
    mut v_hi_604_: *mut LeanObject,
    mut v_pivot_605_: *mut LeanObject,
    mut v_as_606_: *mut LeanObject,
    mut v_i_607_: *mut LeanObject,
    mut v_k_608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_609_: u8 = 0;
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: u8 = 0;
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_609_ = lean_nat_dec_lt(v_k_608_, v_hi_604_);
                if v___x_609_ == 0 {
                    lean_dec(v_k_608_);
                    lean_dec(v_pivot_605_);
                    lean_dec_ref(v_lt_603_);
                    v___x_610_ = lean_array_fswap(v_as_606_, v_i_607_, v_hi_604_);
                    v___x_611_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_611_, 0, v_i_607_);
                    lean_ctor_set(v___x_611_, 1, v___x_610_);
                    return v___x_611_;
                } else {
                    v___x_612_ = lean_array_fget_borrowed(v_as_606_, v_k_608_);
                    lean_inc_ref(v_lt_603_);
                    lean_inc(v_pivot_605_);
                    lean_inc(v___x_612_);
                    v___x_613_ = lean_apply_2(v_lt_603_, v___x_612_, v_pivot_605_);
                    v___x_614_ = (lean_unbox(v___x_613_) as u8);
                    if v___x_614_ == 0 {
                        v___x_615_ = lean_unsigned_to_nat(1);
                        v___x_616_ = lean_nat_add(v_k_608_, v___x_615_);
                        lean_dec(v_k_608_);
                        v_k_608_ = v___x_616_;
                        state = 0;
                        continue;
                    } else {
                        v___x_618_ = lean_array_fswap(v_as_606_, v_i_607_, v_k_608_);
                        v___x_619_ = lean_unsigned_to_nat(1);
                        v___x_620_ = lean_nat_add(v_i_607_, v___x_619_);
                        lean_dec(v_i_607_);
                        v___x_621_ = lean_nat_add(v_k_608_, v___x_619_);
                        lean_dec(v_k_608_);
                        v_as_606_ = v___x_618_;
                        v_i_607_ = v___x_620_;
                        v_k_608_ = v___x_621_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg___boxed(
    mut v_lt_623_: *mut LeanObject,
    mut v_hi_624_: *mut LeanObject,
    mut v_pivot_625_: *mut LeanObject,
    mut v_as_626_: *mut LeanObject,
    mut v_i_627_: *mut LeanObject,
    mut v_k_628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_629_: *mut LeanObject = core::ptr::null_mut();
    v_res_629_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg(
        v_lt_623_,
        v_hi_624_,
        v_pivot_625_,
        v_as_626_,
        v_i_627_,
        v_k_628_,
    );
    lean_dec(v_hi_624_);
    return v_res_629_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop(
    mut v_00_u03b1_630_: *mut LeanObject,
    mut v_n_631_: *mut LeanObject,
    mut v_lt_632_: *mut LeanObject,
    mut v_lo_633_: *mut LeanObject,
    mut v_hi_634_: *mut LeanObject,
    mut v_hhi_635_: *mut LeanObject,
    mut v_pivot_636_: *mut LeanObject,
    mut v_as_637_: *mut LeanObject,
    mut v_i_638_: *mut LeanObject,
    mut v_k_639_: *mut LeanObject,
    mut v_ilo_640_: *mut LeanObject,
    mut v_ik_641_: *mut LeanObject,
    mut v_w_642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    v___x_643_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg(
        v_lt_632_,
        v_hi_634_,
        v_pivot_636_,
        v_as_637_,
        v_i_638_,
        v_k_639_,
    );
    return v___x_643_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___boxed(
    mut v_00_u03b1_644_: *mut LeanObject,
    mut v_n_645_: *mut LeanObject,
    mut v_lt_646_: *mut LeanObject,
    mut v_lo_647_: *mut LeanObject,
    mut v_hi_648_: *mut LeanObject,
    mut v_hhi_649_: *mut LeanObject,
    mut v_pivot_650_: *mut LeanObject,
    mut v_as_651_: *mut LeanObject,
    mut v_i_652_: *mut LeanObject,
    mut v_k_653_: *mut LeanObject,
    mut v_ilo_654_: *mut LeanObject,
    mut v_ik_655_: *mut LeanObject,
    mut v_w_656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_657_: *mut LeanObject = core::ptr::null_mut();
    v_res_657_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop(
        v_00_u03b1_644_,
        v_n_645_,
        v_lt_646_,
        v_lo_647_,
        v_hi_648_,
        v_hhi_649_,
        v_pivot_650_,
        v_as_651_,
        v_i_652_,
        v_k_653_,
        v_ilo_654_,
        v_ik_655_,
        v_w_656_,
    );
    lean_dec(v_hi_648_);
    lean_dec(v_lo_647_);
    lean_dec(v_n_645_);
    return v_res_657_;
}
pub unsafe fn l_Array_qpartition___redArg(
    mut v_as_658_: *mut LeanObject,
    mut v_lt_659_: *mut LeanObject,
    mut v_lo_660_: *mut LeanObject,
    mut v_hi_661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: u8 = 0;
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: u8 = 0;
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_686_: u8 = 0;
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_666_ = lean_nat_add(v_lo_660_, v_hi_661_);
                v___x_667_ = lean_unsigned_to_nat(1);
                v_mid_668_ = lean_nat_shiftr(v___x_666_, v___x_667_);
                lean_dec(v___x_666_);
                v___x_683_ = lean_array_fget_borrowed(v_as_658_, v_mid_668_);
                v___x_684_ = lean_array_fget_borrowed(v_as_658_, v_lo_660_);
                lean_inc_ref(v_lt_659_);
                lean_inc(v___x_684_);
                lean_inc(v___x_683_);
                v___x_685_ = lean_apply_2(v_lt_659_, v___x_683_, v___x_684_);
                v___x_686_ = (lean_unbox(v___x_685_) as u8);
                if v___x_686_ == 0 {
                    v___y_677_ = v_as_658_;
                    state = 3;
                    continue;
                } else {
                    v___x_687_ = lean_array_fswap(v_as_658_, v_lo_660_, v_mid_668_);
                    v___y_677_ = v___x_687_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v_pivot_664_ = lean_array_fget(v___y_663_, v_hi_661_);
                lean_inc(v_lo_660_);
                v___x_665_ =
                    l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg(
                        v_lt_659_,
                        v_hi_661_,
                        v_pivot_664_,
                        v___y_663_,
                        v_lo_660_,
                        v_lo_660_,
                    );
                return v___x_665_;
            }
            2 => {
                v___x_671_ = lean_array_fget_borrowed(v___y_670_, v_mid_668_);
                v___x_672_ = lean_array_fget_borrowed(v___y_670_, v_hi_661_);
                lean_inc_ref(v_lt_659_);
                lean_inc(v___x_672_);
                lean_inc(v___x_671_);
                v___x_673_ = lean_apply_2(v_lt_659_, v___x_671_, v___x_672_);
                v___x_674_ = (lean_unbox(v___x_673_) as u8);
                if v___x_674_ == 0 {
                    lean_dec(v_mid_668_);
                    v___y_663_ = v___y_670_;
                    state = 1;
                    continue;
                } else {
                    v___x_675_ = lean_array_fswap(v___y_670_, v_mid_668_, v_hi_661_);
                    lean_dec(v_mid_668_);
                    v___y_663_ = v___x_675_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_678_ = lean_array_fget_borrowed(v___y_677_, v_hi_661_);
                v___x_679_ = lean_array_fget_borrowed(v___y_677_, v_lo_660_);
                lean_inc_ref(v_lt_659_);
                lean_inc(v___x_679_);
                lean_inc(v___x_678_);
                v___x_680_ = lean_apply_2(v_lt_659_, v___x_678_, v___x_679_);
                v___x_681_ = (lean_unbox(v___x_680_) as u8);
                if v___x_681_ == 0 {
                    v___y_670_ = v___y_677_;
                    state = 2;
                    continue;
                } else {
                    v___x_682_ = lean_array_fswap(v___y_677_, v_lo_660_, v_hi_661_);
                    v___y_670_ = v___x_682_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_qpartition___redArg___boxed(
    mut v_as_688_: *mut LeanObject,
    mut v_lt_689_: *mut LeanObject,
    mut v_lo_690_: *mut LeanObject,
    mut v_hi_691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_692_: *mut LeanObject = core::ptr::null_mut();
    v_res_692_ = l_Array_qpartition___redArg(v_as_688_, v_lt_689_, v_lo_690_, v_hi_691_);
    lean_dec(v_hi_691_);
    return v_res_692_;
}
pub unsafe fn l_Array_qpartition(
    mut v_00_u03b1_693_: *mut LeanObject,
    mut v_n_694_: *mut LeanObject,
    mut v_as_695_: *mut LeanObject,
    mut v_lt_696_: *mut LeanObject,
    mut v_lo_697_: *mut LeanObject,
    mut v_hi_698_: *mut LeanObject,
    mut v_w_699_: *mut LeanObject,
    mut v_hlo_700_: *mut LeanObject,
    mut v_hhi_701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_714_: u8 = 0;
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: u8 = 0;
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: u8 = 0;
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_706_ = lean_nat_add(v_lo_697_, v_hi_698_);
                v___x_707_ = lean_unsigned_to_nat(1);
                v_mid_708_ = lean_nat_shiftr(v___x_706_, v___x_707_);
                lean_dec(v___x_706_);
                v___x_723_ = lean_array_fget_borrowed(v_as_695_, v_mid_708_);
                v___x_724_ = lean_array_fget_borrowed(v_as_695_, v_lo_697_);
                lean_inc_ref(v_lt_696_);
                lean_inc(v___x_724_);
                lean_inc(v___x_723_);
                v___x_725_ = lean_apply_2(v_lt_696_, v___x_723_, v___x_724_);
                v___x_726_ = (lean_unbox(v___x_725_) as u8);
                if v___x_726_ == 0 {
                    v___y_717_ = v_as_695_;
                    state = 3;
                    continue;
                } else {
                    v___x_727_ = lean_array_fswap(v_as_695_, v_lo_697_, v_mid_708_);
                    v___y_717_ = v___x_727_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v_pivot_704_ = lean_array_fget(v___y_703_, v_hi_698_);
                lean_inc(v_lo_697_);
                v___x_705_ =
                    l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg(
                        v_lt_696_,
                        v_hi_698_,
                        v_pivot_704_,
                        v___y_703_,
                        v_lo_697_,
                        v_lo_697_,
                    );
                return v___x_705_;
            }
            2 => {
                v___x_711_ = lean_array_fget_borrowed(v___y_710_, v_mid_708_);
                v___x_712_ = lean_array_fget_borrowed(v___y_710_, v_hi_698_);
                lean_inc_ref(v_lt_696_);
                lean_inc(v___x_712_);
                lean_inc(v___x_711_);
                v___x_713_ = lean_apply_2(v_lt_696_, v___x_711_, v___x_712_);
                v___x_714_ = (lean_unbox(v___x_713_) as u8);
                if v___x_714_ == 0 {
                    lean_dec(v_mid_708_);
                    v___y_703_ = v___y_710_;
                    state = 1;
                    continue;
                } else {
                    v___x_715_ = lean_array_fswap(v___y_710_, v_mid_708_, v_hi_698_);
                    lean_dec(v_mid_708_);
                    v___y_703_ = v___x_715_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_718_ = lean_array_fget_borrowed(v___y_717_, v_hi_698_);
                v___x_719_ = lean_array_fget_borrowed(v___y_717_, v_lo_697_);
                lean_inc_ref(v_lt_696_);
                lean_inc(v___x_719_);
                lean_inc(v___x_718_);
                v___x_720_ = lean_apply_2(v_lt_696_, v___x_718_, v___x_719_);
                v___x_721_ = (lean_unbox(v___x_720_) as u8);
                if v___x_721_ == 0 {
                    v___y_710_ = v___y_717_;
                    state = 2;
                    continue;
                } else {
                    v___x_722_ = lean_array_fswap(v___y_717_, v_lo_697_, v_hi_698_);
                    v___y_710_ = v___x_722_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_qpartition___boxed(
    mut v_00_u03b1_728_: *mut LeanObject,
    mut v_n_729_: *mut LeanObject,
    mut v_as_730_: *mut LeanObject,
    mut v_lt_731_: *mut LeanObject,
    mut v_lo_732_: *mut LeanObject,
    mut v_hi_733_: *mut LeanObject,
    mut v_w_734_: *mut LeanObject,
    mut v_hlo_735_: *mut LeanObject,
    mut v_hhi_736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_737_: *mut LeanObject = core::ptr::null_mut();
    v_res_737_ = l_Array_qpartition(
        v_00_u03b1_728_,
        v_n_729_,
        v_as_730_,
        v_lt_731_,
        v_lo_732_,
        v_hi_733_,
        v_w_734_,
        v_hlo_735_,
        v_hhi_736_,
    );
    lean_dec(v_hi_733_);
    lean_dec(v_n_729_);
    return v_res_737_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__2() -> *mut LeanObject {
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    v___x_744_ = l_Array_qsort___auto__1___closed__0;
    v___x_745_ = l_Lean_mkAtom(v___x_744_);
    return v___x_745_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__3() -> *mut LeanObject {
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    v___x_746_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__2),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__2_once),
        _init_l_Array_qsort___auto__1___closed__2,
    );
    v___x_747_ = l_Array_qpartition___auto__1___closed__5;
    v___x_748_ = lean_array_push(v___x_747_, v___x_746_);
    return v___x_748_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__10() -> *mut LeanObject {
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    v___x_763_ = l_Array_qsort___auto__1___closed__9;
    v___x_764_ = l_Lean_mkAtom(v___x_763_);
    return v___x_764_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__11() -> *mut LeanObject {
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    v___x_765_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__10),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__10_once),
        _init_l_Array_qsort___auto__1___closed__10,
    );
    v___x_766_ = l_Array_qpartition___auto__1___closed__5;
    v___x_767_ = lean_array_push(v___x_766_, v___x_765_);
    return v___x_767_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__15() -> *mut LeanObject {
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    v___x_772_ = l_Array_qsort___auto__1___closed__14;
    v___x_773_ = lean_string_utf8_byte_size(v___x_772_);
    return v___x_773_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__16() -> *mut LeanObject {
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    v___x_774_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__15),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__15_once),
        _init_l_Array_qsort___auto__1___closed__15,
    );
    v___x_775_ = lean_unsigned_to_nat(0);
    v___x_776_ = l_Array_qsort___auto__1___closed__14;
    v___x_777_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_777_, 0, v___x_776_);
    lean_ctor_set(v___x_777_, 1, v___x_775_);
    lean_ctor_set(v___x_777_, 2, v___x_774_);
    return v___x_777_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__17() -> *mut LeanObject {
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    v___x_778_ = lean_box(0);
    v___x_779_ = lean_box(0);
    v___x_780_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__16),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__16_once),
        _init_l_Array_qsort___auto__1___closed__16,
    );
    v___x_781_ = lean_box(2);
    v___x_782_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_782_, 0, v___x_781_);
    lean_ctor_set(v___x_782_, 1, v___x_780_);
    lean_ctor_set(v___x_782_, 2, v___x_779_);
    lean_ctor_set(v___x_782_, 3, v___x_778_);
    return v___x_782_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__18() -> *mut LeanObject {
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    v___x_783_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__17_once),
        _init_l_Array_qsort___auto__1___closed__17,
    );
    v___x_784_ = l_Array_qpartition___auto__1___closed__5;
    v___x_785_ = lean_array_push(v___x_784_, v___x_783_);
    return v___x_785_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__19() -> *mut LeanObject {
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    v___x_786_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__18_once),
        _init_l_Array_qsort___auto__1___closed__18,
    );
    v___x_787_ = l_Array_qsort___auto__1___closed__13;
    v___x_788_ = lean_box(2);
    v___x_789_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_789_, 0, v___x_788_);
    lean_ctor_set(v___x_789_, 1, v___x_787_);
    lean_ctor_set(v___x_789_, 2, v___x_786_);
    return v___x_789_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__20() -> *mut LeanObject {
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    v___x_790_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__19_once),
        _init_l_Array_qsort___auto__1___closed__19,
    );
    v___x_791_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__11),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__11_once),
        _init_l_Array_qsort___auto__1___closed__11,
    );
    v___x_792_ = lean_array_push(v___x_791_, v___x_790_);
    return v___x_792_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__21() -> *mut LeanObject {
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    v___x_793_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__20_once),
        _init_l_Array_qsort___auto__1___closed__20,
    );
    v___x_794_ = l_Array_qsort___auto__1___closed__8;
    v___x_795_ = lean_box(2);
    v___x_796_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_796_, 0, v___x_795_);
    lean_ctor_set(v___x_796_, 1, v___x_794_);
    lean_ctor_set(v___x_796_, 2, v___x_793_);
    return v___x_796_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__22() -> *mut LeanObject {
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    v___x_797_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__21_once),
        _init_l_Array_qsort___auto__1___closed__21,
    );
    v___x_798_ = l_Array_qpartition___auto__1___closed__5;
    v___x_799_ = lean_array_push(v___x_798_, v___x_797_);
    return v___x_799_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__28() -> *mut LeanObject {
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    v___x_810_ = l_Array_qsort___auto__1___closed__27;
    v___x_811_ = l_Lean_mkAtom(v___x_810_);
    return v___x_811_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__29() -> *mut LeanObject {
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    v___x_812_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__28_once),
        _init_l_Array_qsort___auto__1___closed__28,
    );
    v___x_813_ = l_Array_qpartition___auto__1___closed__5;
    v___x_814_ = lean_array_push(v___x_813_, v___x_812_);
    return v___x_814_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__30() -> *mut LeanObject {
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    v___x_815_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__19_once),
        _init_l_Array_qsort___auto__1___closed__19,
    );
    v___x_816_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__29_once),
        _init_l_Array_qsort___auto__1___closed__29,
    );
    v___x_817_ = lean_array_push(v___x_816_, v___x_815_);
    return v___x_817_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__31() -> *mut LeanObject {
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    v___x_818_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__30),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__30_once),
        _init_l_Array_qsort___auto__1___closed__30,
    );
    v___x_819_ = l_Array_qsort___auto__1___closed__26;
    v___x_820_ = lean_box(2);
    v___x_821_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_821_, 0, v___x_820_);
    lean_ctor_set(v___x_821_, 1, v___x_819_);
    lean_ctor_set(v___x_821_, 2, v___x_818_);
    return v___x_821_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__32() -> *mut LeanObject {
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    v___x_822_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__31),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__31_once),
        _init_l_Array_qsort___auto__1___closed__31,
    );
    v___x_823_ = l_Array_qpartition___auto__1___closed__5;
    v___x_824_ = lean_array_push(v___x_823_, v___x_822_);
    return v___x_824_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__34() -> *mut LeanObject {
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    v___x_826_ = l_Array_qsort___auto__1___closed__33;
    v___x_827_ = l_Lean_mkAtom(v___x_826_);
    return v___x_827_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__35() -> *mut LeanObject {
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    v___x_828_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__34),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__34_once),
        _init_l_Array_qsort___auto__1___closed__34,
    );
    v___x_829_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__32_once),
        _init_l_Array_qsort___auto__1___closed__32,
    );
    v___x_830_ = lean_array_push(v___x_829_, v___x_828_);
    return v___x_830_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__36() -> *mut LeanObject {
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    v___x_831_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__31),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__31_once),
        _init_l_Array_qsort___auto__1___closed__31,
    );
    v___x_832_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__35),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__35_once),
        _init_l_Array_qsort___auto__1___closed__35,
    );
    v___x_833_ = lean_array_push(v___x_832_, v___x_831_);
    return v___x_833_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__37() -> *mut LeanObject {
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
    v___x_834_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__36),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__36_once),
        _init_l_Array_qsort___auto__1___closed__36,
    );
    v___x_835_ = l_Array_qsort___auto__1___closed__24;
    v___x_836_ = lean_box(2);
    v___x_837_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_837_, 0, v___x_836_);
    lean_ctor_set(v___x_837_, 1, v___x_835_);
    lean_ctor_set(v___x_837_, 2, v___x_834_);
    return v___x_837_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__38() -> *mut LeanObject {
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    v___x_838_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__37),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__37_once),
        _init_l_Array_qsort___auto__1___closed__37,
    );
    v___x_839_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__22_once),
        _init_l_Array_qsort___auto__1___closed__22,
    );
    v___x_840_ = lean_array_push(v___x_839_, v___x_838_);
    return v___x_840_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__40() -> *mut LeanObject {
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    v___x_842_ = l_Array_qsort___auto__1___closed__39;
    v___x_843_ = l_Lean_mkAtom(v___x_842_);
    return v___x_843_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__41() -> *mut LeanObject {
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    v___x_844_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__40),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__40_once),
        _init_l_Array_qsort___auto__1___closed__40,
    );
    v___x_845_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__38),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__38_once),
        _init_l_Array_qsort___auto__1___closed__38,
    );
    v___x_846_ = lean_array_push(v___x_845_, v___x_844_);
    return v___x_846_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__42() -> *mut LeanObject {
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    v___x_847_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__41),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__41_once),
        _init_l_Array_qsort___auto__1___closed__41,
    );
    v___x_848_ = l_Array_qsort___auto__1___closed__6;
    v___x_849_ = lean_box(2);
    v___x_850_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_850_, 0, v___x_849_);
    lean_ctor_set(v___x_850_, 1, v___x_848_);
    lean_ctor_set(v___x_850_, 2, v___x_847_);
    return v___x_850_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__43() -> *mut LeanObject {
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    v___x_851_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__42),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__42_once),
        _init_l_Array_qsort___auto__1___closed__42,
    );
    v___x_852_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__3),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__3_once),
        _init_l_Array_qsort___auto__1___closed__3,
    );
    v___x_853_ = lean_array_push(v___x_852_, v___x_851_);
    return v___x_853_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__44() -> *mut LeanObject {
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    v___x_854_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__43),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__43_once),
        _init_l_Array_qsort___auto__1___closed__43,
    );
    v___x_855_ = l_Array_qsort___auto__1___closed__1;
    v___x_856_ = lean_box(2);
    v___x_857_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_857_, 0, v___x_856_);
    lean_ctor_set(v___x_857_, 1, v___x_855_);
    lean_ctor_set(v___x_857_, 2, v___x_854_);
    return v___x_857_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__45() -> *mut LeanObject {
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    v___x_858_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__44),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__44_once),
        _init_l_Array_qsort___auto__1___closed__44,
    );
    v___x_859_ = l_Array_qpartition___auto__1___closed__5;
    v___x_860_ = lean_array_push(v___x_859_, v___x_858_);
    return v___x_860_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__46() -> *mut LeanObject {
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    v___x_861_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__45),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__45_once),
        _init_l_Array_qsort___auto__1___closed__45,
    );
    v___x_862_ = l_Array_qpartition___auto__1___closed__9;
    v___x_863_ = lean_box(2);
    v___x_864_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_864_, 0, v___x_863_);
    lean_ctor_set(v___x_864_, 1, v___x_862_);
    lean_ctor_set(v___x_864_, 2, v___x_861_);
    return v___x_864_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__47() -> *mut LeanObject {
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    v___x_865_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__46),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__46_once),
        _init_l_Array_qsort___auto__1___closed__46,
    );
    v___x_866_ = l_Array_qpartition___auto__1___closed__5;
    v___x_867_ = lean_array_push(v___x_866_, v___x_865_);
    return v___x_867_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__48() -> *mut LeanObject {
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    v___x_868_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__47),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__47_once),
        _init_l_Array_qsort___auto__1___closed__47,
    );
    v___x_869_ = l_Array_qpartition___auto__1___closed__7;
    v___x_870_ = lean_box(2);
    v___x_871_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_871_, 0, v___x_870_);
    lean_ctor_set(v___x_871_, 1, v___x_869_);
    lean_ctor_set(v___x_871_, 2, v___x_868_);
    return v___x_871_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__49() -> *mut LeanObject {
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    v___x_872_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__48),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__48_once),
        _init_l_Array_qsort___auto__1___closed__48,
    );
    v___x_873_ = l_Array_qpartition___auto__1___closed__5;
    v___x_874_ = lean_array_push(v___x_873_, v___x_872_);
    return v___x_874_;
}
pub unsafe fn _init_l_Array_qsort___auto__1___closed__50() -> *mut LeanObject {
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    v___x_875_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__49),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__49_once),
        _init_l_Array_qsort___auto__1___closed__49,
    );
    v___x_876_ = l_Array_qpartition___auto__1___closed__4;
    v___x_877_ = lean_box(2);
    v___x_878_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_878_, 0, v___x_877_);
    lean_ctor_set(v___x_878_, 1, v___x_876_);
    lean_ctor_set(v___x_878_, 2, v___x_875_);
    return v___x_878_;
}
pub unsafe fn _init_l_Array_qsort___auto__1() -> *mut LeanObject {
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    v___x_879_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__50),
        core::ptr::addr_of_mut!(l_Array_qsort___auto__1___closed__50_once),
        _init_l_Array_qsort___auto__1___closed__50,
    );
    return v___x_879_;
}
pub unsafe fn _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__2()
-> *mut LeanObject {
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    v___x_880_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_880_;
}
pub unsafe fn _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__4()
-> *mut LeanObject {
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    v___x_881_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_881_;
}
pub unsafe fn _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__6()
-> *mut LeanObject {
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    v___x_882_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Array_qpartition___auto__1___closed__26_once),
        _init_l_Array_qpartition___auto__1___closed__26,
    );
    return v___x_882_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
    mut v_lt_883_: *mut LeanObject,
    mut v_as_884_: *mut LeanObject,
    mut v_lo_885_: *mut LeanObject,
    mut v_hi_886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: u8 = 0;
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: u8 = 0;
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: u8 = 0;
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: u8 = 0;
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: u8 = 0;
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_898_ = lean_nat_dec_lt(v_lo_885_, v_hi_886_);
                if v___x_898_ == 0 {
                    lean_dec(v_lo_885_);
                    lean_dec_ref(v_lt_883_);
                    return v_as_884_;
                } else {
                    v___x_899_ = lean_nat_add(v_lo_885_, v_hi_886_);
                    v___x_900_ = lean_unsigned_to_nat(1);
                    v_mid_901_ = lean_nat_shiftr(v___x_899_, v___x_900_);
                    lean_dec(v___x_899_);
                    v___x_916_ = lean_array_fget_borrowed(v_as_884_, v_mid_901_);
                    v___x_917_ = lean_array_fget_borrowed(v_as_884_, v_lo_885_);
                    lean_inc_ref(v_lt_883_);
                    lean_inc(v___x_917_);
                    lean_inc(v___x_916_);
                    v___x_918_ = lean_apply_2(v_lt_883_, v___x_916_, v___x_917_);
                    v___x_919_ = (lean_unbox(v___x_918_) as u8);
                    if v___x_919_ == 0 {
                        v___y_910_ = v_as_884_;
                        state = 3;
                        continue;
                    } else {
                        v___x_920_ = lean_array_fswap(v_as_884_, v_lo_885_, v_mid_901_);
                        v___y_910_ = v___x_920_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_889_ = lean_array_fget(v___y_888_, v_hi_886_);
                lean_inc_n(v_lo_885_, 2);
                lean_inc_ref(v_lt_883_);
                v___x_890_ =
                    l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___redArg(
                        v_lt_883_,
                        v_hi_886_,
                        v_pivot_889_,
                        v___y_888_,
                        v_lo_885_,
                        v_lo_885_,
                    );
                v_fst_891_ = lean_ctor_get(v___x_890_, 0);
                lean_inc(v_fst_891_);
                v_snd_892_ = lean_ctor_get(v___x_890_, 1);
                lean_inc(v_snd_892_);
                lean_dec_ref(v___x_890_);
                v___x_893_ = lean_nat_dec_le(v_hi_886_, v_fst_891_);
                if v___x_893_ == 0 {
                    lean_inc_ref(v_lt_883_);
                    v___x_894_ =
                        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
                            v_lt_883_, v_snd_892_, v_lo_885_, v_fst_891_,
                        );
                    v___x_895_ = lean_unsigned_to_nat(1);
                    v___x_896_ = lean_nat_add(v_fst_891_, v___x_895_);
                    lean_dec(v_fst_891_);
                    v_as_884_ = v___x_894_;
                    v_lo_885_ = v___x_896_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_fst_891_);
                    lean_dec(v_lo_885_);
                    lean_dec_ref(v_lt_883_);
                    return v_snd_892_;
                }
            }
            2 => {
                v___x_904_ = lean_array_fget_borrowed(v___y_903_, v_mid_901_);
                v___x_905_ = lean_array_fget_borrowed(v___y_903_, v_hi_886_);
                lean_inc_ref(v_lt_883_);
                lean_inc(v___x_905_);
                lean_inc(v___x_904_);
                v___x_906_ = lean_apply_2(v_lt_883_, v___x_904_, v___x_905_);
                v___x_907_ = (lean_unbox(v___x_906_) as u8);
                if v___x_907_ == 0 {
                    lean_dec(v_mid_901_);
                    v___y_888_ = v___y_903_;
                    state = 1;
                    continue;
                } else {
                    v___x_908_ = lean_array_fswap(v___y_903_, v_mid_901_, v_hi_886_);
                    lean_dec(v_mid_901_);
                    v___y_888_ = v___x_908_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_911_ = lean_array_fget_borrowed(v___y_910_, v_hi_886_);
                v___x_912_ = lean_array_fget_borrowed(v___y_910_, v_lo_885_);
                lean_inc_ref(v_lt_883_);
                lean_inc(v___x_912_);
                lean_inc(v___x_911_);
                v___x_913_ = lean_apply_2(v_lt_883_, v___x_911_, v___x_912_);
                v___x_914_ = (lean_unbox(v___x_913_) as u8);
                if v___x_914_ == 0 {
                    v___y_903_ = v___y_910_;
                    state = 2;
                    continue;
                } else {
                    v___x_915_ = lean_array_fswap(v___y_910_, v_lo_885_, v_hi_886_);
                    v___y_903_ = v___x_915_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg___boxed(
    mut v_lt_921_: *mut LeanObject,
    mut v_as_922_: *mut LeanObject,
    mut v_lo_923_: *mut LeanObject,
    mut v_hi_924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_925_: *mut LeanObject = core::ptr::null_mut();
    v_res_925_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
        v_lt_921_, v_as_922_, v_lo_923_, v_hi_924_,
    );
    lean_dec(v_hi_924_);
    return v_res_925_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
    mut v_00_u03b1_926_: *mut LeanObject,
    mut v_lt_927_: *mut LeanObject,
    mut v_n_928_: *mut LeanObject,
    mut v_as_929_: *mut LeanObject,
    mut v_lo_930_: *mut LeanObject,
    mut v_hi_931_: *mut LeanObject,
    mut v_w_932_: *mut LeanObject,
    mut v_hlo_933_: *mut LeanObject,
    mut v_hhi_934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    v___x_935_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
        v_lt_927_, v_as_929_, v_lo_930_, v_hi_931_,
    );
    return v___x_935_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___boxed(
    mut v_00_u03b1_936_: *mut LeanObject,
    mut v_lt_937_: *mut LeanObject,
    mut v_n_938_: *mut LeanObject,
    mut v_as_939_: *mut LeanObject,
    mut v_lo_940_: *mut LeanObject,
    mut v_hi_941_: *mut LeanObject,
    mut v_w_942_: *mut LeanObject,
    mut v_hlo_943_: *mut LeanObject,
    mut v_hhi_944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_945_: *mut LeanObject = core::ptr::null_mut();
    v_res_945_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
        v_00_u03b1_936_,
        v_lt_937_,
        v_n_938_,
        v_as_939_,
        v_lo_940_,
        v_hi_941_,
        v_w_942_,
        v_hlo_943_,
        v_hhi_944_,
    );
    lean_dec(v_hi_941_);
    lean_dec(v_n_938_);
    return v_res_945_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_match__8_splitter___redArg(
    mut v_x_946_: *mut LeanObject,
    mut v_h__1_947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    v_fst_948_ = lean_ctor_get(v_x_946_, 0);
    lean_inc(v_fst_948_);
    v_snd_949_ = lean_ctor_get(v_x_946_, 1);
    lean_inc(v_snd_949_);
    lean_dec_ref(v_x_946_);
    v___x_950_ = lean_apply_3(v_h__1_947_, v_fst_948_, lean_box(0), v_snd_949_);
    return v___x_950_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_match__8_splitter(
    mut v_00_u03b1_951_: *mut LeanObject,
    mut v_n_952_: *mut LeanObject,
    mut v_lo_953_: *mut LeanObject,
    mut v_hi_954_: *mut LeanObject,
    mut v_motive_955_: *mut LeanObject,
    mut v_x_956_: *mut LeanObject,
    mut v_h__1_957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    v_fst_958_ = lean_ctor_get(v_x_956_, 0);
    lean_inc(v_fst_958_);
    v_snd_959_ = lean_ctor_get(v_x_956_, 1);
    lean_inc(v_snd_959_);
    lean_dec_ref(v_x_956_);
    v___x_960_ = lean_apply_3(v_h__1_957_, v_fst_958_, lean_box(0), v_snd_959_);
    return v___x_960_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_match__8_splitter___boxed(
    mut v_00_u03b1_961_: *mut LeanObject,
    mut v_n_962_: *mut LeanObject,
    mut v_lo_963_: *mut LeanObject,
    mut v_hi_964_: *mut LeanObject,
    mut v_motive_965_: *mut LeanObject,
    mut v_x_966_: *mut LeanObject,
    mut v_h__1_967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_968_: *mut LeanObject = core::ptr::null_mut();
    v_res_968_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_match__8_splitter(
        v_00_u03b1_961_,
        v_n_962_,
        v_lo_963_,
        v_hi_964_,
        v_motive_965_,
        v_x_966_,
        v_h__1_967_,
    );
    lean_dec(v_hi_964_);
    lean_dec(v_lo_963_);
    lean_dec(v_n_962_);
    return v_res_968_;
}
pub unsafe fn l_Array_qsort___redArg(
    mut v_as_969_: *mut LeanObject,
    mut v_lt_970_: *mut LeanObject,
    mut v_lo_971_: *mut LeanObject,
    mut v_hi_972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: u8 = 0;
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: u8 = 0;
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: u8 = 0;
    let mut v___x_987_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_979_ = lean_array_get_size(v_as_969_);
                v___x_980_ = lean_unsigned_to_nat(0);
                v___x_981_ = lean_nat_dec_eq(v___x_979_, v___x_980_);
                if v___x_981_ == 0 {
                    v___x_982_ = lean_unsigned_to_nat(1);
                    v___x_983_ = lean_nat_sub(v___x_979_, v___x_982_);
                    v___x_987_ = lean_nat_dec_le(v_lo_971_, v___x_983_);
                    if v___x_987_ == 0 {
                        lean_dec(v_lo_971_);
                        lean_inc(v___x_983_);
                        v___y_985_ = v___x_983_;
                        state = 2;
                        continue;
                    } else {
                        v___y_985_ = v_lo_971_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_hi_972_);
                    lean_dec(v_lo_971_);
                    lean_dec_ref(v_lt_970_);
                    return v_as_969_;
                }
            }
            1 => {
                v___x_976_ = lean_nat_dec_le(v___y_974_, v___y_975_);
                if v___x_976_ == 0 {
                    lean_dec(v___y_975_);
                    lean_inc(v___y_974_);
                    v___x_977_ =
                        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
                            v_lt_970_, v_as_969_, v___y_974_, v___y_974_,
                        );
                    lean_dec(v___y_974_);
                    return v___x_977_;
                } else {
                    v___x_978_ =
                        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
                            v_lt_970_, v_as_969_, v___y_974_, v___y_975_,
                        );
                    lean_dec(v___y_975_);
                    return v___x_978_;
                }
            }
            2 => {
                v___x_986_ = lean_nat_dec_le(v_hi_972_, v___x_983_);
                if v___x_986_ == 0 {
                    lean_dec(v_hi_972_);
                    v___y_974_ = v___y_985_;
                    v___y_975_ = v___x_983_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_983_);
                    v___y_974_ = v___y_985_;
                    v___y_975_ = v_hi_972_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_qsort(
    mut v_00_u03b1_988_: *mut LeanObject,
    mut v_as_989_: *mut LeanObject,
    mut v_lt_990_: *mut LeanObject,
    mut v_lo_991_: *mut LeanObject,
    mut v_hi_992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_996_: u8 = 0;
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: u8 = 0;
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: u8 = 0;
    let mut v___x_1007_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_999_ = lean_array_get_size(v_as_989_);
                v___x_1000_ = lean_unsigned_to_nat(0);
                v___x_1001_ = lean_nat_dec_eq(v___x_999_, v___x_1000_);
                if v___x_1001_ == 0 {
                    v___x_1002_ = lean_unsigned_to_nat(1);
                    v___x_1003_ = lean_nat_sub(v___x_999_, v___x_1002_);
                    v___x_1007_ = lean_nat_dec_le(v_lo_991_, v___x_1003_);
                    if v___x_1007_ == 0 {
                        lean_dec(v_lo_991_);
                        lean_inc(v___x_1003_);
                        v___y_1005_ = v___x_1003_;
                        state = 2;
                        continue;
                    } else {
                        v___y_1005_ = v_lo_991_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_hi_992_);
                    lean_dec(v_lo_991_);
                    lean_dec_ref(v_lt_990_);
                    return v_as_989_;
                }
            }
            1 => {
                v___x_996_ = lean_nat_dec_le(v___y_994_, v___y_995_);
                if v___x_996_ == 0 {
                    lean_dec(v___y_995_);
                    lean_inc(v___y_994_);
                    v___x_997_ =
                        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
                            v_lt_990_, v_as_989_, v___y_994_, v___y_994_,
                        );
                    lean_dec(v___y_994_);
                    return v___x_997_;
                } else {
                    v___x_998_ =
                        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
                            v_lt_990_, v_as_989_, v___y_994_, v___y_995_,
                        );
                    lean_dec(v___y_995_);
                    return v___x_998_;
                }
            }
            2 => {
                v___x_1006_ = lean_nat_dec_le(v_hi_992_, v___x_1003_);
                if v___x_1006_ == 0 {
                    lean_dec(v_hi_992_);
                    v___y_994_ = v___y_1005_;
                    v___y_995_ = v___x_1003_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_1003_);
                    v___y_994_ = v___y_1005_;
                    v___y_995_ = v_hi_992_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_qsortOrd___redArg___lam__0(
    mut v_ord_1008_: *mut LeanObject,
    mut v___x_1009_: u8,
    mut v_x_1010_: *mut LeanObject,
    mut v_y_1011_: *mut LeanObject,
) -> u8 {
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: u8 = 0;
    v___x_1012_ = lean_apply_2(v_ord_1008_, v_x_1010_, v_y_1011_);
    v___x_1013_ = (lean_unbox(v___x_1012_) as u8);
    if v___x_1013_ == 0 {
        let mut v___x_1014_: u8 = 0;
        v___x_1014_ = 1;
        return v___x_1014_;
    } else {
        return v___x_1009_;
    }
}
pub unsafe fn l_Array_qsortOrd___redArg___lam__0___boxed(
    mut v_ord_1015_: *mut LeanObject,
    mut v___x_1016_: *mut LeanObject,
    mut v_x_1017_: *mut LeanObject,
    mut v_y_1018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_63__boxed_1019_: u8 = 0;
    let mut v_res_1020_: u8 = 0;
    let mut v_r_1021_: *mut LeanObject = core::ptr::null_mut();
    v___x_63__boxed_1019_ = (lean_unbox(v___x_1016_) as u8);
    v_res_1020_ = l_Array_qsortOrd___redArg___lam__0(
        v_ord_1015_,
        v___x_63__boxed_1019_,
        v_x_1017_,
        v_y_1018_,
    );
    v_r_1021_ = lean_box((v_res_1020_) as usize);
    return v_r_1021_;
}
pub unsafe fn l_Array_qsortOrd___redArg(
    mut v_ord_1022_: *mut LeanObject,
    mut v_xs_1023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: u8 = 0;
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: u8 = 0;
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1024_ = lean_array_get_size(v_xs_1023_);
                v___x_1025_ = lean_unsigned_to_nat(0);
                v___x_1026_ = lean_nat_dec_eq(v___x_1024_, v___x_1025_);
                if v___x_1026_ == 0 {
                    v___x_1027_ = lean_box((v___x_1026_) as usize);
                    v___f_1028_ = lean_alloc_closure(
                        l_Array_qsortOrd___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    lean_closure_set(v___f_1028_, 0, v_ord_1022_);
                    lean_closure_set(v___f_1028_, 1, v___x_1027_);
                    v___x_1029_ = lean_unsigned_to_nat(1);
                    v___x_1030_ = lean_nat_sub(v___x_1024_, v___x_1029_);
                    v___x_1036_ = lean_nat_dec_le(v___x_1025_, v___x_1030_);
                    if v___x_1036_ == 0 {
                        lean_inc(v___x_1030_);
                        v___y_1032_ = v___x_1030_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1032_ = v___x_1025_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_ord_1022_);
                    return v_xs_1023_;
                }
            }
            1 => {
                v___x_1033_ = lean_nat_dec_le(v___y_1032_, v___x_1030_);
                if v___x_1033_ == 0 {
                    lean_dec(v___x_1030_);
                    lean_inc(v___y_1032_);
                    v___x_1034_ =
                        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
                            v___f_1028_,
                            v_xs_1023_,
                            v___y_1032_,
                            v___y_1032_,
                        );
                    lean_dec(v___y_1032_);
                    return v___x_1034_;
                } else {
                    v___x_1035_ =
                        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___redArg(
                            v___f_1028_,
                            v_xs_1023_,
                            v___y_1032_,
                            v___x_1030_,
                        );
                    lean_dec(v___x_1030_);
                    return v___x_1035_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_qsortOrd(
    mut v_00_u03b1_1037_: *mut LeanObject,
    mut v_ord_1038_: *mut LeanObject,
    mut v_xs_1039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    v___x_1040_ = l_Array_qsortOrd___redArg(v_ord_1038_, v_xs_1039_);
    return v___x_1040_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_QSort_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord_Basic(builtin);
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
pub unsafe fn meta_initialize_Init_Data_Array_QSort_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Array_qpartition___auto__1 = _init_l_Array_qpartition___auto__1();
    lean_mark_persistent(l_Array_qpartition___auto__1);
    l_Array_qpartition___auto__3 = _init_l_Array_qpartition___auto__3();
    lean_mark_persistent(l_Array_qpartition___auto__3);
    l_Array_qpartition___auto__5 = _init_l_Array_qpartition___auto__5();
    lean_mark_persistent(l_Array_qpartition___auto__5);
    l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__2 =
        _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__2();
    lean_mark_persistent(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__2);
    l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__4 =
        _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__4();
    lean_mark_persistent(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__4);
    l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__6 =
        _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__6();
    lean_mark_persistent(l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition___auto__6);
    l_Array_qsort___auto__1 = _init_l_Array_qsort___auto__1();
    lean_mark_persistent(l_Array_qsort___auto__1);
    l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__2 =
        _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__2();
    lean_mark_persistent(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__2);
    l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__4 =
        _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__4();
    lean_mark_persistent(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__4);
    l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__6 =
        _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__6();
    lean_mark_persistent(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort___auto__6);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_QSort_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Vector_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Ord_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_QSort_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_QSort_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Array_QSort_Basic(builtin);
}

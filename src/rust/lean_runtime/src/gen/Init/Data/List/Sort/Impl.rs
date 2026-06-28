// Lean compiler output
// Module: Init.Data.List.Sort.Impl
// Imports: Init.Data.List.Sort.Basic Init.Data.List.Sort.Basic Init.Data.List.Sort.Lemmas Init.Data.Nat.Linear
use crate::r#gen::Init::Data::List::Basic::l_List_reverseAux___redArg;
use crate::r#gen::Init::Data::List::Sort::Basic::{
    initialize_Init_Data_List_Sort_Basic, l_List_MergeSort_Internal_splitInTwo___redArg,
    runtime_initialize_Init_Data_List_Sort_Basic,
};
use crate::r#gen::Init::Data::List::Sort::Lemmas::{
    initialize_Init_Data_List_Sort_Lemmas, runtime_initialize_Init_Data_List_Sort_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom, l_List_lengthTR___redArg,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_sub, lean_string_utf8_byte_size,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_apply_3,
    lean_apply_4, lean_apply_5, lean_box, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0_value: LeanStringObject<5> =
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
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0_value)
        as *mut LeanObject;
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1_value: LeanStringObject<7> =
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
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1_value)
        as *mut LeanObject;
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__2_value: LeanStringObject<7> =
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
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__2_value)
        as *mut LeanObject;
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__3_value: LeanStringObject<10> =
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
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__3_value)
        as *mut LeanObject;
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__3_value)
                as *mut LeanObject,
            8504843326314613972 as *mut LeanObject,
        ],
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4_value)
        as *mut LeanObject;
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5_value: LeanArrayObject<0> =
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
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5_value)
        as *mut LeanObject;
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__6_value: LeanStringObject<19> =
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
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__6_value)
        as *mut LeanObject;
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__6_value)
                as *mut LeanObject,
            17228437386856258271 as *mut LeanObject,
        ],
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7_value)
        as *mut LeanObject;
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__8_value: LeanStringObject<5> =
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
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__8_value)
        as *mut LeanObject;
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__8_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9_value)
        as *mut LeanObject;
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__10_value: LeanStringObject<6> =
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
        m_data: [101, 120, 97, 99, 116, 0],
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__10_value)
        as *mut LeanObject;
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__10_value)
                as *mut LeanObject,
            14997215300048349804 as *mut LeanObject,
        ],
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11_value)
        as *mut LeanObject;
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__14_value: LeanStringObject<5> =
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
        m_data: [84, 101, 114, 109, 0],
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__14_value)
        as *mut LeanObject;
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__15_value: LeanStringObject<4> =
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
        m_data: [102, 117, 110, 0],
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__15_value)
        as *mut LeanObject;
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__14_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__15_value)
                as *mut LeanObject,
            7043493786777132025 as *mut LeanObject,
        ],
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16_value)
        as *mut LeanObject;
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__17: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18: *mut LeanObject =
    core::ptr::null_mut();
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__19_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [98, 97, 115, 105, 99, 70, 117, 110, 0],
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__19_value)
        as *mut LeanObject;
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__14_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__19_value)
                as *mut LeanObject,
            16077784126176397009 as *mut LeanObject,
        ],
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20_value)
        as *mut LeanObject;
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__21_value: LeanStringObject<2> =
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
        m_data: [97, 0],
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__21_value)
        as *mut LeanObject;
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23: *mut LeanObject =
    core::ptr::null_mut();
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__24_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__21_value)
                as *mut LeanObject,
            7839396180116328695 as *mut LeanObject,
        ],
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__24_value)
        as *mut LeanObject;
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26: *mut LeanObject =
    core::ptr::null_mut();
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27_value: LeanStringObject<2> =
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
        m_data: [98, 0],
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27_value)
        as *mut LeanObject;
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29: *mut LeanObject =
    core::ptr::null_mut();
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__30_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27_value)
                as *mut LeanObject,
            10300200614825825839 as *mut LeanObject,
        ],
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__30_value)
        as *mut LeanObject;
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34: *mut LeanObject =
    core::ptr::null_mut();
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__35_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__35_value)
        as *mut LeanObject;
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36: *mut LeanObject =
    core::ptr::null_mut();
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__37_value: LeanStringObject<3> =
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
        m_data: [61, 62, 0],
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__37_value)
        as *mut LeanObject;
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39: *mut LeanObject =
    core::ptr::null_mut();
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__40_value: LeanStringObject<
    10,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 7,
    m_data: [116, 101, 114, 109, 95, 226, 137, 164, 95, 0],
};
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__40_value)
        as *mut LeanObject;
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__41_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__40_value)
                as *mut LeanObject,
            8748957123817046895 as *mut LeanObject,
        ],
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__41_value)
        as *mut LeanObject;
pub static l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__42_value: LeanStringObject<4> =
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
        m_data: [226, 137, 164, 0],
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__42: *mut LeanObject =
    core::ptr::addr_of!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__42_value)
        as *mut LeanObject;
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__57_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__57: *mut LeanObject =
    core::ptr::null_mut();
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_List_MergeSort_Internal_mergeSortTR___auto__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_List_MergeSort_Internal_mergeSortTR_u2082___auto__1: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go___redArg(
    mut v_le_611_: *mut LeanObject,
    mut v_a_612_: *mut LeanObject,
    mut v_a_613_: *mut LeanObject,
    mut v_a_614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: u8 = 0;
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_625_: u8 = 0;
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_630_: u8 = 0;
    let mut v_unused_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_635_: u8 = 0;
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_640_: u8 = 0;
    let mut v_unused_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_642_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_612_) == 0 {
                    lean_dec_ref(v_le_611_);
                    v___x_615_ = l_List_reverseAux___redArg(v_a_614_, v_a_613_);
                    return v___x_615_;
                } else {
                    if lean_obj_tag(v_a_613_) == 0 {
                        lean_dec_ref(v_le_611_);
                        v___x_616_ = l_List_reverseAux___redArg(v_a_614_, v_a_612_);
                        return v___x_616_;
                    } else {
                        v_head_617_ = lean_ctor_get(v_a_612_, 0);
                        v_tail_618_ = lean_ctor_get(v_a_612_, 1);
                        v_head_619_ = lean_ctor_get(v_a_613_, 0);
                        v_tail_620_ = lean_ctor_get(v_a_613_, 1);
                        lean_inc_ref(v_le_611_);
                        lean_inc(v_head_619_);
                        lean_inc(v_head_617_);
                        v___x_621_ = lean_apply_2(v_le_611_, v_head_617_, v_head_619_);
                        v___x_622_ = (lean_unbox(v___x_621_) as u8);
                        if v___x_622_ == 0 {
                            lean_inc(v_tail_620_);
                            lean_inc(v_head_619_);
                            v_isSharedCheck_630_ = (!lean_is_exclusive(v_a_613_)) as u8;
                            if v_isSharedCheck_630_ == 0 {
                                v_unused_631_ = lean_ctor_get(v_a_613_, 1);
                                lean_dec(v_unused_631_);
                                v_unused_632_ = lean_ctor_get(v_a_613_, 0);
                                lean_dec(v_unused_632_);
                                v___x_624_ = v_a_613_;
                                v_isShared_625_ = v_isSharedCheck_630_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_a_613_);
                                v___x_624_ = lean_box(0);
                                v_isShared_625_ = v_isSharedCheck_630_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_inc(v_tail_618_);
                            lean_inc(v_head_617_);
                            v_isSharedCheck_640_ = (!lean_is_exclusive(v_a_612_)) as u8;
                            if v_isSharedCheck_640_ == 0 {
                                v_unused_641_ = lean_ctor_get(v_a_612_, 1);
                                lean_dec(v_unused_641_);
                                v_unused_642_ = lean_ctor_get(v_a_612_, 0);
                                lean_dec(v_unused_642_);
                                v___x_634_ = v_a_612_;
                                v_isShared_635_ = v_isSharedCheck_640_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v_a_612_);
                                v___x_634_ = lean_box(0);
                                v_isShared_635_ = v_isSharedCheck_640_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_625_ == 0 {
                    lean_ctor_set(v___x_624_, 1, v_a_614_);
                    v___x_627_ = v___x_624_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_629_, 0, v_head_619_);
                    lean_ctor_set(v_reuseFailAlloc_629_, 1, v_a_614_);
                    v___x_627_ = v_reuseFailAlloc_629_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_613_ = v_tail_620_;
                v_a_614_ = v___x_627_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_635_ == 0 {
                    lean_ctor_set(v___x_634_, 1, v_a_614_);
                    v___x_637_ = v___x_634_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_639_, 0, v_head_617_);
                    lean_ctor_set(v_reuseFailAlloc_639_, 1, v_a_614_);
                    v___x_637_ = v_reuseFailAlloc_639_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_612_ = v_tail_618_;
                v_a_614_ = v___x_637_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go(
    mut v_00_u03b1_643_: *mut LeanObject,
    mut v_le_644_: *mut LeanObject,
    mut v_a_645_: *mut LeanObject,
    mut v_a_646_: *mut LeanObject,
    mut v_a_647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    v___x_648_ =
        l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go___redArg(
            v_le_644_, v_a_645_, v_a_646_, v_a_647_,
        );
    return v___x_648_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go_match__1_splitter___redArg(
    mut v_x_649_: *mut LeanObject,
    mut v_x_650_: *mut LeanObject,
    mut v_x_651_: *mut LeanObject,
    mut v_h__1_652_: *mut LeanObject,
    mut v_h__2_653_: *mut LeanObject,
    mut v_h__3_654_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_649_) == 0 {
        let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_654_);
        lean_dec(v_h__2_653_);
        v___x_655_ = lean_apply_2(v_h__1_652_, v_x_650_, v_x_651_);
        return v___x_655_;
    } else {
        lean_dec(v_h__1_652_);
        if lean_obj_tag(v_x_650_) == 0 {
            let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_654_);
            v___x_656_ = lean_apply_3(v_h__2_653_, v_x_649_, v_x_651_, lean_box(0));
            return v___x_656_;
        } else {
            let mut v_head_657_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_658_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_659_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_660_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_653_);
            v_head_657_ = lean_ctor_get(v_x_649_, 0);
            lean_inc(v_head_657_);
            v_tail_658_ = lean_ctor_get(v_x_649_, 1);
            lean_inc(v_tail_658_);
            lean_dec_ref_known(v_x_649_, 2);
            v_head_659_ = lean_ctor_get(v_x_650_, 0);
            lean_inc(v_head_659_);
            v_tail_660_ = lean_ctor_get(v_x_650_, 1);
            lean_inc(v_tail_660_);
            lean_dec_ref_known(v_x_650_, 2);
            v___x_661_ = lean_apply_5(
                v_h__3_654_,
                v_head_657_,
                v_tail_658_,
                v_head_659_,
                v_tail_660_,
                v_x_651_,
            );
            return v___x_661_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go_match__1_splitter(
    mut v_00_u03b1_662_: *mut LeanObject,
    mut v_motive_663_: *mut LeanObject,
    mut v_x_664_: *mut LeanObject,
    mut v_x_665_: *mut LeanObject,
    mut v_x_666_: *mut LeanObject,
    mut v_h__1_667_: *mut LeanObject,
    mut v_h__2_668_: *mut LeanObject,
    mut v_h__3_669_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_664_) == 0 {
        let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_669_);
        lean_dec(v_h__2_668_);
        v___x_670_ = lean_apply_2(v_h__1_667_, v_x_665_, v_x_666_);
        return v___x_670_;
    } else {
        lean_dec(v_h__1_667_);
        if lean_obj_tag(v_x_665_) == 0 {
            let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_669_);
            v___x_671_ = lean_apply_3(v_h__2_668_, v_x_664_, v_x_666_, lean_box(0));
            return v___x_671_;
        } else {
            let mut v_head_672_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_673_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_674_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_675_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_668_);
            v_head_672_ = lean_ctor_get(v_x_664_, 0);
            lean_inc(v_head_672_);
            v_tail_673_ = lean_ctor_get(v_x_664_, 1);
            lean_inc(v_tail_673_);
            lean_dec_ref_known(v_x_664_, 2);
            v_head_674_ = lean_ctor_get(v_x_665_, 0);
            lean_inc(v_head_674_);
            v_tail_675_ = lean_ctor_get(v_x_665_, 1);
            lean_inc(v_tail_675_);
            lean_dec_ref_known(v_x_665_, 2);
            v___x_676_ = lean_apply_5(
                v_h__3_669_,
                v_head_672_,
                v_tail_673_,
                v_head_674_,
                v_tail_675_,
                v_x_666_,
            );
            return v___x_676_;
        }
    }
}
pub unsafe fn l_List_MergeSort_Internal_mergeTR___redArg(
    mut v_l_u2081_677_: *mut LeanObject,
    mut v_l_u2082_678_: *mut LeanObject,
    mut v_le_679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    v___x_680_ = lean_box(0);
    v___x_681_ =
        l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeTR_go___redArg(
            v_le_679_,
            v_l_u2081_677_,
            v_l_u2082_678_,
            v___x_680_,
        );
    return v___x_681_;
}
pub unsafe fn l_List_MergeSort_Internal_mergeTR(
    mut v_00_u03b1_682_: *mut LeanObject,
    mut v_l_u2081_683_: *mut LeanObject,
    mut v_l_u2082_684_: *mut LeanObject,
    mut v_le_685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    v___x_686_ =
        l_List_MergeSort_Internal_mergeTR___redArg(v_l_u2081_683_, v_l_u2082_684_, v_le_685_);
    return v___x_686_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_merge_match__1_splitter___redArg(
    mut v_xs_687_: *mut LeanObject,
    mut v_ys_688_: *mut LeanObject,
    mut v_h__1_689_: *mut LeanObject,
    mut v_h__2_690_: *mut LeanObject,
    mut v_h__3_691_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_xs_687_) == 0 {
        let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_691_);
        lean_dec(v_h__2_690_);
        v___x_692_ = lean_apply_1(v_h__1_689_, v_ys_688_);
        return v___x_692_;
    } else {
        lean_dec(v_h__1_689_);
        if lean_obj_tag(v_ys_688_) == 0 {
            let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_691_);
            v___x_693_ = lean_apply_2(v_h__2_690_, v_xs_687_, lean_box(0));
            return v___x_693_;
        } else {
            let mut v_head_694_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_695_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_696_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_697_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_690_);
            v_head_694_ = lean_ctor_get(v_xs_687_, 0);
            lean_inc(v_head_694_);
            v_tail_695_ = lean_ctor_get(v_xs_687_, 1);
            lean_inc(v_tail_695_);
            lean_dec_ref_known(v_xs_687_, 2);
            v_head_696_ = lean_ctor_get(v_ys_688_, 0);
            lean_inc(v_head_696_);
            v_tail_697_ = lean_ctor_get(v_ys_688_, 1);
            lean_inc(v_tail_697_);
            lean_dec_ref_known(v_ys_688_, 2);
            v___x_698_ = lean_apply_4(
                v_h__3_691_,
                v_head_694_,
                v_tail_695_,
                v_head_696_,
                v_tail_697_,
            );
            return v___x_698_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_merge_match__1_splitter(
    mut v_00_u03b1_699_: *mut LeanObject,
    mut v_motive_700_: *mut LeanObject,
    mut v_xs_701_: *mut LeanObject,
    mut v_ys_702_: *mut LeanObject,
    mut v_h__1_703_: *mut LeanObject,
    mut v_h__2_704_: *mut LeanObject,
    mut v_h__3_705_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_xs_701_) == 0 {
        let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_705_);
        lean_dec(v_h__2_704_);
        v___x_706_ = lean_apply_1(v_h__1_703_, v_ys_702_);
        return v___x_706_;
    } else {
        lean_dec(v_h__1_703_);
        if lean_obj_tag(v_ys_702_) == 0 {
            let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_705_);
            v___x_707_ = lean_apply_2(v_h__2_704_, v_xs_701_, lean_box(0));
            return v___x_707_;
        } else {
            let mut v_head_708_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_709_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_710_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_711_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_704_);
            v_head_708_ = lean_ctor_get(v_xs_701_, 0);
            lean_inc(v_head_708_);
            v_tail_709_ = lean_ctor_get(v_xs_701_, 1);
            lean_inc(v_tail_709_);
            lean_dec_ref_known(v_xs_701_, 2);
            v_head_710_ = lean_ctor_get(v_ys_702_, 0);
            lean_inc(v_head_710_);
            v_tail_711_ = lean_ctor_get(v_ys_702_, 1);
            lean_inc(v_tail_711_);
            lean_dec_ref_known(v_ys_702_, 2);
            v___x_712_ = lean_apply_4(
                v_h__3_705_,
                v_head_708_,
                v_tail_709_,
                v_head_710_,
                v_tail_711_,
            );
            return v___x_712_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go___redArg(
    mut v_a_713_: *mut LeanObject,
    mut v_a_714_: *mut LeanObject,
    mut v_a_715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_719_: u8 = 0;
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_722_: u8 = 0;
    let mut v_one_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_729_: u8 = 0;
    let mut v_unused_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_713_) == 1 {
                    v_head_716_ = lean_ctor_get(v_a_713_, 0);
                    v_tail_717_ = lean_ctor_get(v_a_713_, 1);
                    v_zero_718_ = lean_unsigned_to_nat(0);
                    v_isZero_719_ = lean_nat_dec_eq(v_a_714_, v_zero_718_);
                    if v_isZero_719_ == 0 {
                        lean_inc(v_tail_717_);
                        lean_inc(v_head_716_);
                        v_isSharedCheck_729_ = (!lean_is_exclusive(v_a_713_)) as u8;
                        if v_isSharedCheck_729_ == 0 {
                            v_unused_730_ = lean_ctor_get(v_a_713_, 1);
                            lean_dec(v_unused_730_);
                            v_unused_731_ = lean_ctor_get(v_a_713_, 0);
                            lean_dec(v_unused_731_);
                            v___x_721_ = v_a_713_;
                            v_isShared_722_ = v_isSharedCheck_729_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_713_);
                            v___x_721_ = lean_box(0);
                            v_isShared_722_ = v_isSharedCheck_729_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_714_);
                        v___x_732_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_732_, 0, v_a_715_);
                        lean_ctor_set(v___x_732_, 1, v_a_713_);
                        return v___x_732_;
                    }
                } else {
                    lean_dec(v_a_714_);
                    v___x_733_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_733_, 0, v_a_715_);
                    lean_ctor_set(v___x_733_, 1, v_a_713_);
                    return v___x_733_;
                }
            }
            1 => {
                v_one_723_ = lean_unsigned_to_nat(1);
                v_n_724_ = lean_nat_sub(v_a_714_, v_one_723_);
                lean_dec(v_a_714_);
                if v_isShared_722_ == 0 {
                    lean_ctor_set(v___x_721_, 1, v_a_715_);
                    v___x_726_ = v___x_721_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_728_, 0, v_head_716_);
                    lean_ctor_set(v_reuseFailAlloc_728_, 1, v_a_715_);
                    v___x_726_ = v_reuseFailAlloc_728_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_713_ = v_tail_717_;
                v_a_714_ = v_n_724_;
                v_a_715_ = v___x_726_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go(
    mut v_00_u03b1_734_: *mut LeanObject,
    mut v_a_735_: *mut LeanObject,
    mut v_a_736_: *mut LeanObject,
    mut v_a_737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    v___x_738_ =
        l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go___redArg(
            v_a_735_, v_a_736_, v_a_737_,
        );
    return v___x_738_;
}
pub unsafe fn l_List_MergeSort_Internal_splitRevAt___redArg(
    mut v_n_739_: *mut LeanObject,
    mut v_l_740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    v___x_741_ = lean_box(0);
    v___x_742_ =
        l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go___redArg(
            v_l_740_, v_n_739_, v___x_741_,
        );
    return v___x_742_;
}
pub unsafe fn l_List_MergeSort_Internal_splitRevAt(
    mut v_00_u03b1_743_: *mut LeanObject,
    mut v_n_744_: *mut LeanObject,
    mut v_l_745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    v___x_746_ = l_List_MergeSort_Internal_splitRevAt___redArg(v_n_744_, v_l_745_);
    return v___x_746_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go_match__1_splitter___redArg(
    mut v_x_747_: *mut LeanObject,
    mut v_x_748_: *mut LeanObject,
    mut v_x_749_: *mut LeanObject,
    mut v_h__1_750_: *mut LeanObject,
    mut v_h__2_751_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_747_) == 1 {
        let mut v_head_752_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_753_: *mut LeanObject = core::ptr::null_mut();
        let mut v_zero_754_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_755_: u8 = 0;
        v_head_752_ = lean_ctor_get(v_x_747_, 0);
        v_tail_753_ = lean_ctor_get(v_x_747_, 1);
        v_zero_754_ = lean_unsigned_to_nat(0);
        v_isZero_755_ = lean_nat_dec_eq(v_x_748_, v_zero_754_);
        if v_isZero_755_ == 0 {
            let mut v_one_756_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_757_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_753_);
            lean_inc(v_head_752_);
            lean_dec_ref_known(v_x_747_, 2);
            lean_dec(v_h__2_751_);
            v_one_756_ = lean_unsigned_to_nat(1);
            v_n_757_ = lean_nat_sub(v_x_748_, v_one_756_);
            lean_dec(v_x_748_);
            v___x_758_ = lean_apply_4(v_h__1_750_, v_head_752_, v_tail_753_, v_n_757_, v_x_749_);
            return v___x_758_;
        } else {
            let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_750_);
            v___x_759_ = lean_apply_4(v_h__2_751_, v_x_747_, v_x_748_, v_x_749_, lean_box(0));
            return v___x_759_;
        }
    } else {
        let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_750_);
        v___x_760_ = lean_apply_4(v_h__2_751_, v_x_747_, v_x_748_, v_x_749_, lean_box(0));
        return v___x_760_;
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_splitRevAt_go_match__1_splitter(
    mut v_00_u03b1_761_: *mut LeanObject,
    mut v_motive_762_: *mut LeanObject,
    mut v_x_763_: *mut LeanObject,
    mut v_x_764_: *mut LeanObject,
    mut v_x_765_: *mut LeanObject,
    mut v_h__1_766_: *mut LeanObject,
    mut v_h__2_767_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_763_) == 1 {
        let mut v_head_768_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_769_: *mut LeanObject = core::ptr::null_mut();
        let mut v_zero_770_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_771_: u8 = 0;
        v_head_768_ = lean_ctor_get(v_x_763_, 0);
        v_tail_769_ = lean_ctor_get(v_x_763_, 1);
        v_zero_770_ = lean_unsigned_to_nat(0);
        v_isZero_771_ = lean_nat_dec_eq(v_x_764_, v_zero_770_);
        if v_isZero_771_ == 0 {
            let mut v_one_772_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_773_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_769_);
            lean_inc(v_head_768_);
            lean_dec_ref_known(v_x_763_, 2);
            lean_dec(v_h__2_767_);
            v_one_772_ = lean_unsigned_to_nat(1);
            v_n_773_ = lean_nat_sub(v_x_764_, v_one_772_);
            lean_dec(v_x_764_);
            v___x_774_ = lean_apply_4(v_h__1_766_, v_head_768_, v_tail_769_, v_n_773_, v_x_765_);
            return v___x_774_;
        } else {
            let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_766_);
            v___x_775_ = lean_apply_4(v_h__2_767_, v_x_763_, v_x_764_, v_x_765_, lean_box(0));
            return v___x_775_;
        }
    } else {
        let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_766_);
        v___x_776_ = lean_apply_4(v_h__2_767_, v_x_763_, v_x_764_, v_x_765_, lean_box(0));
        return v___x_776_;
    }
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__12() -> *mut LeanObject
{
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    v___x_803_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__10;
    v___x_804_ = l_Lean_mkAtom(v___x_803_);
    return v___x_804_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13() -> *mut LeanObject
{
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    v___x_805_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__12_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__12,
    );
    v___x_806_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5;
    v___x_807_ = lean_array_push(v___x_806_, v___x_805_);
    return v___x_807_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__17() -> *mut LeanObject
{
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    v___x_815_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__15;
    v___x_816_ = l_Lean_mkAtom(v___x_815_);
    return v___x_816_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18() -> *mut LeanObject
{
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    v___x_817_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__17_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__17,
    );
    v___x_818_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5;
    v___x_819_ = lean_array_push(v___x_818_, v___x_817_);
    return v___x_819_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22() -> *mut LeanObject
{
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    v___x_827_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__21;
    v___x_828_ = lean_string_utf8_byte_size(v___x_827_);
    return v___x_828_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23() -> *mut LeanObject
{
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    v___x_829_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__22,
    );
    v___x_830_ = lean_unsigned_to_nat(0);
    v___x_831_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__21;
    v___x_832_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_832_, 0, v___x_831_);
    lean_ctor_set(v___x_832_, 1, v___x_830_);
    lean_ctor_set(v___x_832_, 2, v___x_829_);
    return v___x_832_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25() -> *mut LeanObject
{
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    v___x_835_ = lean_box(0);
    v___x_836_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__24;
    v___x_837_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__23,
    );
    v___x_838_ = lean_box(2);
    v___x_839_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_839_, 0, v___x_838_);
    lean_ctor_set(v___x_839_, 1, v___x_837_);
    lean_ctor_set(v___x_839_, 2, v___x_836_);
    lean_ctor_set(v___x_839_, 3, v___x_835_);
    return v___x_839_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26() -> *mut LeanObject
{
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    v___x_840_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__25,
    );
    v___x_841_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5;
    v___x_842_ = lean_array_push(v___x_841_, v___x_840_);
    return v___x_842_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28() -> *mut LeanObject
{
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    v___x_844_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27;
    v___x_845_ = lean_string_utf8_byte_size(v___x_844_);
    return v___x_845_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29() -> *mut LeanObject
{
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    v___x_846_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__28,
    );
    v___x_847_ = lean_unsigned_to_nat(0);
    v___x_848_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__27;
    v___x_849_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_849_, 0, v___x_848_);
    lean_ctor_set(v___x_849_, 1, v___x_847_);
    lean_ctor_set(v___x_849_, 2, v___x_846_);
    return v___x_849_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31() -> *mut LeanObject
{
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    v___x_852_ = lean_box(0);
    v___x_853_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__30;
    v___x_854_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__29,
    );
    v___x_855_ = lean_box(2);
    v___x_856_ = lean_alloc_ctor(3, 4, (0) as u32);
    lean_ctor_set(v___x_856_, 0, v___x_855_);
    lean_ctor_set(v___x_856_, 1, v___x_854_);
    lean_ctor_set(v___x_856_, 2, v___x_853_);
    lean_ctor_set(v___x_856_, 3, v___x_852_);
    return v___x_856_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32() -> *mut LeanObject
{
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    v___x_857_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31,
    );
    v___x_858_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26,
    );
    v___x_859_ = lean_array_push(v___x_858_, v___x_857_);
    return v___x_859_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33() -> *mut LeanObject
{
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    v___x_860_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__32,
    );
    v___x_861_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9;
    v___x_862_ = lean_box(2);
    v___x_863_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_863_, 0, v___x_862_);
    lean_ctor_set(v___x_863_, 1, v___x_861_);
    lean_ctor_set(v___x_863_, 2, v___x_860_);
    return v___x_863_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34() -> *mut LeanObject
{
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    v___x_864_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__33,
    );
    v___x_865_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5;
    v___x_866_ = lean_array_push(v___x_865_, v___x_864_);
    return v___x_866_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36() -> *mut LeanObject
{
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
    v___x_871_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__35;
    v___x_872_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__34,
    );
    v___x_873_ = lean_array_push(v___x_872_, v___x_871_);
    return v___x_873_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38() -> *mut LeanObject
{
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    v___x_875_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__37;
    v___x_876_ = l_Lean_mkAtom(v___x_875_);
    return v___x_876_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39() -> *mut LeanObject
{
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    v___x_877_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__38,
    );
    v___x_878_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__36,
    );
    v___x_879_ = lean_array_push(v___x_878_, v___x_877_);
    return v___x_879_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43() -> *mut LeanObject
{
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    v___x_884_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__42;
    v___x_885_ = l_Lean_mkAtom(v___x_884_);
    return v___x_885_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44() -> *mut LeanObject
{
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    v___x_886_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__43,
    );
    v___x_887_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__26,
    );
    v___x_888_ = lean_array_push(v___x_887_, v___x_886_);
    return v___x_888_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45() -> *mut LeanObject
{
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    v___x_889_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__31,
    );
    v___x_890_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__44,
    );
    v___x_891_ = lean_array_push(v___x_890_, v___x_889_);
    return v___x_891_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46() -> *mut LeanObject
{
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    v___x_892_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__45,
    );
    v___x_893_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__41;
    v___x_894_ = lean_box(2);
    v___x_895_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_895_, 0, v___x_894_);
    lean_ctor_set(v___x_895_, 1, v___x_893_);
    lean_ctor_set(v___x_895_, 2, v___x_892_);
    return v___x_895_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47() -> *mut LeanObject
{
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    v___x_896_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__46,
    );
    v___x_897_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__39,
    );
    v___x_898_ = lean_array_push(v___x_897_, v___x_896_);
    return v___x_898_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48() -> *mut LeanObject
{
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
    v___x_899_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__47,
    );
    v___x_900_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__20;
    v___x_901_ = lean_box(2);
    v___x_902_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_902_, 0, v___x_901_);
    lean_ctor_set(v___x_902_, 1, v___x_900_);
    lean_ctor_set(v___x_902_, 2, v___x_899_);
    return v___x_902_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49() -> *mut LeanObject
{
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    v___x_903_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__48,
    );
    v___x_904_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__18,
    );
    v___x_905_ = lean_array_push(v___x_904_, v___x_903_);
    return v___x_905_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50() -> *mut LeanObject
{
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    v___x_906_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__49,
    );
    v___x_907_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__16;
    v___x_908_ = lean_box(2);
    v___x_909_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_909_, 0, v___x_908_);
    lean_ctor_set(v___x_909_, 1, v___x_907_);
    lean_ctor_set(v___x_909_, 2, v___x_906_);
    return v___x_909_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51() -> *mut LeanObject
{
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    v___x_910_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__50,
    );
    v___x_911_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__13,
    );
    v___x_912_ = lean_array_push(v___x_911_, v___x_910_);
    return v___x_912_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52() -> *mut LeanObject
{
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    v___x_913_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__51,
    );
    v___x_914_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__11;
    v___x_915_ = lean_box(2);
    v___x_916_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_916_, 0, v___x_915_);
    lean_ctor_set(v___x_916_, 1, v___x_914_);
    lean_ctor_set(v___x_916_, 2, v___x_913_);
    return v___x_916_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53() -> *mut LeanObject
{
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    v___x_917_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__52,
    );
    v___x_918_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5;
    v___x_919_ = lean_array_push(v___x_918_, v___x_917_);
    return v___x_919_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54() -> *mut LeanObject
{
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    v___x_920_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__53,
    );
    v___x_921_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__9;
    v___x_922_ = lean_box(2);
    v___x_923_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_923_, 0, v___x_922_);
    lean_ctor_set(v___x_923_, 1, v___x_921_);
    lean_ctor_set(v___x_923_, 2, v___x_920_);
    return v___x_923_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55() -> *mut LeanObject
{
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    v___x_924_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__54,
    );
    v___x_925_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5;
    v___x_926_ = lean_array_push(v___x_925_, v___x_924_);
    return v___x_926_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56() -> *mut LeanObject
{
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    v___x_927_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__55,
    );
    v___x_928_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__7;
    v___x_929_ = lean_box(2);
    v___x_930_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_930_, 0, v___x_929_);
    lean_ctor_set(v___x_930_, 1, v___x_928_);
    lean_ctor_set(v___x_930_, 2, v___x_927_);
    return v___x_930_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__57() -> *mut LeanObject
{
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    v___x_931_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__56,
    );
    v___x_932_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__5;
    v___x_933_ = lean_array_push(v___x_932_, v___x_931_);
    return v___x_933_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58() -> *mut LeanObject
{
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    v___x_934_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__57),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__57_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__57,
    );
    v___x_935_ = l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__4;
    v___x_936_ = lean_box(2);
    v___x_937_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_937_, 0, v___x_936_);
    lean_ctor_set(v___x_937_, 1, v___x_935_);
    lean_ctor_set(v___x_937_, 2, v___x_934_);
    return v___x_937_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR___auto__1() -> *mut LeanObject {
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    v___x_938_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58,
    );
    return v___x_938_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(
    mut v_le_939_: *mut LeanObject,
    mut v_n_940_: *mut LeanObject,
    mut v_a_941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_943_: u8 = 0;
    v_zero_942_ = lean_unsigned_to_nat(0);
    v_isZero_943_ = lean_nat_dec_eq(v_n_940_, v_zero_942_);
    if v_isZero_943_ == 1 {
        lean_dec_ref(v_le_939_);
        return v_a_941_;
    } else {
        let mut v_one_944_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_945_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_946_: u8 = 0;
        v_one_944_ = lean_unsigned_to_nat(1);
        v_n_945_ = lean_nat_sub(v_n_940_, v_one_944_);
        v_isZero_946_ = lean_nat_dec_eq(v_n_945_, v_zero_942_);
        if v_isZero_946_ == 1 {
            lean_dec(v_n_945_);
            lean_dec_ref(v_le_939_);
            return v_a_941_;
        } else {
            let mut v_n_947_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fst_951_: *mut LeanObject = core::ptr::null_mut();
            let mut v_snd_952_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
            v_n_947_ = lean_nat_sub(v_n_945_, v_one_944_);
            lean_dec(v_n_945_);
            v___x_948_ = lean_unsigned_to_nat(2);
            v___x_949_ = lean_nat_add(v_n_947_, v___x_948_);
            lean_dec(v_n_947_);
            v___x_950_ = l_List_MergeSort_Internal_splitInTwo___redArg(v___x_949_, v_a_941_);
            v_fst_951_ = lean_ctor_get(v___x_950_, 0);
            lean_inc(v_fst_951_);
            v_snd_952_ = lean_ctor_get(v___x_950_, 1);
            lean_inc(v_snd_952_);
            lean_dec_ref(v___x_950_);
            v___x_953_ = lean_nat_add(v___x_949_, v_one_944_);
            v___x_954_ = lean_nat_shiftr(v___x_953_, v_one_944_);
            lean_dec(v___x_953_);
            lean_inc_ref_n(v_le_939_, 2);
            v___x_955_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(v_le_939_, v___x_954_, v_fst_951_);
            lean_dec(v___x_954_);
            v___x_956_ = lean_nat_shiftr(v___x_949_, v_one_944_);
            lean_dec(v___x_949_);
            v___x_957_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(v_le_939_, v___x_956_, v_snd_952_);
            lean_dec(v___x_956_);
            v___x_958_ =
                l_List_MergeSort_Internal_mergeTR___redArg(v___x_955_, v___x_957_, v_le_939_);
            return v___x_958_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg___boxed(
    mut v_le_959_: *mut LeanObject,
    mut v_n_960_: *mut LeanObject,
    mut v_a_961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_962_: *mut LeanObject = core::ptr::null_mut();
    v_res_962_ =
        l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(
            v_le_959_, v_n_960_, v_a_961_,
        );
    lean_dec(v_n_960_);
    return v_res_962_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run(
    mut v_00_u03b1_963_: *mut LeanObject,
    mut v_le_964_: *mut LeanObject,
    mut v_n_965_: *mut LeanObject,
    mut v_a_966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    v___x_967_ =
        l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(
            v_le_964_, v_n_965_, v_a_966_,
        );
    return v___x_967_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___boxed(
    mut v_00_u03b1_968_: *mut LeanObject,
    mut v_le_969_: *mut LeanObject,
    mut v_n_970_: *mut LeanObject,
    mut v_a_971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_972_: *mut LeanObject = core::ptr::null_mut();
    v_res_972_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run(
        v_00_u03b1_968_,
        v_le_969_,
        v_n_970_,
        v_a_971_,
    );
    lean_dec(v_n_970_);
    return v_res_972_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter___redArg(
    mut v_x_973_: *mut LeanObject,
    mut v_x_974_: *mut LeanObject,
    mut v_h__1_975_: *mut LeanObject,
    mut v_h__2_976_: *mut LeanObject,
    mut v_h__3_977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_979_: u8 = 0;
    v_zero_978_ = lean_unsigned_to_nat(0);
    v_isZero_979_ = lean_nat_dec_eq(v_x_973_, v_zero_978_);
    if v_isZero_979_ == 1 {
        let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_977_);
        lean_dec(v_h__2_976_);
        lean_dec(v_x_974_);
        v___x_980_ = lean_apply_1(v_h__1_975_, lean_box(0));
        return v___x_980_;
    } else {
        let mut v_one_981_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_982_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_983_: u8 = 0;
        lean_dec(v_h__1_975_);
        v_one_981_ = lean_unsigned_to_nat(1);
        v_n_982_ = lean_nat_sub(v_x_973_, v_one_981_);
        v_isZero_983_ = lean_nat_dec_eq(v_n_982_, v_zero_978_);
        if v_isZero_983_ == 1 {
            let mut v_head_984_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_n_982_);
            lean_dec(v_h__3_977_);
            v_head_984_ = lean_ctor_get(v_x_974_, 0);
            lean_inc(v_head_984_);
            lean_dec(v_x_974_);
            v___x_985_ = lean_apply_2(v_h__2_976_, v_head_984_, lean_box(0));
            return v___x_985_;
        } else {
            let mut v_n_986_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_976_);
            v_n_986_ = lean_nat_sub(v_n_982_, v_one_981_);
            lean_dec(v_n_982_);
            v___x_987_ = lean_apply_2(v_h__3_977_, v_n_986_, v_x_974_);
            return v___x_987_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter___redArg___boxed(
    mut v_x_988_: *mut LeanObject,
    mut v_x_989_: *mut LeanObject,
    mut v_h__1_990_: *mut LeanObject,
    mut v_h__2_991_: *mut LeanObject,
    mut v_h__3_992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_993_: *mut LeanObject = core::ptr::null_mut();
    v_res_993_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter___redArg(v_x_988_, v_x_989_, v_h__1_990_, v_h__2_991_, v_h__3_992_);
    lean_dec(v_x_988_);
    return v_res_993_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter(
    mut v_00_u03b1_994_: *mut LeanObject,
    mut v_motive_995_: *mut LeanObject,
    mut v_x_996_: *mut LeanObject,
    mut v_x_997_: *mut LeanObject,
    mut v_h__1_998_: *mut LeanObject,
    mut v_h__2_999_: *mut LeanObject,
    mut v_h__3_1000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1002_: u8 = 0;
    v_zero_1001_ = lean_unsigned_to_nat(0);
    v_isZero_1002_ = lean_nat_dec_eq(v_x_996_, v_zero_1001_);
    if v_isZero_1002_ == 1 {
        let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_1000_);
        lean_dec(v_h__2_999_);
        lean_dec(v_x_997_);
        v___x_1003_ = lean_apply_1(v_h__1_998_, lean_box(0));
        return v___x_1003_;
    } else {
        let mut v_one_1004_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_1005_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_1006_: u8 = 0;
        lean_dec(v_h__1_998_);
        v_one_1004_ = lean_unsigned_to_nat(1);
        v_n_1005_ = lean_nat_sub(v_x_996_, v_one_1004_);
        v_isZero_1006_ = lean_nat_dec_eq(v_n_1005_, v_zero_1001_);
        if v_isZero_1006_ == 1 {
            let mut v_head_1007_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_n_1005_);
            lean_dec(v_h__3_1000_);
            v_head_1007_ = lean_ctor_get(v_x_997_, 0);
            lean_inc(v_head_1007_);
            lean_dec(v_x_997_);
            v___x_1008_ = lean_apply_2(v_h__2_999_, v_head_1007_, lean_box(0));
            return v___x_1008_;
        } else {
            let mut v_n_1009_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_999_);
            v_n_1009_ = lean_nat_sub(v_n_1005_, v_one_1004_);
            lean_dec(v_n_1005_);
            v___x_1010_ = lean_apply_2(v_h__3_1000_, v_n_1009_, v_x_997_);
            return v___x_1010_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter___boxed(
    mut v_00_u03b1_1011_: *mut LeanObject,
    mut v_motive_1012_: *mut LeanObject,
    mut v_x_1013_: *mut LeanObject,
    mut v_x_1014_: *mut LeanObject,
    mut v_h__1_1015_: *mut LeanObject,
    mut v_h__2_1016_: *mut LeanObject,
    mut v_h__3_1017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1018_: *mut LeanObject = core::ptr::null_mut();
    v_res_1018_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__3_splitter(v_00_u03b1_1011_, v_motive_1012_, v_x_1013_, v_x_1014_, v_h__1_1015_, v_h__2_1016_, v_h__3_1017_);
    lean_dec(v_x_1013_);
    return v_res_1018_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__1_splitter___redArg(
    mut v_x_1019_: *mut LeanObject,
    mut v_h__1_1020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1021_ = lean_ctor_get(v_x_1019_, 0);
    lean_inc(v_fst_1021_);
    v_snd_1022_ = lean_ctor_get(v_x_1019_, 1);
    lean_inc(v_snd_1022_);
    lean_dec_ref(v_x_1019_);
    v___x_1023_ = lean_apply_2(v_h__1_1020_, v_fst_1021_, v_snd_1022_);
    return v___x_1023_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__1_splitter(
    mut v_00_u03b1_1024_: *mut LeanObject,
    mut v_n_1025_: *mut LeanObject,
    mut v_motive_1026_: *mut LeanObject,
    mut v_x_1027_: *mut LeanObject,
    mut v_h__1_1028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1029_ = lean_ctor_get(v_x_1027_, 0);
    lean_inc(v_fst_1029_);
    v_snd_1030_ = lean_ctor_get(v_x_1027_, 1);
    lean_inc(v_snd_1030_);
    lean_dec_ref(v_x_1027_);
    v___x_1031_ = lean_apply_2(v_h__1_1028_, v_fst_1029_, v_snd_1030_);
    return v___x_1031_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__1_splitter___boxed(
    mut v_00_u03b1_1032_: *mut LeanObject,
    mut v_n_1033_: *mut LeanObject,
    mut v_motive_1034_: *mut LeanObject,
    mut v_x_1035_: *mut LeanObject,
    mut v_h__1_1036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1037_: *mut LeanObject = core::ptr::null_mut();
    v_res_1037_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run_match__1_splitter(v_00_u03b1_1032_, v_n_1033_, v_motive_1034_, v_x_1035_, v_h__1_1036_);
    lean_dec(v_n_1033_);
    return v_res_1037_;
}
pub unsafe fn l_List_MergeSort_Internal_mergeSortTR___redArg(
    mut v_l_1038_: *mut LeanObject,
    mut v_le_1039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    v___x_1040_ = l_List_lengthTR___redArg(v_l_1038_);
    v___x_1041_ =
        l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_run___redArg(
            v_le_1039_,
            v___x_1040_,
            v_l_1038_,
        );
    lean_dec(v___x_1040_);
    return v___x_1041_;
}
pub unsafe fn l_List_MergeSort_Internal_mergeSortTR(
    mut v_00_u03b1_1042_: *mut LeanObject,
    mut v_l_1043_: *mut LeanObject,
    mut v_le_1044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    v___x_1045_ = l_List_MergeSort_Internal_mergeSortTR___redArg(v_l_1043_, v_le_1044_);
    return v___x_1045_;
}
pub unsafe fn l_List_MergeSort_Internal_splitRevInTwo___redArg(
    mut v_n_1046_: *mut LeanObject,
    mut v_l_1047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1056_: u8 = 0;
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1060_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1048_ = lean_unsigned_to_nat(1);
                v___x_1049_ = lean_nat_add(v_n_1046_, v___x_1048_);
                v___x_1050_ = lean_nat_shiftr(v___x_1049_, v___x_1048_);
                lean_dec(v___x_1049_);
                v_r_1051_ = l_List_MergeSort_Internal_splitRevAt___redArg(v___x_1050_, v_l_1047_);
                v_fst_1052_ = lean_ctor_get(v_r_1051_, 0);
                v_snd_1053_ = lean_ctor_get(v_r_1051_, 1);
                v_isSharedCheck_1060_ = (!lean_is_exclusive(v_r_1051_)) as u8;
                if v_isSharedCheck_1060_ == 0 {
                    v___x_1055_ = v_r_1051_;
                    v_isShared_1056_ = v_isSharedCheck_1060_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_1053_);
                    lean_inc(v_fst_1052_);
                    lean_dec(v_r_1051_);
                    v___x_1055_ = lean_box(0);
                    v_isShared_1056_ = v_isSharedCheck_1060_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1056_ == 0 {
                    v___x_1058_ = v___x_1055_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_fst_1052_);
                    lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_snd_1053_);
                    v___x_1058_ = v_reuseFailAlloc_1059_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1058_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_MergeSort_Internal_splitRevInTwo___redArg___boxed(
    mut v_n_1061_: *mut LeanObject,
    mut v_l_1062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1063_: *mut LeanObject = core::ptr::null_mut();
    v_res_1063_ = l_List_MergeSort_Internal_splitRevInTwo___redArg(v_n_1061_, v_l_1062_);
    lean_dec(v_n_1061_);
    return v_res_1063_;
}
pub unsafe fn l_List_MergeSort_Internal_splitRevInTwo(
    mut v_00_u03b1_1064_: *mut LeanObject,
    mut v_n_1065_: *mut LeanObject,
    mut v_l_1066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    v___x_1067_ = l_List_MergeSort_Internal_splitRevInTwo___redArg(v_n_1065_, v_l_1066_);
    return v___x_1067_;
}
pub unsafe fn l_List_MergeSort_Internal_splitRevInTwo___boxed(
    mut v_00_u03b1_1068_: *mut LeanObject,
    mut v_n_1069_: *mut LeanObject,
    mut v_l_1070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1071_: *mut LeanObject = core::ptr::null_mut();
    v_res_1071_ = l_List_MergeSort_Internal_splitRevInTwo(v_00_u03b1_1068_, v_n_1069_, v_l_1070_);
    lean_dec(v_n_1069_);
    return v_res_1071_;
}
pub unsafe fn l_List_MergeSort_Internal_splitRevInTwo_x27___redArg(
    mut v_n_1072_: *mut LeanObject,
    mut v_l_1073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1081_: u8 = 0;
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1085_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1074_ = lean_unsigned_to_nat(1);
                v___x_1075_ = lean_nat_shiftr(v_n_1072_, v___x_1074_);
                v_r_1076_ = l_List_MergeSort_Internal_splitRevAt___redArg(v___x_1075_, v_l_1073_);
                v_fst_1077_ = lean_ctor_get(v_r_1076_, 0);
                v_snd_1078_ = lean_ctor_get(v_r_1076_, 1);
                v_isSharedCheck_1085_ = (!lean_is_exclusive(v_r_1076_)) as u8;
                if v_isSharedCheck_1085_ == 0 {
                    v___x_1080_ = v_r_1076_;
                    v_isShared_1081_ = v_isSharedCheck_1085_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_1078_);
                    lean_inc(v_fst_1077_);
                    lean_dec(v_r_1076_);
                    v___x_1080_ = lean_box(0);
                    v_isShared_1081_ = v_isSharedCheck_1085_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1081_ == 0 {
                    v___x_1083_ = v___x_1080_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_fst_1077_);
                    lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_snd_1078_);
                    v___x_1083_ = v_reuseFailAlloc_1084_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1083_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_MergeSort_Internal_splitRevInTwo_x27___redArg___boxed(
    mut v_n_1086_: *mut LeanObject,
    mut v_l_1087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1088_: *mut LeanObject = core::ptr::null_mut();
    v_res_1088_ = l_List_MergeSort_Internal_splitRevInTwo_x27___redArg(v_n_1086_, v_l_1087_);
    lean_dec(v_n_1086_);
    return v_res_1088_;
}
pub unsafe fn l_List_MergeSort_Internal_splitRevInTwo_x27(
    mut v_00_u03b1_1089_: *mut LeanObject,
    mut v_n_1090_: *mut LeanObject,
    mut v_l_1091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    v___x_1092_ = l_List_MergeSort_Internal_splitRevInTwo_x27___redArg(v_n_1090_, v_l_1091_);
    return v___x_1092_;
}
pub unsafe fn l_List_MergeSort_Internal_splitRevInTwo_x27___boxed(
    mut v_00_u03b1_1093_: *mut LeanObject,
    mut v_n_1094_: *mut LeanObject,
    mut v_l_1095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1096_: *mut LeanObject = core::ptr::null_mut();
    v_res_1096_ =
        l_List_MergeSort_Internal_splitRevInTwo_x27(v_00_u03b1_1093_, v_n_1094_, v_l_1095_);
    lean_dec(v_n_1094_);
    return v_res_1096_;
}
pub unsafe fn _init_l_List_MergeSort_Internal_mergeSortTR_u2082___auto__1() -> *mut LeanObject {
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    v___x_1097_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58),
        core::ptr::addr_of_mut!(l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58_once),
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1___closed__58,
    );
    return v___x_1097_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(
    mut v_le_1098_: *mut LeanObject,
    mut v_n_1099_: *mut LeanObject,
    mut v_a_1100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1102_: u8 = 0;
    v_zero_1101_ = lean_unsigned_to_nat(0);
    v_isZero_1102_ = lean_nat_dec_eq(v_n_1099_, v_zero_1101_);
    if v_isZero_1102_ == 1 {
        lean_dec_ref(v_le_1098_);
        return v_a_1100_;
    } else {
        let mut v_one_1103_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_1104_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_1105_: u8 = 0;
        v_one_1103_ = lean_unsigned_to_nat(1);
        v_n_1104_ = lean_nat_sub(v_n_1099_, v_one_1103_);
        v_isZero_1105_ = lean_nat_dec_eq(v_n_1104_, v_zero_1101_);
        if v_isZero_1105_ == 1 {
            lean_dec(v_n_1104_);
            lean_dec_ref(v_le_1098_);
            return v_a_1100_;
        } else {
            let mut v_n_1106_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fst_1110_: *mut LeanObject = core::ptr::null_mut();
            let mut v_snd_1111_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
            v_n_1106_ = lean_nat_sub(v_n_1104_, v_one_1103_);
            lean_dec(v_n_1104_);
            v___x_1107_ = lean_unsigned_to_nat(2);
            v___x_1108_ = lean_nat_add(v_n_1106_, v___x_1107_);
            lean_dec(v_n_1106_);
            v___x_1109_ = l_List_MergeSort_Internal_splitRevInTwo___redArg(v___x_1108_, v_a_1100_);
            v_fst_1110_ = lean_ctor_get(v___x_1109_, 0);
            lean_inc(v_fst_1110_);
            v_snd_1111_ = lean_ctor_get(v___x_1109_, 1);
            lean_inc(v_snd_1111_);
            lean_dec_ref(v___x_1109_);
            v___x_1112_ = lean_nat_add(v___x_1108_, v_one_1103_);
            v___x_1113_ = lean_nat_shiftr(v___x_1112_, v_one_1103_);
            lean_dec(v___x_1112_);
            lean_inc_ref_n(v_le_1098_, 2);
            v___x_1114_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(v_le_1098_, v___x_1113_, v_fst_1110_);
            lean_dec(v___x_1113_);
            v___x_1115_ = lean_nat_shiftr(v___x_1108_, v_one_1103_);
            lean_dec(v___x_1108_);
            v___x_1116_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(v_le_1098_, v___x_1115_, v_snd_1111_);
            lean_dec(v___x_1115_);
            v___x_1117_ =
                l_List_MergeSort_Internal_mergeTR___redArg(v___x_1114_, v___x_1116_, v_le_1098_);
            return v___x_1117_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(
    mut v_le_1118_: *mut LeanObject,
    mut v_n_1119_: *mut LeanObject,
    mut v_a_1120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1122_: u8 = 0;
    v_zero_1121_ = lean_unsigned_to_nat(0);
    v_isZero_1122_ = lean_nat_dec_eq(v_n_1119_, v_zero_1121_);
    if v_isZero_1122_ == 1 {
        lean_dec_ref(v_le_1118_);
        return v_a_1120_;
    } else {
        let mut v_one_1123_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_1124_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_1125_: u8 = 0;
        v_one_1123_ = lean_unsigned_to_nat(1);
        v_n_1124_ = lean_nat_sub(v_n_1119_, v_one_1123_);
        v_isZero_1125_ = lean_nat_dec_eq(v_n_1124_, v_zero_1121_);
        if v_isZero_1125_ == 1 {
            lean_dec(v_n_1124_);
            lean_dec_ref(v_le_1118_);
            return v_a_1120_;
        } else {
            let mut v_n_1126_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fst_1130_: *mut LeanObject = core::ptr::null_mut();
            let mut v_snd_1131_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
            v_n_1126_ = lean_nat_sub(v_n_1124_, v_one_1123_);
            lean_dec(v_n_1124_);
            v___x_1127_ = lean_unsigned_to_nat(2);
            v___x_1128_ = lean_nat_add(v_n_1126_, v___x_1127_);
            lean_dec(v_n_1126_);
            v___x_1129_ =
                l_List_MergeSort_Internal_splitRevInTwo_x27___redArg(v___x_1128_, v_a_1120_);
            v_fst_1130_ = lean_ctor_get(v___x_1129_, 0);
            lean_inc(v_fst_1130_);
            v_snd_1131_ = lean_ctor_get(v___x_1129_, 1);
            lean_inc(v_snd_1131_);
            lean_dec_ref(v___x_1129_);
            v___x_1132_ = lean_nat_add(v___x_1128_, v_one_1123_);
            v___x_1133_ = lean_nat_shiftr(v___x_1132_, v_one_1123_);
            lean_dec(v___x_1132_);
            lean_inc_ref_n(v_le_1118_, 2);
            v___x_1134_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(v_le_1118_, v___x_1133_, v_snd_1131_);
            lean_dec(v___x_1133_);
            v___x_1135_ = lean_nat_shiftr(v___x_1128_, v_one_1123_);
            lean_dec(v___x_1128_);
            v___x_1136_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(v_le_1118_, v___x_1135_, v_fst_1130_);
            lean_dec(v___x_1135_);
            v___x_1137_ =
                l_List_MergeSort_Internal_mergeTR___redArg(v___x_1134_, v___x_1136_, v_le_1118_);
            return v___x_1137_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg___boxed(
    mut v_le_1138_: *mut LeanObject,
    mut v_n_1139_: *mut LeanObject,
    mut v_a_1140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1141_: *mut LeanObject = core::ptr::null_mut();
    v_res_1141_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(v_le_1138_, v_n_1139_, v_a_1140_);
    lean_dec(v_n_1139_);
    return v_res_1141_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg___boxed(
    mut v_le_1142_: *mut LeanObject,
    mut v_n_1143_: *mut LeanObject,
    mut v_a_1144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1145_: *mut LeanObject = core::ptr::null_mut();
    v_res_1145_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(v_le_1142_, v_n_1143_, v_a_1144_);
    lean_dec(v_n_1143_);
    return v_res_1145_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run(
    mut v_00_u03b1_1146_: *mut LeanObject,
    mut v_le_1147_: *mut LeanObject,
    mut v_n_1148_: *mut LeanObject,
    mut v_a_1149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    v___x_1150_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(v_le_1147_, v_n_1148_, v_a_1149_);
    return v___x_1150_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___boxed(
    mut v_00_u03b1_1151_: *mut LeanObject,
    mut v_le_1152_: *mut LeanObject,
    mut v_n_1153_: *mut LeanObject,
    mut v_a_1154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1155_: *mut LeanObject = core::ptr::null_mut();
    v_res_1155_ =
        l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run(
            v_00_u03b1_1151_,
            v_le_1152_,
            v_n_1153_,
            v_a_1154_,
        );
    lean_dec(v_n_1153_);
    return v_res_1155_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27(
    mut v_00_u03b1_1156_: *mut LeanObject,
    mut v_le_1157_: *mut LeanObject,
    mut v_n_1158_: *mut LeanObject,
    mut v_a_1159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    v___x_1160_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___redArg(v_le_1157_, v_n_1158_, v_a_1159_);
    return v___x_1160_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27___boxed(
    mut v_00_u03b1_1161_: *mut LeanObject,
    mut v_le_1162_: *mut LeanObject,
    mut v_n_1163_: *mut LeanObject,
    mut v_a_1164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1165_: *mut LeanObject = core::ptr::null_mut();
    v_res_1165_ =
        l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27(
            v_00_u03b1_1161_,
            v_le_1162_,
            v_n_1163_,
            v_a_1164_,
        );
    lean_dec(v_n_1163_);
    return v_res_1165_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27_match__1_splitter___redArg(
    mut v_x_1166_: *mut LeanObject,
    mut v_h__1_1167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1168_ = lean_ctor_get(v_x_1166_, 0);
    lean_inc(v_fst_1168_);
    v_snd_1169_ = lean_ctor_get(v_x_1166_, 1);
    lean_inc(v_snd_1169_);
    lean_dec_ref(v_x_1166_);
    v___x_1170_ = lean_apply_2(v_h__1_1167_, v_fst_1168_, v_snd_1169_);
    return v___x_1170_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27_match__1_splitter(
    mut v_00_u03b1_1171_: *mut LeanObject,
    mut v_n_1172_: *mut LeanObject,
    mut v_motive_1173_: *mut LeanObject,
    mut v_x_1174_: *mut LeanObject,
    mut v_h__1_1175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1176_ = lean_ctor_get(v_x_1174_, 0);
    lean_inc(v_fst_1176_);
    v_snd_1177_ = lean_ctor_get(v_x_1174_, 1);
    lean_inc(v_snd_1177_);
    lean_dec_ref(v_x_1174_);
    v___x_1178_ = lean_apply_2(v_h__1_1175_, v_fst_1176_, v_snd_1177_);
    return v___x_1178_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27_match__1_splitter___boxed(
    mut v_00_u03b1_1179_: *mut LeanObject,
    mut v_n_1180_: *mut LeanObject,
    mut v_motive_1181_: *mut LeanObject,
    mut v_x_1182_: *mut LeanObject,
    mut v_h__1_1183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1184_: *mut LeanObject = core::ptr::null_mut();
    v_res_1184_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run_x27_match__1_splitter(v_00_u03b1_1179_, v_n_1180_, v_motive_1181_, v_x_1182_, v_h__1_1183_);
    lean_dec(v_n_1180_);
    return v_res_1184_;
}
pub unsafe fn l_List_MergeSort_Internal_mergeSortTR_u2082___redArg(
    mut v_l_1185_: *mut LeanObject,
    mut v_le_1186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
    v___x_1187_ = l_List_lengthTR___redArg(v_l_1185_);
    v___x_1188_ = l___private_Init_Data_List_Sort_Impl_0__List_MergeSort_Internal_mergeSortTR_u2082_run___redArg(v_le_1186_, v___x_1187_, v_l_1185_);
    lean_dec(v___x_1187_);
    return v___x_1188_;
}
pub unsafe fn l_List_MergeSort_Internal_mergeSortTR_u2082(
    mut v_00_u03b1_1189_: *mut LeanObject,
    mut v_l_1190_: *mut LeanObject,
    mut v_le_1191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    v___x_1192_ = l_List_MergeSort_Internal_mergeSortTR_u2082___redArg(v_l_1190_, v_le_1191_);
    return v___x_1192_;
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_mergeSort_match__1_splitter___redArg(
    mut v_x_1193_: *mut LeanObject,
    mut v_x_1194_: *mut LeanObject,
    mut v_h__1_1195_: *mut LeanObject,
    mut v_h__2_1196_: *mut LeanObject,
    mut v_h__3_1197_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1193_) == 0 {
        let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_1197_);
        lean_dec(v_h__2_1196_);
        v___x_1198_ = lean_apply_1(v_h__1_1195_, v_x_1194_);
        return v___x_1198_;
    } else {
        let mut v_tail_1199_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1195_);
        v_tail_1199_ = lean_ctor_get(v_x_1193_, 1);
        if lean_obj_tag(v_tail_1199_) == 0 {
            let mut v_head_1200_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1197_);
            v_head_1200_ = lean_ctor_get(v_x_1193_, 0);
            lean_inc(v_head_1200_);
            lean_dec_ref_known(v_x_1193_, 2);
            v___x_1201_ = lean_apply_2(v_h__2_1196_, v_head_1200_, v_x_1194_);
            return v___x_1201_;
        } else {
            let mut v_head_1202_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_1203_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_1204_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_tail_1199_);
            lean_dec(v_h__2_1196_);
            v_head_1202_ = lean_ctor_get(v_x_1193_, 0);
            lean_inc(v_head_1202_);
            lean_dec_ref_known(v_x_1193_, 2);
            v_head_1203_ = lean_ctor_get(v_tail_1199_, 0);
            lean_inc(v_head_1203_);
            v_tail_1204_ = lean_ctor_get(v_tail_1199_, 1);
            lean_inc(v_tail_1204_);
            lean_dec_ref_known(v_tail_1199_, 2);
            v___x_1205_ = lean_apply_4(
                v_h__3_1197_,
                v_head_1202_,
                v_head_1203_,
                v_tail_1204_,
                v_x_1194_,
            );
            return v___x_1205_;
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Sort_Impl_0__List_mergeSort_match__1_splitter(
    mut v_00_u03b1_1206_: *mut LeanObject,
    mut v_motive_1207_: *mut LeanObject,
    mut v_x_1208_: *mut LeanObject,
    mut v_x_1209_: *mut LeanObject,
    mut v_h__1_1210_: *mut LeanObject,
    mut v_h__2_1211_: *mut LeanObject,
    mut v_h__3_1212_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1208_) == 0 {
        let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_1212_);
        lean_dec(v_h__2_1211_);
        v___x_1213_ = lean_apply_1(v_h__1_1210_, v_x_1209_);
        return v___x_1213_;
    } else {
        let mut v_tail_1214_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1210_);
        v_tail_1214_ = lean_ctor_get(v_x_1208_, 1);
        if lean_obj_tag(v_tail_1214_) == 0 {
            let mut v_head_1215_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1212_);
            v_head_1215_ = lean_ctor_get(v_x_1208_, 0);
            lean_inc(v_head_1215_);
            lean_dec_ref_known(v_x_1208_, 2);
            v___x_1216_ = lean_apply_2(v_h__2_1211_, v_head_1215_, v_x_1209_);
            return v___x_1216_;
        } else {
            let mut v_head_1217_: *mut LeanObject = core::ptr::null_mut();
            let mut v_head_1218_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tail_1219_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_tail_1214_);
            lean_dec(v_h__2_1211_);
            v_head_1217_ = lean_ctor_get(v_x_1208_, 0);
            lean_inc(v_head_1217_);
            lean_dec_ref_known(v_x_1208_, 2);
            v_head_1218_ = lean_ctor_get(v_tail_1214_, 0);
            lean_inc(v_head_1218_);
            v_tail_1219_ = lean_ctor_get(v_tail_1214_, 1);
            lean_inc(v_tail_1219_);
            lean_dec_ref_known(v_tail_1214_, 2);
            v___x_1220_ = lean_apply_4(
                v_h__3_1212_,
                v_head_1217_,
                v_head_1218_,
                v_tail_1219_,
                v_x_1209_,
            );
            return v___x_1220_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Sort_Impl(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Sort_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sort_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Sort_Impl(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_List_MergeSort_Internal_mergeSortTR___auto__1 =
        _init_l_List_MergeSort_Internal_mergeSortTR___auto__1();
    lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR___auto__1);
    l_List_MergeSort_Internal_mergeSortTR_u2082___auto__1 =
        _init_l_List_MergeSort_Internal_mergeSortTR_u2082___auto__1();
    lean_mark_persistent(l_List_MergeSort_Internal_mergeSortTR_u2082___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Sort_Impl(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Sort_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Sort_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sort_Impl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Sort_Impl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_List_Sort_Impl(builtin);
}

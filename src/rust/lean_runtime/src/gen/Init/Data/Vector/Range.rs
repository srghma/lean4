// Lean compiler output
// Module: Init.Data.Vector.Range
// Imports: Init.Data.Array.Basic Init.Data.Vector.Basic Init.BinderPredicates Init.Data.Vector.Basic Init.ByCases Init.Data.Array.Find Init.Data.Array.Range Init.Data.Vector.MapIdx Init.Data.Vector.Zip
use crate::r#gen::Init::BinderPredicates::{
    initialize_Init_BinderPredicates, runtime_initialize_Init_BinderPredicates,
};
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::Array::Find::{
    initialize_Init_Data_Array_Find, runtime_initialize_Init_Data_Array_Find,
};
use crate::r#gen::Init::Data::Array::Range::{
    initialize_Init_Data_Array_Range, runtime_initialize_Init_Data_Array_Range,
};
use crate::r#gen::Init::Data::Vector::Basic::{
    initialize_Init_Data_Vector_Basic, runtime_initialize_Init_Data_Vector_Basic,
};
use crate::r#gen::Init::Data::Vector::MapIdx::{
    initialize_Init_Data_Vector_MapIdx, runtime_initialize_Init_Data_Vector_MapIdx,
};
use crate::r#gen::Init::Data::Vector::Zip::{
    initialize_Init_Data_Vector_Zip, runtime_initialize_Init_Data_Vector_Zip,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_mkAtom};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_set, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once,
};
pub static l_Vector_count__range_x27___auto__1___closed__0_value: LeanStringObject<5> =
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
static mut l_Vector_count__range_x27___auto__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__0_value) as *mut LeanObject;
pub static l_Vector_count__range_x27___auto__1___closed__1_value: LeanStringObject<7> =
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
static mut l_Vector_count__range_x27___auto__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__1_value) as *mut LeanObject;
pub static l_Vector_count__range_x27___auto__1___closed__2_value: LeanStringObject<7> =
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
static mut l_Vector_count__range_x27___auto__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__2_value) as *mut LeanObject;
pub static l_Vector_count__range_x27___auto__1___closed__3_value: LeanStringObject<10> =
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
static mut l_Vector_count__range_x27___auto__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__3_value) as *mut LeanObject;
static l_Vector_count__range_x27___auto__1___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Vector_count__range_x27___auto__1___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Vector_count__range_x27___auto__1___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Vector_count__range_x27___auto__1___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__3_value)
                as *mut LeanObject,
            8504843326314613972 as *mut LeanObject,
        ],
    };
static mut l_Vector_count__range_x27___auto__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__4_value) as *mut LeanObject;
pub static l_Vector_count__range_x27___auto__1___closed__5_value: LeanArrayObject<0> =
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
static mut l_Vector_count__range_x27___auto__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__5_value) as *mut LeanObject;
pub static l_Vector_count__range_x27___auto__1___closed__6_value: LeanStringObject<19> =
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
static mut l_Vector_count__range_x27___auto__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__6_value) as *mut LeanObject;
static l_Vector_count__range_x27___auto__1___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Vector_count__range_x27___auto__1___closed__7_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Vector_count__range_x27___auto__1___closed__7_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Vector_count__range_x27___auto__1___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__7_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__6_value)
                as *mut LeanObject,
            17228437386856258271 as *mut LeanObject,
        ],
    };
static mut l_Vector_count__range_x27___auto__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__7_value) as *mut LeanObject;
pub static l_Vector_count__range_x27___auto__1___closed__8_value: LeanStringObject<5> =
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
static mut l_Vector_count__range_x27___auto__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__8_value) as *mut LeanObject;
pub static l_Vector_count__range_x27___auto__1___closed__9_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__8_value)
                as *mut LeanObject,
            9855511589286918680 as *mut LeanObject,
        ],
    };
static mut l_Vector_count__range_x27___auto__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__9_value) as *mut LeanObject;
pub static l_Vector_count__range_x27___auto__1___closed__10_value: LeanStringObject<5> =
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
static mut l_Vector_count__range_x27___auto__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__10_value) as *mut LeanObject;
static l_Vector_count__range_x27___auto__1___closed__11_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Vector_count__range_x27___auto__1___closed__11_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__11_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Vector_count__range_x27___auto__1___closed__11_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__11_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Vector_count__range_x27___auto__1___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__11_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__10_value)
                as *mut LeanObject,
            12783917532758215986 as *mut LeanObject,
        ],
    };
static mut l_Vector_count__range_x27___auto__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__11_value) as *mut LeanObject;
static mut l_Vector_count__range_x27___auto__1___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Vector_count__range_x27___auto__1___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Vector_count__range_x27___auto__1___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Vector_count__range_x27___auto__1___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Vector_count__range_x27___auto__1___closed__14_value: LeanStringObject<10> =
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
static mut l_Vector_count__range_x27___auto__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__14_value) as *mut LeanObject;
static l_Vector_count__range_x27___auto__1___closed__15_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Vector_count__range_x27___auto__1___closed__15_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__15_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Vector_count__range_x27___auto__1___closed__15_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__15_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Vector_count__range_x27___auto__1___closed__15_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__15_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__14_value)
                as *mut LeanObject,
            3488656302031949961 as *mut LeanObject,
        ],
    };
static mut l_Vector_count__range_x27___auto__1___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__15_value) as *mut LeanObject;
pub static l_Vector_count__range_x27___auto__1___closed__16_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Vector_count__range_x27___auto__1___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Vector_count__range_x27___auto__1___closed__16_value) as *mut LeanObject;
static mut l_Vector_count__range_x27___auto__1___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Vector_count__range_x27___auto__1___closed__17: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Vector_count__range_x27___auto__1___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Vector_count__range_x27___auto__1___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Vector_count__range_x27___auto__1___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Vector_count__range_x27___auto__1___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Vector_count__range_x27___auto__1___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Vector_count__range_x27___auto__1___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Vector_count__range_x27___auto__1___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Vector_count__range_x27___auto__1___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Vector_count__range_x27___auto__1___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Vector_count__range_x27___auto__1___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Vector_count__range_x27___auto__1___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Vector_count__range_x27___auto__1___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Vector_count__range_x27___auto__1___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Vector_count__range_x27___auto__1___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Vector_count__range_x27___auto__1___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Vector_count__range_x27___auto__1___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Vector_count__range_x27___auto__1___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Vector_count__range_x27___auto__1___closed__26: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Vector_count__range_x27___auto__1___closed__27_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Vector_count__range_x27___auto__1___closed__27: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Vector_count__range_x27___auto__1___closed__28_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Vector_count__range_x27___auto__1___closed__28: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Vector_count__range_x27___auto__1___closed__29_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Vector_count__range_x27___auto__1___closed__29: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Vector_count__range_x27___auto__1___closed__30_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Vector_count__range_x27___auto__1___closed__30: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Vector_count__range_x27___auto__1: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Vector_count__range_x27___auto__1___closed__12() -> *mut LeanObject {
    let mut v___x_116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_117_: *mut LeanObject = core::ptr::null_mut();
    v___x_116_ = l_Vector_count__range_x27___auto__1___closed__10;
    v___x_117_ = l_Lean_mkAtom(v___x_116_);
    return v___x_117_;
}
pub unsafe fn _init_l_Vector_count__range_x27___auto__1___closed__13() -> *mut LeanObject {
    let mut v___x_118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_120_: *mut LeanObject = core::ptr::null_mut();
    v___x_118_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__12),
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__12_once),
        _init_l_Vector_count__range_x27___auto__1___closed__12,
    );
    v___x_119_ = l_Vector_count__range_x27___auto__1___closed__5;
    v___x_120_ = lean_array_push(v___x_119_, v___x_118_);
    return v___x_120_;
}
pub unsafe fn _init_l_Vector_count__range_x27___auto__1___closed__17() -> *mut LeanObject {
    let mut v___x_131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_133_: *mut LeanObject = core::ptr::null_mut();
    v___x_131_ = l_Vector_count__range_x27___auto__1___closed__16;
    v___x_132_ = l_Vector_count__range_x27___auto__1___closed__5;
    v___x_133_ = lean_array_push(v___x_132_, v___x_131_);
    return v___x_133_;
}
pub unsafe fn _init_l_Vector_count__range_x27___auto__1___closed__18() -> *mut LeanObject {
    let mut v___x_134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_137_: *mut LeanObject = core::ptr::null_mut();
    v___x_134_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__17),
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__17_once),
        _init_l_Vector_count__range_x27___auto__1___closed__17,
    );
    v___x_135_ = l_Vector_count__range_x27___auto__1___closed__15;
    v___x_136_ = lean_box(2);
    v___x_137_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_137_, 0, v___x_136_);
    lean_ctor_set(v___x_137_, 1, v___x_135_);
    lean_ctor_set(v___x_137_, 2, v___x_134_);
    return v___x_137_;
}
pub unsafe fn _init_l_Vector_count__range_x27___auto__1___closed__19() -> *mut LeanObject {
    let mut v___x_138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
    v___x_138_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__18),
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__18_once),
        _init_l_Vector_count__range_x27___auto__1___closed__18,
    );
    v___x_139_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__13),
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__13_once),
        _init_l_Vector_count__range_x27___auto__1___closed__13,
    );
    v___x_140_ = lean_array_push(v___x_139_, v___x_138_);
    return v___x_140_;
}
pub unsafe fn _init_l_Vector_count__range_x27___auto__1___closed__20() -> *mut LeanObject {
    let mut v___x_141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_143_: *mut LeanObject = core::ptr::null_mut();
    v___x_141_ = l_Vector_count__range_x27___auto__1___closed__16;
    v___x_142_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__19),
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__19_once),
        _init_l_Vector_count__range_x27___auto__1___closed__19,
    );
    v___x_143_ = lean_array_push(v___x_142_, v___x_141_);
    return v___x_143_;
}
pub unsafe fn _init_l_Vector_count__range_x27___auto__1___closed__21() -> *mut LeanObject {
    let mut v___x_144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_146_: *mut LeanObject = core::ptr::null_mut();
    v___x_144_ = l_Vector_count__range_x27___auto__1___closed__16;
    v___x_145_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__20),
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__20_once),
        _init_l_Vector_count__range_x27___auto__1___closed__20,
    );
    v___x_146_ = lean_array_push(v___x_145_, v___x_144_);
    return v___x_146_;
}
pub unsafe fn _init_l_Vector_count__range_x27___auto__1___closed__22() -> *mut LeanObject {
    let mut v___x_147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_149_: *mut LeanObject = core::ptr::null_mut();
    v___x_147_ = l_Vector_count__range_x27___auto__1___closed__16;
    v___x_148_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__21),
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__21_once),
        _init_l_Vector_count__range_x27___auto__1___closed__21,
    );
    v___x_149_ = lean_array_push(v___x_148_, v___x_147_);
    return v___x_149_;
}
pub unsafe fn _init_l_Vector_count__range_x27___auto__1___closed__23() -> *mut LeanObject {
    let mut v___x_150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_152_: *mut LeanObject = core::ptr::null_mut();
    v___x_150_ = l_Vector_count__range_x27___auto__1___closed__16;
    v___x_151_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__22),
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__22_once),
        _init_l_Vector_count__range_x27___auto__1___closed__22,
    );
    v___x_152_ = lean_array_push(v___x_151_, v___x_150_);
    return v___x_152_;
}
pub unsafe fn _init_l_Vector_count__range_x27___auto__1___closed__24() -> *mut LeanObject {
    let mut v___x_153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_156_: *mut LeanObject = core::ptr::null_mut();
    v___x_153_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__23),
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__23_once),
        _init_l_Vector_count__range_x27___auto__1___closed__23,
    );
    v___x_154_ = l_Vector_count__range_x27___auto__1___closed__11;
    v___x_155_ = lean_box(2);
    v___x_156_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_156_, 0, v___x_155_);
    lean_ctor_set(v___x_156_, 1, v___x_154_);
    lean_ctor_set(v___x_156_, 2, v___x_153_);
    return v___x_156_;
}
pub unsafe fn _init_l_Vector_count__range_x27___auto__1___closed__25() -> *mut LeanObject {
    let mut v___x_157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut LeanObject = core::ptr::null_mut();
    v___x_157_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__24),
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__24_once),
        _init_l_Vector_count__range_x27___auto__1___closed__24,
    );
    v___x_158_ = l_Vector_count__range_x27___auto__1___closed__5;
    v___x_159_ = lean_array_push(v___x_158_, v___x_157_);
    return v___x_159_;
}
pub unsafe fn _init_l_Vector_count__range_x27___auto__1___closed__26() -> *mut LeanObject {
    let mut v___x_160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_163_: *mut LeanObject = core::ptr::null_mut();
    v___x_160_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__25),
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__25_once),
        _init_l_Vector_count__range_x27___auto__1___closed__25,
    );
    v___x_161_ = l_Vector_count__range_x27___auto__1___closed__9;
    v___x_162_ = lean_box(2);
    v___x_163_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_163_, 0, v___x_162_);
    lean_ctor_set(v___x_163_, 1, v___x_161_);
    lean_ctor_set(v___x_163_, 2, v___x_160_);
    return v___x_163_;
}
pub unsafe fn _init_l_Vector_count__range_x27___auto__1___closed__27() -> *mut LeanObject {
    let mut v___x_164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_166_: *mut LeanObject = core::ptr::null_mut();
    v___x_164_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__26),
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__26_once),
        _init_l_Vector_count__range_x27___auto__1___closed__26,
    );
    v___x_165_ = l_Vector_count__range_x27___auto__1___closed__5;
    v___x_166_ = lean_array_push(v___x_165_, v___x_164_);
    return v___x_166_;
}
pub unsafe fn _init_l_Vector_count__range_x27___auto__1___closed__28() -> *mut LeanObject {
    let mut v___x_167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut LeanObject = core::ptr::null_mut();
    v___x_167_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__27),
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__27_once),
        _init_l_Vector_count__range_x27___auto__1___closed__27,
    );
    v___x_168_ = l_Vector_count__range_x27___auto__1___closed__7;
    v___x_169_ = lean_box(2);
    v___x_170_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_170_, 0, v___x_169_);
    lean_ctor_set(v___x_170_, 1, v___x_168_);
    lean_ctor_set(v___x_170_, 2, v___x_167_);
    return v___x_170_;
}
pub unsafe fn _init_l_Vector_count__range_x27___auto__1___closed__29() -> *mut LeanObject {
    let mut v___x_171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut LeanObject = core::ptr::null_mut();
    v___x_171_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__28),
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__28_once),
        _init_l_Vector_count__range_x27___auto__1___closed__28,
    );
    v___x_172_ = l_Vector_count__range_x27___auto__1___closed__5;
    v___x_173_ = lean_array_push(v___x_172_, v___x_171_);
    return v___x_173_;
}
pub unsafe fn _init_l_Vector_count__range_x27___auto__1___closed__30() -> *mut LeanObject {
    let mut v___x_174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_177_: *mut LeanObject = core::ptr::null_mut();
    v___x_174_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__29),
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__29_once),
        _init_l_Vector_count__range_x27___auto__1___closed__29,
    );
    v___x_175_ = l_Vector_count__range_x27___auto__1___closed__4;
    v___x_176_ = lean_box(2);
    v___x_177_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_177_, 0, v___x_176_);
    lean_ctor_set(v___x_177_, 1, v___x_175_);
    lean_ctor_set(v___x_177_, 2, v___x_174_);
    return v___x_177_;
}
pub unsafe fn _init_l_Vector_count__range_x27___auto__1() -> *mut LeanObject {
    let mut v___x_178_: *mut LeanObject = core::ptr::null_mut();
    v___x_178_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__30),
        core::ptr::addr_of_mut!(l_Vector_count__range_x27___auto__1___closed__30_once),
        _init_l_Vector_count__range_x27___auto__1___closed__30,
    );
    return v___x_178_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Vector_Range(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_BinderPredicates(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Find(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Range(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_MapIdx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Vector_Range(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    l_Vector_count__range_x27___auto__1 = _init_l_Vector_count__range_x27___auto__1();
    lean_mark_persistent(l_Vector_count__range_x27___auto__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Vector_Range(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_BinderPredicates(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Find(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Range(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Vector_MapIdx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Range(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Vector_Range(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Vector_Range(builtin);
}

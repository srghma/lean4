// Lean compiler output
// Module: Std.Time.Format.DateFormat
// Imports: Init.Data.Vector.Extract Std.Time.Date.Unit.Weekday
use crate::r#gen::Init::Data::Vector::Extract::{
    initialize_Init_Data_Vector_Extract, runtime_initialize_Init_Data_Vector_Extract,
};
use crate::r#gen::Std::Time::Date::Unit::Weekday::{
    initialize_Std_Time_Date_Unit_Weekday, runtime_initialize_Std_Time_Date_Unit_Weekday,
};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub static l_Std_Time_DateFormatSymbols_enUS___closed__0_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [74, 97, 110, 117, 97, 114, 121, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__1_value: LeanStringObject<9> =
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
        m_data: [70, 101, 98, 114, 117, 97, 114, 121, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__1_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__2_value: LeanStringObject<6> =
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
        m_data: [77, 97, 114, 99, 104, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__2_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__3_value: LeanStringObject<6> =
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
        m_data: [65, 112, 114, 105, 108, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__3_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__4_value: LeanStringObject<4> =
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
        m_data: [77, 97, 121, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__4_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__5_value: LeanStringObject<5> =
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
        m_data: [74, 117, 110, 101, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__5_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__6_value: LeanStringObject<5> =
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
        m_data: [74, 117, 108, 121, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__6_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__7_value: LeanStringObject<7> =
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
        m_data: [65, 117, 103, 117, 115, 116, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__7_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__8_value: LeanStringObject<10> =
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
        m_data: [83, 101, 112, 116, 101, 109, 98, 101, 114, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__8_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__9_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [79, 99, 116, 111, 98, 101, 114, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__9_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__10_value: LeanStringObject<9> =
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
        m_data: [78, 111, 118, 101, 109, 98, 101, 114, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__10_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__11_value: LeanStringObject<9> =
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
        m_data: [68, 101, 99, 101, 109, 98, 101, 114, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__11_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__12_value: LeanArrayObject<12> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 12) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 12,
        m_capacity: 12,
        m_data: [
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__9_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__10_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__12_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__13_value: LeanStringObject<4> =
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
        m_data: [74, 97, 110, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__13_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__14_value: LeanStringObject<4> =
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
        m_data: [70, 101, 98, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__14_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__15_value: LeanStringObject<4> =
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
        m_data: [77, 97, 114, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__15_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__16_value: LeanStringObject<4> =
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
        m_data: [65, 112, 114, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__16_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__17_value: LeanStringObject<4> =
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
        m_data: [74, 117, 110, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__17_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__18_value: LeanStringObject<4> =
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
        m_data: [74, 117, 108, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__18_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__19_value: LeanStringObject<4> =
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
        m_data: [65, 117, 103, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__19_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__20_value: LeanStringObject<4> =
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
        m_data: [83, 101, 112, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__20_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__21_value: LeanStringObject<4> =
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
        m_data: [79, 99, 116, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__21_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__22_value: LeanStringObject<4> =
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
        m_data: [78, 111, 118, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__22_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__23_value: LeanStringObject<4> =
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
        m_data: [68, 101, 99, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__23_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__24_value: LeanArrayObject<12> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 12) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 12,
        m_capacity: 12,
        m_data: [
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__13_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__14_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__15_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__16_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__17_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__18_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__19_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__20_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__21_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__22_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__23_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__24_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__25_value: LeanStringObject<2> =
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
        m_data: [74, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__25_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__26_value: LeanStringObject<2> =
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
        m_data: [70, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__26_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__27_value: LeanStringObject<2> =
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
        m_data: [77, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__27_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__28_value: LeanStringObject<2> =
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
        m_data: [65, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__28_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__29_value: LeanStringObject<2> =
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
        m_data: [83, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__29_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__30_value: LeanStringObject<2> =
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
        m_data: [79, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__30_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__31_value: LeanStringObject<2> =
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
        m_data: [78, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__31_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__32_value: LeanStringObject<2> =
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
        m_data: [68, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__32_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__33_value: LeanArrayObject<12> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 12) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 12,
        m_capacity: 12,
        m_data: [
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__25_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__26_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__27_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__28_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__27_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__25_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__25_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__28_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__29_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__30_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__31_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__32_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__33_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__34_value: LeanStringObject<7> =
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
        m_data: [77, 111, 110, 100, 97, 121, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__34_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__35_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [84, 117, 101, 115, 100, 97, 121, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__35_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__36_value: LeanStringObject<10> =
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
        m_data: [87, 101, 100, 110, 101, 115, 100, 97, 121, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__36_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__37_value: LeanStringObject<9> =
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
        m_data: [84, 104, 117, 114, 115, 100, 97, 121, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__37_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__38_value: LeanStringObject<7> =
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
        m_data: [70, 114, 105, 100, 97, 121, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__38_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__39_value: LeanStringObject<9> =
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
        m_data: [83, 97, 116, 117, 114, 100, 97, 121, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__39_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__40_value: LeanStringObject<7> =
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
        m_data: [83, 117, 110, 100, 97, 121, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__40_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__41_value: LeanArrayObject<7> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 7) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 7,
        m_capacity: 7,
        m_data: [
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__34_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__35_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__36_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__37_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__38_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__39_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__40_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__41_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__42_value: LeanStringObject<4> =
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
        m_data: [77, 111, 110, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__42: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__42_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__43_value: LeanStringObject<4> =
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
        m_data: [84, 117, 101, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__43: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__43_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__44_value: LeanStringObject<4> =
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
        m_data: [87, 101, 100, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__44: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__44_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__45_value: LeanStringObject<4> =
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
        m_data: [84, 104, 117, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__45: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__45_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__46_value: LeanStringObject<4> =
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
        m_data: [70, 114, 105, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__46: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__46_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__47_value: LeanStringObject<4> =
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
        m_data: [83, 97, 116, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__47: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__47_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__48_value: LeanStringObject<4> =
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
        m_data: [83, 117, 110, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__48: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__48_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__49_value: LeanArrayObject<7> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 7) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 7,
        m_capacity: 7,
        m_data: [
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__42_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__43_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__44_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__45_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__46_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__47_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__48_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__49: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__49_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__50_value: LeanStringObject<2> =
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
        m_data: [84, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__50: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__50_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__51_value: LeanStringObject<2> =
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
        m_data: [87, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__51: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__51_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__52_value: LeanArrayObject<7> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 7) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 7,
        m_capacity: 7,
        m_data: [
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__27_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__50_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__51_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__50_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__26_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__29_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__29_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__52: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__52_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__53_value: LeanStringObject<4> =
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
        m_data: [66, 67, 69, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__53: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__53_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__54_value: LeanStringObject<3> =
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
        m_data: [67, 69, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__54: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__54_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__55_value: LeanArrayObject<2> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 2,
        m_capacity: 2,
        m_data: [
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__53_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__54_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__55: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__55_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__56_value: LeanStringObject<18> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            66, 101, 102, 111, 114, 101, 32, 67, 111, 109, 109, 111, 110, 32, 69, 114, 97, 0,
        ],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__56: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__56_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__57_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [67, 111, 109, 109, 111, 110, 32, 69, 114, 97, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__57: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__57_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__58_value: LeanArrayObject<2> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 2,
        m_capacity: 2,
        m_data: [
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__56_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__57_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__58: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__58_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__59_value: LeanStringObject<2> =
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
        m_data: [66, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__59: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__59_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__60_value: LeanStringObject<2> =
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
        m_data: [67, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__60: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__60_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__61_value: LeanArrayObject<2> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 2,
        m_capacity: 2,
        m_data: [
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__59_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__60_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__61: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__61_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__62_value: LeanStringObject<3> =
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
        m_data: [81, 49, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__62: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__62_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__63_value: LeanStringObject<3> =
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
        m_data: [81, 50, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__63: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__63_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__64_value: LeanStringObject<3> =
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
        m_data: [81, 51, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__64: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__64_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__65_value: LeanStringObject<3> =
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
        m_data: [81, 52, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__65: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__65_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__66_value: LeanArrayObject<4> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 4,
        m_capacity: 4,
        m_data: [
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__62_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__63_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__64_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__65_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__66: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__66_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__67_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [49, 115, 116, 32, 113, 117, 97, 114, 116, 101, 114, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__67: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__67_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__68_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [50, 110, 100, 32, 113, 117, 97, 114, 116, 101, 114, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__68: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__68_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__69_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [51, 114, 100, 32, 113, 117, 97, 114, 116, 101, 114, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__69: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__69_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__70_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [52, 116, 104, 32, 113, 117, 97, 114, 116, 101, 114, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__70: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__70_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__71_value: LeanArrayObject<4> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 4,
        m_capacity: 4,
        m_data: [
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__67_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__68_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__69_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__70_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__71: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__71_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__72_value: LeanStringObject<2> =
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
        m_data: [49, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__72: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__72_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__73_value: LeanStringObject<2> =
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
        m_data: [50, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__73: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__73_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__74_value: LeanStringObject<2> =
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
        m_data: [51, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__74: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__74_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__75_value: LeanStringObject<2> =
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
        m_data: [52, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__75: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__75_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__76_value: LeanArrayObject<4> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 4,
        m_capacity: 4,
        m_data: [
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__72_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__73_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__74_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__75_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__76: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__76_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__77_value: LeanStringObject<3> =
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
        m_data: [65, 77, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__77: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__77_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__78_value: LeanStringObject<3> =
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
        m_data: [80, 77, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__78: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__78_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__79_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            65, 110, 116, 101, 32, 77, 101, 114, 105, 100, 105, 101, 109, 0,
        ],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__79: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__79_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__80_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            80, 111, 115, 116, 32, 77, 101, 114, 105, 100, 105, 101, 109, 0,
        ],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__80: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__80_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__81_value: LeanStringObject<2> =
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
        m_data: [80, 0],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__81: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__81_value) as *mut LeanObject;
pub static l_Std_Time_DateFormatSymbols_enUS___closed__82_value: LeanCtorObject<18> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 18
                + 0) as u16,
            other: 18,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__12_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__24_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__33_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__41_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__49_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__52_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__55_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__58_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__61_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__66_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__71_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__76_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__77_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__78_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__79_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__80_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__28_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__81_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_DateFormatSymbols_enUS___closed__82: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__82_value) as *mut LeanObject;
pub static mut l_Std_Time_DateFormatSymbols_enUS: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__82_value) as *mut LeanObject;
pub static l_Std_Time_DateFormat_enUS___closed__0_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_DateFormatSymbols_enUS___closed__82_value)
            as *mut LeanObject,
        6 as *mut LeanObject,
    ],
};
static mut l_Std_Time_DateFormat_enUS___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormat_enUS___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_DateFormat_enUS: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateFormat_enUS___closed__0_value) as *mut LeanObject;
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Format_DateFormat(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Vector_Extract(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Date_Unit_Weekday(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Format_DateFormat(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Format_DateFormat(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Vector_Extract(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Time_Date_Unit_Weekday(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Format_DateFormat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Time_Format_DateFormat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Time_Format_DateFormat(builtin);
}

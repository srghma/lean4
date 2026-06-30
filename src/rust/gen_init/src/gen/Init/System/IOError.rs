// Lean compiler output
// Module: Init.System.IOError
// Imports: Init.Data.ToString.Basic Init.Data.String.Modify
use crate::ffi::{
    lean_string_append, lean_string_utf8_get, lean_string_utf8_set, lean_uint32_add,
    lean_uint32_dec_le, lean_uint32_to_nat,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Modify::{
    initialize_Init_Data_String_Modify, runtime_initialize_Init_Data_String_Modify,
};
use crate::r#gen::Init::Data::ToString::Basic::{
    initialize_Init_Data_ToString_Basic, runtime_initialize_Init_Data_ToString_Basic,
};
pub static l_instInhabitedError___closed__0_value: leanh::LeanStringObject<37> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 37,
        m_capacity: 37,
        m_length: 36,
        m_data: [
            40, 96, 73, 110, 104, 97, 98, 105, 116, 101, 100, 46, 100, 101, 102, 97, 117, 108, 116,
            96, 32, 102, 111, 114, 32, 96, 73, 79, 46, 69, 114, 114, 111, 114, 96, 41, 0,
        ],
    };
static mut l_instInhabitedError___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instInhabitedError___closed__0_value) as *mut leanh::LeanObject;
pub static l_instInhabitedError___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 18,
        },
        m_objs: [core::ptr::addr_of!(l_instInhabitedError___closed__0_value)
            as *mut leanh::LeanObject],
    };
static mut l_instInhabitedError___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instInhabitedError___closed__1_value) as *mut leanh::LeanObject;
pub static mut l_instInhabitedError: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instInhabitedError___closed__1_value) as *mut leanh::LeanObject;
pub static l_instCoeStringError___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: lean_mk_io_user_error as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instCoeStringError___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instCoeStringError___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instCoeStringError: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instCoeStringError___closed__0_value) as *mut leanh::LeanObject;
pub static l_IO_Error_fopenErrorToString___closed__0_value: leanh::LeanStringObject<15> =
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
            32, 40, 101, 114, 114, 111, 114, 32, 99, 111, 100, 101, 58, 32, 0,
        ],
    };
static mut l_IO_Error_fopenErrorToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_Error_fopenErrorToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_IO_Error_fopenErrorToString___closed__1_value: leanh::LeanStringObject<11> =
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
        m_data: [41, 10, 32, 32, 102, 105, 108, 101, 58, 32, 0],
    };
static mut l_IO_Error_fopenErrorToString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_Error_fopenErrorToString___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_IO_Error_fopenErrorToString___closed__2_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [44, 32, 0],
    };
static mut l_IO_Error_fopenErrorToString___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_Error_fopenErrorToString___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_IO_Error_otherErrorToString___closed__0_value: leanh::LeanStringObject<2> =
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
static mut l_IO_Error_otherErrorToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_Error_otherErrorToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_IO_Error_toString___closed__0_value: leanh::LeanStringObject<15> =
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
            97, 108, 114, 101, 97, 100, 121, 32, 101, 120, 105, 115, 116, 115, 0,
        ],
    };
static mut l_IO_Error_toString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__0_value) as *mut leanh::LeanObject;
pub static l_IO_Error_toString___closed__1_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            114, 101, 115, 111, 117, 114, 99, 101, 32, 98, 117, 115, 121, 0,
        ],
    };
static mut l_IO_Error_toString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__1_value) as *mut leanh::LeanObject;
pub static l_IO_Error_toString___closed__2_value: leanh::LeanStringObject<18> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            114, 101, 115, 111, 117, 114, 99, 101, 32, 118, 97, 110, 105, 115, 104, 101, 100, 0,
        ],
    };
static mut l_IO_Error_toString___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__2_value) as *mut leanh::LeanObject;
pub static l_IO_Error_toString___closed__3_value: leanh::LeanStringObject<22> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 111, 112, 101, 114, 97, 116,
            105, 111, 110, 0,
        ],
    };
static mut l_IO_Error_toString___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__3_value) as *mut leanh::LeanObject;
pub static l_IO_Error_toString___closed__4_value: leanh::LeanStringObject<15> =
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
            104, 97, 114, 100, 119, 97, 114, 101, 32, 102, 97, 117, 108, 116, 0,
        ],
    };
static mut l_IO_Error_toString___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__4_value) as *mut leanh::LeanObject;
pub static l_IO_Error_toString___closed__5_value: leanh::LeanStringObject<20> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            100, 105, 114, 101, 99, 116, 111, 114, 121, 32, 110, 111, 116, 32, 101, 109, 112, 116,
            121, 0,
        ],
    };
static mut l_IO_Error_toString___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__5_value) as *mut leanh::LeanObject;
pub static l_IO_Error_toString___closed__6_value: leanh::LeanStringObject<18> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            105, 108, 108, 101, 103, 97, 108, 32, 111, 112, 101, 114, 97, 116, 105, 111, 110, 0,
        ],
    };
static mut l_IO_Error_toString___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__6_value) as *mut leanh::LeanObject;
pub static l_IO_Error_toString___closed__7_value: leanh::LeanStringObject<15> =
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
            112, 114, 111, 116, 111, 99, 111, 108, 32, 101, 114, 114, 111, 114, 0,
        ],
    };
static mut l_IO_Error_toString___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__7_value) as *mut leanh::LeanObject;
pub static l_IO_Error_toString___closed__8_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [116, 105, 109, 101, 32, 101, 120, 112, 105, 114, 101, 100, 0],
    };
static mut l_IO_Error_toString___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__8_value) as *mut leanh::LeanObject;
pub static l_IO_Error_toString___closed__9_value: leanh::LeanStringObject<24> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            105, 110, 116, 101, 114, 114, 117, 112, 116, 101, 100, 32, 115, 121, 115, 116, 101,
            109, 32, 99, 97, 108, 108, 0,
        ],
    };
static mut l_IO_Error_toString___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__9_value) as *mut leanh::LeanObject;
pub static l_IO_Error_toString___closed__10_value: leanh::LeanStringObject<26> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            110, 111, 32, 115, 117, 99, 104, 32, 102, 105, 108, 101, 32, 111, 114, 32, 100, 105,
            114, 101, 99, 116, 111, 114, 121, 0,
        ],
    };
static mut l_IO_Error_toString___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__10_value) as *mut leanh::LeanObject;
pub static l_IO_Error_toString___closed__11_value: leanh::LeanStringObject<17> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            105, 110, 118, 97, 108, 105, 100, 32, 97, 114, 103, 117, 109, 101, 110, 116, 0,
        ],
    };
static mut l_IO_Error_toString___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__11_value) as *mut leanh::LeanObject;
pub static l_IO_Error_toString___closed__12_value: leanh::LeanStringObject<19> =
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
            114, 101, 115, 111, 117, 114, 99, 101, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100,
            0,
        ],
    };
static mut l_IO_Error_toString___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__12_value) as *mut leanh::LeanObject;
pub static l_IO_Error_toString___closed__13_value: leanh::LeanStringObject<19> =
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
            105, 110, 97, 112, 112, 114, 111, 112, 114, 105, 97, 116, 101, 32, 116, 121, 112, 101,
            0,
        ],
    };
static mut l_IO_Error_toString___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__13_value) as *mut leanh::LeanObject;
pub static l_IO_Error_toString___closed__14_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            110, 111, 32, 115, 117, 99, 104, 32, 116, 104, 105, 110, 103, 0,
        ],
    };
static mut l_IO_Error_toString___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__14_value) as *mut leanh::LeanObject;
pub static l_IO_Error_toString___closed__15_value: leanh::LeanStringObject<12> =
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
        m_data: [101, 110, 100, 32, 111, 102, 32, 102, 105, 108, 101, 0],
    };
static mut l_IO_Error_toString___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__15_value) as *mut leanh::LeanObject;
pub static l_IO_Error_instToString___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: lean_io_error_to_string as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_IO_Error_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_Error_instToString___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_IO_Error_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_Error_instToString___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn l_IO_Error_ctorIdx(
    mut v_x_687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_687_) {
        0 => {
            let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_688_ = leanh::lean_unsigned_to_nat(0);
            return v___x_688_;
        }
        1 => {
            let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_689_ = leanh::lean_unsigned_to_nat(1);
            return v___x_689_;
        }
        2 => {
            let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_690_ = leanh::lean_unsigned_to_nat(2);
            return v___x_690_;
        }
        3 => {
            let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_691_ = leanh::lean_unsigned_to_nat(3);
            return v___x_691_;
        }
        4 => {
            let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_692_ = leanh::lean_unsigned_to_nat(4);
            return v___x_692_;
        }
        5 => {
            let mut v___x_693_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_693_ = leanh::lean_unsigned_to_nat(5);
            return v___x_693_;
        }
        6 => {
            let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_694_ = leanh::lean_unsigned_to_nat(6);
            return v___x_694_;
        }
        7 => {
            let mut v___x_695_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_695_ = leanh::lean_unsigned_to_nat(7);
            return v___x_695_;
        }
        8 => {
            let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_696_ = leanh::lean_unsigned_to_nat(8);
            return v___x_696_;
        }
        9 => {
            let mut v___x_697_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_697_ = leanh::lean_unsigned_to_nat(9);
            return v___x_697_;
        }
        10 => {
            let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_698_ = leanh::lean_unsigned_to_nat(10);
            return v___x_698_;
        }
        11 => {
            let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_699_ = leanh::lean_unsigned_to_nat(11);
            return v___x_699_;
        }
        12 => {
            let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_700_ = leanh::lean_unsigned_to_nat(12);
            return v___x_700_;
        }
        13 => {
            let mut v___x_701_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_701_ = leanh::lean_unsigned_to_nat(13);
            return v___x_701_;
        }
        14 => {
            let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_702_ = leanh::lean_unsigned_to_nat(14);
            return v___x_702_;
        }
        15 => {
            let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_703_ = leanh::lean_unsigned_to_nat(15);
            return v___x_703_;
        }
        16 => {
            let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_704_ = leanh::lean_unsigned_to_nat(16);
            return v___x_704_;
        }
        17 => {
            let mut v___x_705_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_705_ = leanh::lean_unsigned_to_nat(17);
            return v___x_705_;
        }
        _ => {
            let mut v___x_706_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_706_ = leanh::lean_unsigned_to_nat(18);
            return v___x_706_;
        }
    }
}
pub unsafe fn l_IO_Error_ctorIdx___boxed(
    mut v_x_707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_708_ = l_IO_Error_ctorIdx(v_x_707_);
    leanh::lean_dec(v_x_707_);
    return v_res_708_;
}
pub unsafe fn l_IO_Error_ctorElim___redArg(
    mut v_t_709_: *mut leanh::LeanObject,
    mut v_k_710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_709_) {
        0 => {
            let mut v_filename_711_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_osCode_712_: u32 = 0;
            let mut v_details_713_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_714_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_715_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_filename_711_ = leanh::lean_ctor_get(v_t_709_, 0);
            leanh::lean_inc(v_filename_711_);
            v_osCode_712_ = leanh::lean_ctor_get_uint32(
                v_t_709_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
            );
            v_details_713_ = leanh::lean_ctor_get(v_t_709_, 1);
            leanh::lean_inc_ref(v_details_713_);
            leanh::lean_dec_ref_known(v_t_709_, 2);
            v___x_714_ = leanh::lean_box_uint32(v_osCode_712_);
            v___x_715_ =
                leanh::lean_apply_3(v_k_710_, v_filename_711_, v___x_714_, v_details_713_);
            return v___x_715_;
        }
        10 => {
            let mut v_filename_716_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_osCode_717_: u32 = 0;
            let mut v_details_718_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_719_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_720_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_filename_716_ = leanh::lean_ctor_get(v_t_709_, 0);
            leanh::lean_inc_ref(v_filename_716_);
            v_osCode_717_ = leanh::lean_ctor_get_uint32(
                v_t_709_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
            );
            v_details_718_ = leanh::lean_ctor_get(v_t_709_, 1);
            leanh::lean_inc_ref(v_details_718_);
            leanh::lean_dec_ref_known(v_t_709_, 2);
            v___x_719_ = leanh::lean_box_uint32(v_osCode_717_);
            v___x_720_ =
                leanh::lean_apply_3(v_k_710_, v_filename_716_, v___x_719_, v_details_718_);
            return v___x_720_;
        }
        11 => {
            let mut v_filename_721_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_osCode_722_: u32 = 0;
            let mut v_details_723_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_724_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_725_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_filename_721_ = leanh::lean_ctor_get(v_t_709_, 0);
            leanh::lean_inc_ref(v_filename_721_);
            v_osCode_722_ = leanh::lean_ctor_get_uint32(
                v_t_709_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
            );
            v_details_723_ = leanh::lean_ctor_get(v_t_709_, 1);
            leanh::lean_inc_ref(v_details_723_);
            leanh::lean_dec_ref_known(v_t_709_, 2);
            v___x_724_ = leanh::lean_box_uint32(v_osCode_722_);
            v___x_725_ =
                leanh::lean_apply_3(v_k_710_, v_filename_721_, v___x_724_, v_details_723_);
            return v___x_725_;
        }
        12 => {
            let mut v_filename_726_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_osCode_727_: u32 = 0;
            let mut v_details_728_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_730_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_filename_726_ = leanh::lean_ctor_get(v_t_709_, 0);
            leanh::lean_inc(v_filename_726_);
            v_osCode_727_ = leanh::lean_ctor_get_uint32(
                v_t_709_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
            );
            v_details_728_ = leanh::lean_ctor_get(v_t_709_, 1);
            leanh::lean_inc_ref(v_details_728_);
            leanh::lean_dec_ref_known(v_t_709_, 2);
            v___x_729_ = leanh::lean_box_uint32(v_osCode_727_);
            v___x_730_ =
                leanh::lean_apply_3(v_k_710_, v_filename_726_, v___x_729_, v_details_728_);
            return v___x_730_;
        }
        13 => {
            let mut v_filename_731_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_osCode_732_: u32 = 0;
            let mut v_details_733_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_filename_731_ = leanh::lean_ctor_get(v_t_709_, 0);
            leanh::lean_inc(v_filename_731_);
            v_osCode_732_ = leanh::lean_ctor_get_uint32(
                v_t_709_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
            );
            v_details_733_ = leanh::lean_ctor_get(v_t_709_, 1);
            leanh::lean_inc_ref(v_details_733_);
            leanh::lean_dec_ref_known(v_t_709_, 2);
            v___x_734_ = leanh::lean_box_uint32(v_osCode_732_);
            v___x_735_ =
                leanh::lean_apply_3(v_k_710_, v_filename_731_, v___x_734_, v_details_733_);
            return v___x_735_;
        }
        14 => {
            let mut v_filename_736_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_osCode_737_: u32 = 0;
            let mut v_details_738_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_740_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_filename_736_ = leanh::lean_ctor_get(v_t_709_, 0);
            leanh::lean_inc(v_filename_736_);
            v_osCode_737_ = leanh::lean_ctor_get_uint32(
                v_t_709_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
            );
            v_details_738_ = leanh::lean_ctor_get(v_t_709_, 1);
            leanh::lean_inc_ref(v_details_738_);
            leanh::lean_dec_ref_known(v_t_709_, 2);
            v___x_739_ = leanh::lean_box_uint32(v_osCode_737_);
            v___x_740_ =
                leanh::lean_apply_3(v_k_710_, v_filename_736_, v___x_739_, v_details_738_);
            return v___x_740_;
        }
        15 => {
            let mut v_filename_741_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_osCode_742_: u32 = 0;
            let mut v_details_743_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_745_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_filename_741_ = leanh::lean_ctor_get(v_t_709_, 0);
            leanh::lean_inc(v_filename_741_);
            v_osCode_742_ = leanh::lean_ctor_get_uint32(
                v_t_709_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
            );
            v_details_743_ = leanh::lean_ctor_get(v_t_709_, 1);
            leanh::lean_inc_ref(v_details_743_);
            leanh::lean_dec_ref_known(v_t_709_, 2);
            v___x_744_ = leanh::lean_box_uint32(v_osCode_742_);
            v___x_745_ =
                leanh::lean_apply_3(v_k_710_, v_filename_741_, v___x_744_, v_details_743_);
            return v___x_745_;
        }
        16 => {
            let mut v_filename_746_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_osCode_747_: u32 = 0;
            let mut v_details_748_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_749_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_750_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_filename_746_ = leanh::lean_ctor_get(v_t_709_, 0);
            leanh::lean_inc(v_filename_746_);
            v_osCode_747_ = leanh::lean_ctor_get_uint32(
                v_t_709_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
            );
            v_details_748_ = leanh::lean_ctor_get(v_t_709_, 1);
            leanh::lean_inc_ref(v_details_748_);
            leanh::lean_dec_ref_known(v_t_709_, 2);
            v___x_749_ = leanh::lean_box_uint32(v_osCode_747_);
            v___x_750_ =
                leanh::lean_apply_3(v_k_710_, v_filename_746_, v___x_749_, v_details_748_);
            return v___x_750_;
        }
        17 => {
            return v_k_710_;
        }
        18 => {
            let mut v_msg_751_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_752_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_msg_751_ = leanh::lean_ctor_get(v_t_709_, 0);
            leanh::lean_inc_ref(v_msg_751_);
            leanh::lean_dec_ref_known(v_t_709_, 1);
            v___x_752_ = leanh::lean_apply_1(v_k_710_, v_msg_751_);
            return v___x_752_;
        }
        _ => {
            let mut v_osCode_753_: u32 = 0;
            let mut v_details_754_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_755_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_756_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_osCode_753_ = leanh::lean_ctor_get_uint32(
                v_t_709_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
            );
            v_details_754_ = leanh::lean_ctor_get(v_t_709_, 0);
            leanh::lean_inc_ref(v_details_754_);
            leanh::lean_dec(v_t_709_);
            v___x_755_ = leanh::lean_box_uint32(v_osCode_753_);
            v___x_756_ = leanh::lean_apply_2(v_k_710_, v___x_755_, v_details_754_);
            return v___x_756_;
        }
    }
}
pub unsafe fn l_IO_Error_ctorElim(
    mut v_motive_757_: *mut leanh::LeanObject,
    mut v_ctorIdx_758_: *mut leanh::LeanObject,
    mut v_t_759_: *mut leanh::LeanObject,
    mut v_h_760_: *mut leanh::LeanObject,
    mut v_k_761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_762_ = l_IO_Error_ctorElim___redArg(v_t_759_, v_k_761_);
    return v___x_762_;
}
pub unsafe fn l_IO_Error_ctorElim___boxed(
    mut v_motive_763_: *mut leanh::LeanObject,
    mut v_ctorIdx_764_: *mut leanh::LeanObject,
    mut v_t_765_: *mut leanh::LeanObject,
    mut v_h_766_: *mut leanh::LeanObject,
    mut v_k_767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_768_ = l_IO_Error_ctorElim(v_motive_763_, v_ctorIdx_764_, v_t_765_, v_h_766_, v_k_767_);
    leanh::lean_dec(v_ctorIdx_764_);
    return v_res_768_;
}
pub unsafe fn l_IO_Error_alreadyExists_elim___redArg(
    mut v_t_769_: *mut leanh::LeanObject,
    mut v_alreadyExists_770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_771_ = l_IO_Error_ctorElim___redArg(v_t_769_, v_alreadyExists_770_);
    return v___x_771_;
}
pub unsafe fn l_IO_Error_alreadyExists_elim(
    mut v_motive_772_: *mut leanh::LeanObject,
    mut v_t_773_: *mut leanh::LeanObject,
    mut v_h_774_: *mut leanh::LeanObject,
    mut v_alreadyExists_775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_776_ = l_IO_Error_ctorElim___redArg(v_t_773_, v_alreadyExists_775_);
    return v___x_776_;
}
pub unsafe fn l_IO_Error_otherError_elim___redArg(
    mut v_t_777_: *mut leanh::LeanObject,
    mut v_otherError_778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_779_ = l_IO_Error_ctorElim___redArg(v_t_777_, v_otherError_778_);
    return v___x_779_;
}
pub unsafe fn l_IO_Error_otherError_elim(
    mut v_motive_780_: *mut leanh::LeanObject,
    mut v_t_781_: *mut leanh::LeanObject,
    mut v_h_782_: *mut leanh::LeanObject,
    mut v_otherError_783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_784_ = l_IO_Error_ctorElim___redArg(v_t_781_, v_otherError_783_);
    return v___x_784_;
}
pub unsafe fn l_IO_Error_resourceBusy_elim___redArg(
    mut v_t_785_: *mut leanh::LeanObject,
    mut v_resourceBusy_786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_787_ = l_IO_Error_ctorElim___redArg(v_t_785_, v_resourceBusy_786_);
    return v___x_787_;
}
pub unsafe fn l_IO_Error_resourceBusy_elim(
    mut v_motive_788_: *mut leanh::LeanObject,
    mut v_t_789_: *mut leanh::LeanObject,
    mut v_h_790_: *mut leanh::LeanObject,
    mut v_resourceBusy_791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_792_ = l_IO_Error_ctorElim___redArg(v_t_789_, v_resourceBusy_791_);
    return v___x_792_;
}
pub unsafe fn l_IO_Error_resourceVanished_elim___redArg(
    mut v_t_793_: *mut leanh::LeanObject,
    mut v_resourceVanished_794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_795_ = l_IO_Error_ctorElim___redArg(v_t_793_, v_resourceVanished_794_);
    return v___x_795_;
}
pub unsafe fn l_IO_Error_resourceVanished_elim(
    mut v_motive_796_: *mut leanh::LeanObject,
    mut v_t_797_: *mut leanh::LeanObject,
    mut v_h_798_: *mut leanh::LeanObject,
    mut v_resourceVanished_799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_800_ = l_IO_Error_ctorElim___redArg(v_t_797_, v_resourceVanished_799_);
    return v___x_800_;
}
pub unsafe fn l_IO_Error_unsupportedOperation_elim___redArg(
    mut v_t_801_: *mut leanh::LeanObject,
    mut v_unsupportedOperation_802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_803_ = l_IO_Error_ctorElim___redArg(v_t_801_, v_unsupportedOperation_802_);
    return v___x_803_;
}
pub unsafe fn l_IO_Error_unsupportedOperation_elim(
    mut v_motive_804_: *mut leanh::LeanObject,
    mut v_t_805_: *mut leanh::LeanObject,
    mut v_h_806_: *mut leanh::LeanObject,
    mut v_unsupportedOperation_807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_808_ = l_IO_Error_ctorElim___redArg(v_t_805_, v_unsupportedOperation_807_);
    return v___x_808_;
}
pub unsafe fn l_IO_Error_hardwareFault_elim___redArg(
    mut v_t_809_: *mut leanh::LeanObject,
    mut v_hardwareFault_810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_811_ = l_IO_Error_ctorElim___redArg(v_t_809_, v_hardwareFault_810_);
    return v___x_811_;
}
pub unsafe fn l_IO_Error_hardwareFault_elim(
    mut v_motive_812_: *mut leanh::LeanObject,
    mut v_t_813_: *mut leanh::LeanObject,
    mut v_h_814_: *mut leanh::LeanObject,
    mut v_hardwareFault_815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_816_ = l_IO_Error_ctorElim___redArg(v_t_813_, v_hardwareFault_815_);
    return v___x_816_;
}
pub unsafe fn l_IO_Error_unsatisfiedConstraints_elim___redArg(
    mut v_t_817_: *mut leanh::LeanObject,
    mut v_unsatisfiedConstraints_818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_819_ = l_IO_Error_ctorElim___redArg(v_t_817_, v_unsatisfiedConstraints_818_);
    return v___x_819_;
}
pub unsafe fn l_IO_Error_unsatisfiedConstraints_elim(
    mut v_motive_820_: *mut leanh::LeanObject,
    mut v_t_821_: *mut leanh::LeanObject,
    mut v_h_822_: *mut leanh::LeanObject,
    mut v_unsatisfiedConstraints_823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_824_ = l_IO_Error_ctorElim___redArg(v_t_821_, v_unsatisfiedConstraints_823_);
    return v___x_824_;
}
pub unsafe fn l_IO_Error_illegalOperation_elim___redArg(
    mut v_t_825_: *mut leanh::LeanObject,
    mut v_illegalOperation_826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_827_ = l_IO_Error_ctorElim___redArg(v_t_825_, v_illegalOperation_826_);
    return v___x_827_;
}
pub unsafe fn l_IO_Error_illegalOperation_elim(
    mut v_motive_828_: *mut leanh::LeanObject,
    mut v_t_829_: *mut leanh::LeanObject,
    mut v_h_830_: *mut leanh::LeanObject,
    mut v_illegalOperation_831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_832_ = l_IO_Error_ctorElim___redArg(v_t_829_, v_illegalOperation_831_);
    return v___x_832_;
}
pub unsafe fn l_IO_Error_protocolError_elim___redArg(
    mut v_t_833_: *mut leanh::LeanObject,
    mut v_protocolError_834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_835_ = l_IO_Error_ctorElim___redArg(v_t_833_, v_protocolError_834_);
    return v___x_835_;
}
pub unsafe fn l_IO_Error_protocolError_elim(
    mut v_motive_836_: *mut leanh::LeanObject,
    mut v_t_837_: *mut leanh::LeanObject,
    mut v_h_838_: *mut leanh::LeanObject,
    mut v_protocolError_839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_840_ = l_IO_Error_ctorElim___redArg(v_t_837_, v_protocolError_839_);
    return v___x_840_;
}
pub unsafe fn l_IO_Error_timeExpired_elim___redArg(
    mut v_t_841_: *mut leanh::LeanObject,
    mut v_timeExpired_842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_843_ = l_IO_Error_ctorElim___redArg(v_t_841_, v_timeExpired_842_);
    return v___x_843_;
}
pub unsafe fn l_IO_Error_timeExpired_elim(
    mut v_motive_844_: *mut leanh::LeanObject,
    mut v_t_845_: *mut leanh::LeanObject,
    mut v_h_846_: *mut leanh::LeanObject,
    mut v_timeExpired_847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_848_ = l_IO_Error_ctorElim___redArg(v_t_845_, v_timeExpired_847_);
    return v___x_848_;
}
pub unsafe fn l_IO_Error_interrupted_elim___redArg(
    mut v_t_849_: *mut leanh::LeanObject,
    mut v_interrupted_850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_851_ = l_IO_Error_ctorElim___redArg(v_t_849_, v_interrupted_850_);
    return v___x_851_;
}
pub unsafe fn l_IO_Error_interrupted_elim(
    mut v_motive_852_: *mut leanh::LeanObject,
    mut v_t_853_: *mut leanh::LeanObject,
    mut v_h_854_: *mut leanh::LeanObject,
    mut v_interrupted_855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_856_ = l_IO_Error_ctorElim___redArg(v_t_853_, v_interrupted_855_);
    return v___x_856_;
}
pub unsafe fn l_IO_Error_noFileOrDirectory_elim___redArg(
    mut v_t_857_: *mut leanh::LeanObject,
    mut v_noFileOrDirectory_858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_859_ = l_IO_Error_ctorElim___redArg(v_t_857_, v_noFileOrDirectory_858_);
    return v___x_859_;
}
pub unsafe fn l_IO_Error_noFileOrDirectory_elim(
    mut v_motive_860_: *mut leanh::LeanObject,
    mut v_t_861_: *mut leanh::LeanObject,
    mut v_h_862_: *mut leanh::LeanObject,
    mut v_noFileOrDirectory_863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_864_ = l_IO_Error_ctorElim___redArg(v_t_861_, v_noFileOrDirectory_863_);
    return v___x_864_;
}
pub unsafe fn l_IO_Error_invalidArgument_elim___redArg(
    mut v_t_865_: *mut leanh::LeanObject,
    mut v_invalidArgument_866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_867_ = l_IO_Error_ctorElim___redArg(v_t_865_, v_invalidArgument_866_);
    return v___x_867_;
}
pub unsafe fn l_IO_Error_invalidArgument_elim(
    mut v_motive_868_: *mut leanh::LeanObject,
    mut v_t_869_: *mut leanh::LeanObject,
    mut v_h_870_: *mut leanh::LeanObject,
    mut v_invalidArgument_871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_872_ = l_IO_Error_ctorElim___redArg(v_t_869_, v_invalidArgument_871_);
    return v___x_872_;
}
pub unsafe fn l_IO_Error_permissionDenied_elim___redArg(
    mut v_t_873_: *mut leanh::LeanObject,
    mut v_permissionDenied_874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_875_ = l_IO_Error_ctorElim___redArg(v_t_873_, v_permissionDenied_874_);
    return v___x_875_;
}
pub unsafe fn l_IO_Error_permissionDenied_elim(
    mut v_motive_876_: *mut leanh::LeanObject,
    mut v_t_877_: *mut leanh::LeanObject,
    mut v_h_878_: *mut leanh::LeanObject,
    mut v_permissionDenied_879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_880_ = l_IO_Error_ctorElim___redArg(v_t_877_, v_permissionDenied_879_);
    return v___x_880_;
}
pub unsafe fn l_IO_Error_resourceExhausted_elim___redArg(
    mut v_t_881_: *mut leanh::LeanObject,
    mut v_resourceExhausted_882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_883_ = l_IO_Error_ctorElim___redArg(v_t_881_, v_resourceExhausted_882_);
    return v___x_883_;
}
pub unsafe fn l_IO_Error_resourceExhausted_elim(
    mut v_motive_884_: *mut leanh::LeanObject,
    mut v_t_885_: *mut leanh::LeanObject,
    mut v_h_886_: *mut leanh::LeanObject,
    mut v_resourceExhausted_887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_888_ = l_IO_Error_ctorElim___redArg(v_t_885_, v_resourceExhausted_887_);
    return v___x_888_;
}
pub unsafe fn l_IO_Error_inappropriateType_elim___redArg(
    mut v_t_889_: *mut leanh::LeanObject,
    mut v_inappropriateType_890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_891_ = l_IO_Error_ctorElim___redArg(v_t_889_, v_inappropriateType_890_);
    return v___x_891_;
}
pub unsafe fn l_IO_Error_inappropriateType_elim(
    mut v_motive_892_: *mut leanh::LeanObject,
    mut v_t_893_: *mut leanh::LeanObject,
    mut v_h_894_: *mut leanh::LeanObject,
    mut v_inappropriateType_895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_896_ = l_IO_Error_ctorElim___redArg(v_t_893_, v_inappropriateType_895_);
    return v___x_896_;
}
pub unsafe fn l_IO_Error_noSuchThing_elim___redArg(
    mut v_t_897_: *mut leanh::LeanObject,
    mut v_noSuchThing_898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_899_ = l_IO_Error_ctorElim___redArg(v_t_897_, v_noSuchThing_898_);
    return v___x_899_;
}
pub unsafe fn l_IO_Error_noSuchThing_elim(
    mut v_motive_900_: *mut leanh::LeanObject,
    mut v_t_901_: *mut leanh::LeanObject,
    mut v_h_902_: *mut leanh::LeanObject,
    mut v_noSuchThing_903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_904_ = l_IO_Error_ctorElim___redArg(v_t_901_, v_noSuchThing_903_);
    return v___x_904_;
}
pub unsafe fn l_IO_Error_unexpectedEof_elim___redArg(
    mut v_t_905_: *mut leanh::LeanObject,
    mut v_unexpectedEof_906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_907_ = l_IO_Error_ctorElim___redArg(v_t_905_, v_unexpectedEof_906_);
    return v___x_907_;
}
pub unsafe fn l_IO_Error_unexpectedEof_elim(
    mut v_motive_908_: *mut leanh::LeanObject,
    mut v_t_909_: *mut leanh::LeanObject,
    mut v_h_910_: *mut leanh::LeanObject,
    mut v_unexpectedEof_911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_912_ = l_IO_Error_ctorElim___redArg(v_t_909_, v_unexpectedEof_911_);
    return v___x_912_;
}
pub unsafe fn l_IO_Error_userError_elim___redArg(
    mut v_t_913_: *mut leanh::LeanObject,
    mut v_userError_914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_915_ = l_IO_Error_ctorElim___redArg(v_t_913_, v_userError_914_);
    return v___x_915_;
}
pub unsafe fn l_IO_Error_userError_elim(
    mut v_motive_916_: *mut leanh::LeanObject,
    mut v_t_917_: *mut leanh::LeanObject,
    mut v_h_918_: *mut leanh::LeanObject,
    mut v_userError_919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_920_ = l_IO_Error_ctorElim___redArg(v_t_917_, v_userError_919_);
    return v___x_920_;
}
pub unsafe fn lean_mk_io_user_error(
    mut v_s_925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_926_ = leanh::lean_alloc_ctor(18, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_926_, 0, v_s_925_);
    return v___x_926_;
}
pub unsafe fn lean_mk_io_error_already_exists_file(
    mut v_a_929_: *mut leanh::LeanObject,
    mut v_a_930_: u32,
    mut v_a_931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_932_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_932_, 0, v_a_929_);
    v___x_933_ = leanh::lean_alloc_ctor(0, 2, (4) as u32);
    leanh::lean_ctor_set(v___x_933_, 0, v___x_932_);
    leanh::lean_ctor_set(v___x_933_, 1, v_a_931_);
    leanh::lean_ctor_set_uint32(
        v___x_933_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v_a_930_,
    );
    return v___x_933_;
}
pub unsafe fn l_IO_Error_mkAlreadyExistsFile___boxed(
    mut v_a_934_: *mut leanh::LeanObject,
    mut v_a_935_: *mut leanh::LeanObject,
    mut v_a_936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_20__boxed_937_: u32 = 0;
    let mut v_res_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_20__boxed_937_ = leanh::lean_unbox_uint32(v_a_935_);
    leanh::lean_dec(v_a_935_);
    v_res_938_ = lean_mk_io_error_already_exists_file(v_a_934_, v_a_20__boxed_937_, v_a_936_);
    return v_res_938_;
}
pub unsafe fn lean_mk_io_error_eof(
    mut v_x_939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_940_ = leanh::lean_box(17);
    return v___x_940_;
}
pub unsafe fn lean_mk_io_error_inappropriate_type_file(
    mut v_a_941_: *mut leanh::LeanObject,
    mut v_a_942_: u32,
    mut v_a_943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_944_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_944_, 0, v_a_941_);
    v___x_945_ = leanh::lean_alloc_ctor(15, 2, (4) as u32);
    leanh::lean_ctor_set(v___x_945_, 0, v___x_944_);
    leanh::lean_ctor_set(v___x_945_, 1, v_a_943_);
    leanh::lean_ctor_set_uint32(
        v___x_945_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v_a_942_,
    );
    return v___x_945_;
}
pub unsafe fn l_IO_Error_mkInappropriateTypeFile___boxed(
    mut v_a_946_: *mut leanh::LeanObject,
    mut v_a_947_: *mut leanh::LeanObject,
    mut v_a_948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_20__boxed_949_: u32 = 0;
    let mut v_res_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_20__boxed_949_ = leanh::lean_unbox_uint32(v_a_947_);
    leanh::lean_dec(v_a_947_);
    v_res_950_ = lean_mk_io_error_inappropriate_type_file(v_a_946_, v_a_20__boxed_949_, v_a_948_);
    return v_res_950_;
}
pub unsafe fn lean_mk_io_error_interrupted(
    mut v_filename_951_: *mut leanh::LeanObject,
    mut v_osCode_952_: u32,
    mut v_details_953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_954_ = leanh::lean_alloc_ctor(10, 2, (4) as u32);
    leanh::lean_ctor_set(v___x_954_, 0, v_filename_951_);
    leanh::lean_ctor_set(v___x_954_, 1, v_details_953_);
    leanh::lean_ctor_set_uint32(
        v___x_954_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v_osCode_952_,
    );
    return v___x_954_;
}
pub unsafe fn l_IO_Error_mkInterrupted___boxed(
    mut v_filename_955_: *mut leanh::LeanObject,
    mut v_osCode_956_: *mut leanh::LeanObject,
    mut v_details_957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_osCode_boxed_958_: u32 = 0;
    let mut v_res_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_osCode_boxed_958_ = leanh::lean_unbox_uint32(v_osCode_956_);
    leanh::lean_dec(v_osCode_956_);
    v_res_959_ = lean_mk_io_error_interrupted(v_filename_955_, v_osCode_boxed_958_, v_details_957_);
    return v_res_959_;
}
pub unsafe fn lean_mk_io_error_invalid_argument_file(
    mut v_a_960_: *mut leanh::LeanObject,
    mut v_a_961_: u32,
    mut v_a_962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_963_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_963_, 0, v_a_960_);
    v___x_964_ = leanh::lean_alloc_ctor(12, 2, (4) as u32);
    leanh::lean_ctor_set(v___x_964_, 0, v___x_963_);
    leanh::lean_ctor_set(v___x_964_, 1, v_a_962_);
    leanh::lean_ctor_set_uint32(
        v___x_964_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v_a_961_,
    );
    return v___x_964_;
}
pub unsafe fn l_IO_Error_mkInvalidArgumentFile___boxed(
    mut v_a_965_: *mut leanh::LeanObject,
    mut v_a_966_: *mut leanh::LeanObject,
    mut v_a_967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_20__boxed_968_: u32 = 0;
    let mut v_res_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_20__boxed_968_ = leanh::lean_unbox_uint32(v_a_966_);
    leanh::lean_dec(v_a_966_);
    v_res_969_ = lean_mk_io_error_invalid_argument_file(v_a_965_, v_a_20__boxed_968_, v_a_967_);
    return v_res_969_;
}
pub unsafe fn lean_mk_io_error_no_file_or_directory(
    mut v_filename_970_: *mut leanh::LeanObject,
    mut v_osCode_971_: u32,
    mut v_details_972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_973_ = leanh::lean_alloc_ctor(11, 2, (4) as u32);
    leanh::lean_ctor_set(v___x_973_, 0, v_filename_970_);
    leanh::lean_ctor_set(v___x_973_, 1, v_details_972_);
    leanh::lean_ctor_set_uint32(
        v___x_973_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v_osCode_971_,
    );
    return v___x_973_;
}
pub unsafe fn l_IO_Error_mkNoFileOrDirectory___boxed(
    mut v_filename_974_: *mut leanh::LeanObject,
    mut v_osCode_975_: *mut leanh::LeanObject,
    mut v_details_976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_osCode_boxed_977_: u32 = 0;
    let mut v_res_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_osCode_boxed_977_ = leanh::lean_unbox_uint32(v_osCode_975_);
    leanh::lean_dec(v_osCode_975_);
    v_res_978_ =
        lean_mk_io_error_no_file_or_directory(v_filename_974_, v_osCode_boxed_977_, v_details_976_);
    return v_res_978_;
}
pub unsafe fn lean_mk_io_error_no_such_thing_file(
    mut v_a_979_: *mut leanh::LeanObject,
    mut v_a_980_: u32,
    mut v_a_981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_982_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_982_, 0, v_a_979_);
    v___x_983_ = leanh::lean_alloc_ctor(16, 2, (4) as u32);
    leanh::lean_ctor_set(v___x_983_, 0, v___x_982_);
    leanh::lean_ctor_set(v___x_983_, 1, v_a_981_);
    leanh::lean_ctor_set_uint32(
        v___x_983_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v_a_980_,
    );
    return v___x_983_;
}
pub unsafe fn l_IO_Error_mkNoSuchThingFile___boxed(
    mut v_a_984_: *mut leanh::LeanObject,
    mut v_a_985_: *mut leanh::LeanObject,
    mut v_a_986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_20__boxed_987_: u32 = 0;
    let mut v_res_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_20__boxed_987_ = leanh::lean_unbox_uint32(v_a_985_);
    leanh::lean_dec(v_a_985_);
    v_res_988_ = lean_mk_io_error_no_such_thing_file(v_a_984_, v_a_20__boxed_987_, v_a_986_);
    return v_res_988_;
}
pub unsafe fn lean_mk_io_error_permission_denied_file(
    mut v_a_989_: *mut leanh::LeanObject,
    mut v_a_990_: u32,
    mut v_a_991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_992_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_992_, 0, v_a_989_);
    v___x_993_ = leanh::lean_alloc_ctor(13, 2, (4) as u32);
    leanh::lean_ctor_set(v___x_993_, 0, v___x_992_);
    leanh::lean_ctor_set(v___x_993_, 1, v_a_991_);
    leanh::lean_ctor_set_uint32(
        v___x_993_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v_a_990_,
    );
    return v___x_993_;
}
pub unsafe fn l_IO_Error_mkPermissionDeniedFile___boxed(
    mut v_a_994_: *mut leanh::LeanObject,
    mut v_a_995_: *mut leanh::LeanObject,
    mut v_a_996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_20__boxed_997_: u32 = 0;
    let mut v_res_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_20__boxed_997_ = leanh::lean_unbox_uint32(v_a_995_);
    leanh::lean_dec(v_a_995_);
    v_res_998_ = lean_mk_io_error_permission_denied_file(v_a_994_, v_a_20__boxed_997_, v_a_996_);
    return v_res_998_;
}
pub unsafe fn lean_mk_io_error_resource_exhausted_file(
    mut v_a_999_: *mut leanh::LeanObject,
    mut v_a_1000_: u32,
    mut v_a_1001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1002_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1002_, 0, v_a_999_);
    v___x_1003_ = leanh::lean_alloc_ctor(14, 2, (4) as u32);
    leanh::lean_ctor_set(v___x_1003_, 0, v___x_1002_);
    leanh::lean_ctor_set(v___x_1003_, 1, v_a_1001_);
    leanh::lean_ctor_set_uint32(
        v___x_1003_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v_a_1000_,
    );
    return v___x_1003_;
}
pub unsafe fn l_IO_Error_mkResourceExhaustedFile___boxed(
    mut v_a_1004_: *mut leanh::LeanObject,
    mut v_a_1005_: *mut leanh::LeanObject,
    mut v_a_1006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_20__boxed_1007_: u32 = 0;
    let mut v_res_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_20__boxed_1007_ = leanh::lean_unbox_uint32(v_a_1005_);
    leanh::lean_dec(v_a_1005_);
    v_res_1008_ =
        lean_mk_io_error_resource_exhausted_file(v_a_1004_, v_a_20__boxed_1007_, v_a_1006_);
    return v_res_1008_;
}
pub unsafe fn lean_mk_io_error_unsupported_operation(
    mut v_osCode_1009_: u32,
    mut v_details_1010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1011_ = leanh::lean_alloc_ctor(4, 1, (4) as u32);
    leanh::lean_ctor_set(v___x_1011_, 0, v_details_1010_);
    leanh::lean_ctor_set_uint32(
        v___x_1011_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_osCode_1009_,
    );
    return v___x_1011_;
}
pub unsafe fn l_IO_Error_mkUnsupportedOperation___boxed(
    mut v_osCode_1012_: *mut leanh::LeanObject,
    mut v_details_1013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_osCode_boxed_1014_: u32 = 0;
    let mut v_res_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1014_ = leanh::lean_unbox_uint32(v_osCode_1012_);
    leanh::lean_dec(v_osCode_1012_);
    v_res_1015_ = lean_mk_io_error_unsupported_operation(v_osCode_boxed_1014_, v_details_1013_);
    return v_res_1015_;
}
pub unsafe fn lean_mk_io_error_resource_exhausted(
    mut v_osCode_1016_: u32,
    mut v_details_1017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1018_ = leanh::lean_box(0);
    v___x_1019_ = leanh::lean_alloc_ctor(14, 2, (4) as u32);
    leanh::lean_ctor_set(v___x_1019_, 0, v___x_1018_);
    leanh::lean_ctor_set(v___x_1019_, 1, v_details_1017_);
    leanh::lean_ctor_set_uint32(
        v___x_1019_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v_osCode_1016_,
    );
    return v___x_1019_;
}
pub unsafe fn l_IO_Error_mkResourceExhausted___boxed(
    mut v_osCode_1020_: *mut leanh::LeanObject,
    mut v_details_1021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_osCode_boxed_1022_: u32 = 0;
    let mut v_res_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1022_ = leanh::lean_unbox_uint32(v_osCode_1020_);
    leanh::lean_dec(v_osCode_1020_);
    v_res_1023_ = lean_mk_io_error_resource_exhausted(v_osCode_boxed_1022_, v_details_1021_);
    return v_res_1023_;
}
pub unsafe fn lean_mk_io_error_already_exists(
    mut v_osCode_1024_: u32,
    mut v_details_1025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1026_ = leanh::lean_box(0);
    v___x_1027_ = leanh::lean_alloc_ctor(0, 2, (4) as u32);
    leanh::lean_ctor_set(v___x_1027_, 0, v___x_1026_);
    leanh::lean_ctor_set(v___x_1027_, 1, v_details_1025_);
    leanh::lean_ctor_set_uint32(
        v___x_1027_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v_osCode_1024_,
    );
    return v___x_1027_;
}
pub unsafe fn l_IO_Error_mkAlreadyExists___boxed(
    mut v_osCode_1028_: *mut leanh::LeanObject,
    mut v_details_1029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_osCode_boxed_1030_: u32 = 0;
    let mut v_res_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1030_ = leanh::lean_unbox_uint32(v_osCode_1028_);
    leanh::lean_dec(v_osCode_1028_);
    v_res_1031_ = lean_mk_io_error_already_exists(v_osCode_boxed_1030_, v_details_1029_);
    return v_res_1031_;
}
pub unsafe fn lean_mk_io_error_inappropriate_type(
    mut v_osCode_1032_: u32,
    mut v_details_1033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1034_ = leanh::lean_box(0);
    v___x_1035_ = leanh::lean_alloc_ctor(15, 2, (4) as u32);
    leanh::lean_ctor_set(v___x_1035_, 0, v___x_1034_);
    leanh::lean_ctor_set(v___x_1035_, 1, v_details_1033_);
    leanh::lean_ctor_set_uint32(
        v___x_1035_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v_osCode_1032_,
    );
    return v___x_1035_;
}
pub unsafe fn l_IO_Error_mkInappropriateType___boxed(
    mut v_osCode_1036_: *mut leanh::LeanObject,
    mut v_details_1037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_osCode_boxed_1038_: u32 = 0;
    let mut v_res_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1038_ = leanh::lean_unbox_uint32(v_osCode_1036_);
    leanh::lean_dec(v_osCode_1036_);
    v_res_1039_ = lean_mk_io_error_inappropriate_type(v_osCode_boxed_1038_, v_details_1037_);
    return v_res_1039_;
}
pub unsafe fn lean_mk_io_error_no_such_thing(
    mut v_osCode_1040_: u32,
    mut v_details_1041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1042_ = leanh::lean_box(0);
    v___x_1043_ = leanh::lean_alloc_ctor(16, 2, (4) as u32);
    leanh::lean_ctor_set(v___x_1043_, 0, v___x_1042_);
    leanh::lean_ctor_set(v___x_1043_, 1, v_details_1041_);
    leanh::lean_ctor_set_uint32(
        v___x_1043_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v_osCode_1040_,
    );
    return v___x_1043_;
}
pub unsafe fn l_IO_Error_mkNoSuchThing___boxed(
    mut v_osCode_1044_: *mut leanh::LeanObject,
    mut v_details_1045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_osCode_boxed_1046_: u32 = 0;
    let mut v_res_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1046_ = leanh::lean_unbox_uint32(v_osCode_1044_);
    leanh::lean_dec(v_osCode_1044_);
    v_res_1047_ = lean_mk_io_error_no_such_thing(v_osCode_boxed_1046_, v_details_1045_);
    return v_res_1047_;
}
pub unsafe fn lean_mk_io_error_resource_vanished(
    mut v_osCode_1048_: u32,
    mut v_details_1049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1050_ = leanh::lean_alloc_ctor(3, 1, (4) as u32);
    leanh::lean_ctor_set(v___x_1050_, 0, v_details_1049_);
    leanh::lean_ctor_set_uint32(
        v___x_1050_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_osCode_1048_,
    );
    return v___x_1050_;
}
pub unsafe fn l_IO_Error_mkResourceVanished___boxed(
    mut v_osCode_1051_: *mut leanh::LeanObject,
    mut v_details_1052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_osCode_boxed_1053_: u32 = 0;
    let mut v_res_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1053_ = leanh::lean_unbox_uint32(v_osCode_1051_);
    leanh::lean_dec(v_osCode_1051_);
    v_res_1054_ = lean_mk_io_error_resource_vanished(v_osCode_boxed_1053_, v_details_1052_);
    return v_res_1054_;
}
pub unsafe fn lean_mk_io_error_resource_busy(
    mut v_osCode_1055_: u32,
    mut v_details_1056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1057_ = leanh::lean_alloc_ctor(2, 1, (4) as u32);
    leanh::lean_ctor_set(v___x_1057_, 0, v_details_1056_);
    leanh::lean_ctor_set_uint32(
        v___x_1057_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_osCode_1055_,
    );
    return v___x_1057_;
}
pub unsafe fn l_IO_Error_mkResourceBusy___boxed(
    mut v_osCode_1058_: *mut leanh::LeanObject,
    mut v_details_1059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_osCode_boxed_1060_: u32 = 0;
    let mut v_res_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1060_ = leanh::lean_unbox_uint32(v_osCode_1058_);
    leanh::lean_dec(v_osCode_1058_);
    v_res_1061_ = lean_mk_io_error_resource_busy(v_osCode_boxed_1060_, v_details_1059_);
    return v_res_1061_;
}
pub unsafe fn lean_mk_io_error_invalid_argument(
    mut v_osCode_1062_: u32,
    mut v_details_1063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1064_ = leanh::lean_box(0);
    v___x_1065_ = leanh::lean_alloc_ctor(12, 2, (4) as u32);
    leanh::lean_ctor_set(v___x_1065_, 0, v___x_1064_);
    leanh::lean_ctor_set(v___x_1065_, 1, v_details_1063_);
    leanh::lean_ctor_set_uint32(
        v___x_1065_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v_osCode_1062_,
    );
    return v___x_1065_;
}
pub unsafe fn l_IO_Error_mkInvalidArgument___boxed(
    mut v_osCode_1066_: *mut leanh::LeanObject,
    mut v_details_1067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_osCode_boxed_1068_: u32 = 0;
    let mut v_res_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1068_ = leanh::lean_unbox_uint32(v_osCode_1066_);
    leanh::lean_dec(v_osCode_1066_);
    v_res_1069_ = lean_mk_io_error_invalid_argument(v_osCode_boxed_1068_, v_details_1067_);
    return v_res_1069_;
}
pub unsafe fn lean_mk_io_error_other_error(
    mut v_osCode_1070_: u32,
    mut v_details_1071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1072_ = leanh::lean_alloc_ctor(1, 1, (4) as u32);
    leanh::lean_ctor_set(v___x_1072_, 0, v_details_1071_);
    leanh::lean_ctor_set_uint32(
        v___x_1072_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_osCode_1070_,
    );
    return v___x_1072_;
}
pub unsafe fn l_IO_Error_mkOtherError___boxed(
    mut v_osCode_1073_: *mut leanh::LeanObject,
    mut v_details_1074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_osCode_boxed_1075_: u32 = 0;
    let mut v_res_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1075_ = leanh::lean_unbox_uint32(v_osCode_1073_);
    leanh::lean_dec(v_osCode_1073_);
    v_res_1076_ = lean_mk_io_error_other_error(v_osCode_boxed_1075_, v_details_1074_);
    return v_res_1076_;
}
pub unsafe fn lean_mk_io_error_permission_denied(
    mut v_osCode_1077_: u32,
    mut v_details_1078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1079_ = leanh::lean_box(0);
    v___x_1080_ = leanh::lean_alloc_ctor(13, 2, (4) as u32);
    leanh::lean_ctor_set(v___x_1080_, 0, v___x_1079_);
    leanh::lean_ctor_set(v___x_1080_, 1, v_details_1078_);
    leanh::lean_ctor_set_uint32(
        v___x_1080_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v_osCode_1077_,
    );
    return v___x_1080_;
}
pub unsafe fn l_IO_Error_mkPermissionDenied___boxed(
    mut v_osCode_1081_: *mut leanh::LeanObject,
    mut v_details_1082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_osCode_boxed_1083_: u32 = 0;
    let mut v_res_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1083_ = leanh::lean_unbox_uint32(v_osCode_1081_);
    leanh::lean_dec(v_osCode_1081_);
    v_res_1084_ = lean_mk_io_error_permission_denied(v_osCode_boxed_1083_, v_details_1082_);
    return v_res_1084_;
}
pub unsafe fn lean_mk_io_error_hardware_fault(
    mut v_osCode_1085_: u32,
    mut v_details_1086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1087_ = leanh::lean_alloc_ctor(5, 1, (4) as u32);
    leanh::lean_ctor_set(v___x_1087_, 0, v_details_1086_);
    leanh::lean_ctor_set_uint32(
        v___x_1087_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_osCode_1085_,
    );
    return v___x_1087_;
}
pub unsafe fn l_IO_Error_mkHardwareFault___boxed(
    mut v_osCode_1088_: *mut leanh::LeanObject,
    mut v_details_1089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_osCode_boxed_1090_: u32 = 0;
    let mut v_res_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1090_ = leanh::lean_unbox_uint32(v_osCode_1088_);
    leanh::lean_dec(v_osCode_1088_);
    v_res_1091_ = lean_mk_io_error_hardware_fault(v_osCode_boxed_1090_, v_details_1089_);
    return v_res_1091_;
}
pub unsafe fn lean_mk_io_error_unsatisfied_constraints(
    mut v_osCode_1092_: u32,
    mut v_details_1093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1094_ = leanh::lean_alloc_ctor(6, 1, (4) as u32);
    leanh::lean_ctor_set(v___x_1094_, 0, v_details_1093_);
    leanh::lean_ctor_set_uint32(
        v___x_1094_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_osCode_1092_,
    );
    return v___x_1094_;
}
pub unsafe fn l_IO_Error_mkUnsatisfiedConstraints___boxed(
    mut v_osCode_1095_: *mut leanh::LeanObject,
    mut v_details_1096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_osCode_boxed_1097_: u32 = 0;
    let mut v_res_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1097_ = leanh::lean_unbox_uint32(v_osCode_1095_);
    leanh::lean_dec(v_osCode_1095_);
    v_res_1098_ = lean_mk_io_error_unsatisfied_constraints(v_osCode_boxed_1097_, v_details_1096_);
    return v_res_1098_;
}
pub unsafe fn lean_mk_io_error_illegal_operation(
    mut v_osCode_1099_: u32,
    mut v_details_1100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1101_ = leanh::lean_alloc_ctor(7, 1, (4) as u32);
    leanh::lean_ctor_set(v___x_1101_, 0, v_details_1100_);
    leanh::lean_ctor_set_uint32(
        v___x_1101_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_osCode_1099_,
    );
    return v___x_1101_;
}
pub unsafe fn l_IO_Error_mkIllegalOperation___boxed(
    mut v_osCode_1102_: *mut leanh::LeanObject,
    mut v_details_1103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_osCode_boxed_1104_: u32 = 0;
    let mut v_res_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1104_ = leanh::lean_unbox_uint32(v_osCode_1102_);
    leanh::lean_dec(v_osCode_1102_);
    v_res_1105_ = lean_mk_io_error_illegal_operation(v_osCode_boxed_1104_, v_details_1103_);
    return v_res_1105_;
}
pub unsafe fn lean_mk_io_error_protocol_error(
    mut v_osCode_1106_: u32,
    mut v_details_1107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1108_ = leanh::lean_alloc_ctor(8, 1, (4) as u32);
    leanh::lean_ctor_set(v___x_1108_, 0, v_details_1107_);
    leanh::lean_ctor_set_uint32(
        v___x_1108_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_osCode_1106_,
    );
    return v___x_1108_;
}
pub unsafe fn l_IO_Error_mkProtocolError___boxed(
    mut v_osCode_1109_: *mut leanh::LeanObject,
    mut v_details_1110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_osCode_boxed_1111_: u32 = 0;
    let mut v_res_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1111_ = leanh::lean_unbox_uint32(v_osCode_1109_);
    leanh::lean_dec(v_osCode_1109_);
    v_res_1112_ = lean_mk_io_error_protocol_error(v_osCode_boxed_1111_, v_details_1110_);
    return v_res_1112_;
}
pub unsafe fn lean_mk_io_error_time_expired(
    mut v_osCode_1113_: u32,
    mut v_details_1114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1115_ = leanh::lean_alloc_ctor(9, 1, (4) as u32);
    leanh::lean_ctor_set(v___x_1115_, 0, v_details_1114_);
    leanh::lean_ctor_set_uint32(
        v___x_1115_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_osCode_1113_,
    );
    return v___x_1115_;
}
pub unsafe fn l_IO_Error_mkTimeExpired___boxed(
    mut v_osCode_1116_: *mut leanh::LeanObject,
    mut v_details_1117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_osCode_boxed_1118_: u32 = 0;
    let mut v_res_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1118_ = leanh::lean_unbox_uint32(v_osCode_1116_);
    leanh::lean_dec(v_osCode_1116_);
    v_res_1119_ = lean_mk_io_error_time_expired(v_osCode_boxed_1118_, v_details_1117_);
    return v_res_1119_;
}
pub unsafe fn l___private_Init_System_IOError_0__IO_Error_downCaseFirst(
    mut v_s_1120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: u32 = 0;
    let mut v___x_1123_: u32 = 0;
    let mut v___x_1124_: u8 = 0;
    v___x_1121_ = leanh::lean_unsigned_to_nat(0);
    v___x_1122_ = lean_string_utf8_get(v_s_1120_, v___x_1121_);
    v___x_1123_ = 65;
    v___x_1124_ = lean_uint32_dec_le(v___x_1123_, v___x_1122_);
    if v___x_1124_ == 0 {
        let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1125_ = lean_string_utf8_set(v_s_1120_, v___x_1121_, v___x_1122_);
        return v___x_1125_;
    } else {
        let mut v___x_1126_: u32 = 0;
        let mut v___x_1127_: u8 = 0;
        v___x_1126_ = 90;
        v___x_1127_ = lean_uint32_dec_le(v___x_1122_, v___x_1126_);
        if v___x_1127_ == 0 {
            let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1128_ = lean_string_utf8_set(v_s_1120_, v___x_1121_, v___x_1122_);
            return v___x_1128_;
        } else {
            let mut v___x_1129_: u32 = 0;
            let mut v___x_1130_: u32 = 0;
            let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1129_ = 32;
            v___x_1130_ = lean_uint32_add(v___x_1122_, v___x_1129_);
            v___x_1131_ = lean_string_utf8_set(v_s_1120_, v___x_1121_, v___x_1130_);
            return v___x_1131_;
        }
    }
}
pub unsafe fn l_IO_Error_fopenErrorToString(
    mut v_gist_1135_: *mut leanh::LeanObject,
    mut v_fn_1136_: *mut leanh::LeanObject,
    mut v_code_1137_: u32,
    mut v_x_1138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1138_) == 0 {
        let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1139_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_gist_1135_);
        v___x_1140_ = l_IO_Error_fopenErrorToString___closed__0;
        v___x_1141_ = lean_string_append(v___x_1139_, v___x_1140_);
        v___x_1142_ = lean_uint32_to_nat(v_code_1137_);
        v___x_1143_ = l_Nat_reprFast(v___x_1142_);
        v___x_1144_ = lean_string_append(v___x_1141_, v___x_1143_);
        leanh::lean_dec_ref(v___x_1143_);
        v___x_1145_ = l_IO_Error_fopenErrorToString___closed__1;
        v___x_1146_ = lean_string_append(v___x_1144_, v___x_1145_);
        v___x_1147_ = lean_string_append(v___x_1146_, v_fn_1136_);
        return v___x_1147_;
    } else {
        let mut v_val_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1148_ = leanh::lean_ctor_get(v_x_1138_, 0);
        leanh::lean_inc(v_val_1148_);
        leanh::lean_dec_ref_known(v_x_1138_, 1);
        v___x_1149_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_gist_1135_);
        v___x_1150_ = l_IO_Error_fopenErrorToString___closed__0;
        v___x_1151_ = lean_string_append(v___x_1149_, v___x_1150_);
        v___x_1152_ = lean_uint32_to_nat(v_code_1137_);
        v___x_1153_ = l_Nat_reprFast(v___x_1152_);
        v___x_1154_ = lean_string_append(v___x_1151_, v___x_1153_);
        leanh::lean_dec_ref(v___x_1153_);
        v___x_1155_ = l_IO_Error_fopenErrorToString___closed__2;
        v___x_1156_ = lean_string_append(v___x_1154_, v___x_1155_);
        v___x_1157_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_val_1148_);
        v___x_1158_ = lean_string_append(v___x_1156_, v___x_1157_);
        leanh::lean_dec_ref(v___x_1157_);
        v___x_1159_ = l_IO_Error_fopenErrorToString___closed__1;
        v___x_1160_ = lean_string_append(v___x_1158_, v___x_1159_);
        v___x_1161_ = lean_string_append(v___x_1160_, v_fn_1136_);
        return v___x_1161_;
    }
}
pub unsafe fn l_IO_Error_fopenErrorToString___boxed(
    mut v_gist_1162_: *mut leanh::LeanObject,
    mut v_fn_1163_: *mut leanh::LeanObject,
    mut v_code_1164_: *mut leanh::LeanObject,
    mut v_x_1165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_code_boxed_1166_: u32 = 0;
    let mut v_res_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_code_boxed_1166_ = leanh::lean_unbox_uint32(v_code_1164_);
    leanh::lean_dec(v_code_1164_);
    v_res_1167_ =
        l_IO_Error_fopenErrorToString(v_gist_1162_, v_fn_1163_, v_code_boxed_1166_, v_x_1165_);
    leanh::lean_dec_ref(v_fn_1163_);
    return v_res_1167_;
}
pub unsafe fn l_IO_Error_otherErrorToString(
    mut v_gist_1169_: *mut leanh::LeanObject,
    mut v_code_1170_: u32,
    mut v_x_1171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1171_) == 0 {
        let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1172_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_gist_1169_);
        v___x_1173_ = l_IO_Error_fopenErrorToString___closed__0;
        v___x_1174_ = lean_string_append(v___x_1172_, v___x_1173_);
        v___x_1175_ = lean_uint32_to_nat(v_code_1170_);
        v___x_1176_ = l_Nat_reprFast(v___x_1175_);
        v___x_1177_ = lean_string_append(v___x_1174_, v___x_1176_);
        leanh::lean_dec_ref(v___x_1176_);
        v___x_1178_ = l_IO_Error_otherErrorToString___closed__0;
        v___x_1179_ = lean_string_append(v___x_1177_, v___x_1178_);
        return v___x_1179_;
    } else {
        let mut v_val_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1180_ = leanh::lean_ctor_get(v_x_1171_, 0);
        leanh::lean_inc(v_val_1180_);
        leanh::lean_dec_ref_known(v_x_1171_, 1);
        v___x_1181_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_gist_1169_);
        v___x_1182_ = l_IO_Error_fopenErrorToString___closed__0;
        v___x_1183_ = lean_string_append(v___x_1181_, v___x_1182_);
        v___x_1184_ = lean_uint32_to_nat(v_code_1170_);
        v___x_1185_ = l_Nat_reprFast(v___x_1184_);
        v___x_1186_ = lean_string_append(v___x_1183_, v___x_1185_);
        leanh::lean_dec_ref(v___x_1185_);
        v___x_1187_ = l_IO_Error_fopenErrorToString___closed__2;
        v___x_1188_ = lean_string_append(v___x_1186_, v___x_1187_);
        v___x_1189_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_val_1180_);
        v___x_1190_ = lean_string_append(v___x_1188_, v___x_1189_);
        leanh::lean_dec_ref(v___x_1189_);
        v___x_1191_ = l_IO_Error_otherErrorToString___closed__0;
        v___x_1192_ = lean_string_append(v___x_1190_, v___x_1191_);
        return v___x_1192_;
    }
}
pub unsafe fn l_IO_Error_otherErrorToString___boxed(
    mut v_gist_1193_: *mut leanh::LeanObject,
    mut v_code_1194_: *mut leanh::LeanObject,
    mut v_x_1195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_code_boxed_1196_: u32 = 0;
    let mut v_res_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_code_boxed_1196_ = leanh::lean_unbox_uint32(v_code_1194_);
    leanh::lean_dec(v_code_1194_);
    v_res_1197_ = l_IO_Error_otherErrorToString(v_gist_1193_, v_code_boxed_1196_, v_x_1195_);
    return v_res_1197_;
}
pub unsafe fn lean_io_error_to_string(
    mut v_x_1214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_code_1216_: u32 = 0;
    let mut v_details_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_filename_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_osCode_1221_: u32 = 0;
    let mut v_details_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_osCode_1226_: u32 = 0;
    let mut v_details_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1231_: u8 = 0;
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1237_: u8 = 0;
    let mut v_osCode_1238_: u32 = 0;
    let mut v_details_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_osCode_1240_: u32 = 0;
    let mut v_details_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_osCode_1245_: u32 = 0;
    let mut v_details_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_osCode_1250_: u32 = 0;
    let mut v_details_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_osCode_1255_: u32 = 0;
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_osCode_1259_: u32 = 0;
    let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_osCode_1263_: u32 = 0;
    let mut v_details_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_osCode_1268_: u32 = 0;
    let mut v_details_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_osCode_1273_: u32 = 0;
    let mut v_details_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_filename_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_osCode_1279_: u32 = 0;
    let mut v_details_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_filename_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_osCode_1285_: u32 = 0;
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_filename_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_osCode_1290_: u32 = 0;
    let mut v_details_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_osCode_1295_: u32 = 0;
    let mut v_details_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1300_: u8 = 0;
    let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1306_: u8 = 0;
    let mut v_filename_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_osCode_1308_: u32 = 0;
    let mut v_details_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_osCode_1310_: u32 = 0;
    let mut v_details_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_filename_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_osCode_1316_: u32 = 0;
    let mut v_details_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_osCode_1321_: u32 = 0;
    let mut v_details_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1326_: u8 = 0;
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1332_: u8 = 0;
    let mut v_filename_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_osCode_1334_: u32 = 0;
    let mut v_details_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_osCode_1339_: u32 = 0;
    let mut v_details_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1344_: u8 = 0;
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1350_: u8 = 0;
    let mut v_filename_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_osCode_1352_: u32 = 0;
    let mut v_details_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_osCode_1357_: u32 = 0;
    let mut v_details_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1362_: u8 = 0;
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1368_: u8 = 0;
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1214_) {
                0 => {
                    v_filename_1220_ = leanh::lean_ctor_get(v_x_1214_, 0);
                    leanh::lean_inc(v_filename_1220_);
                    if leanh::lean_obj_tag(v_filename_1220_) == 0 {
                        v_osCode_1221_ = leanh::lean_ctor_get_uint32(
                            v_x_1214_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v_details_1222_ = leanh::lean_ctor_get(v_x_1214_, 1);
                        leanh::lean_inc_ref(v_details_1222_);
                        leanh::lean_dec_ref_known(v_x_1214_, 2);
                        v___x_1223_ = l_IO_Error_toString___closed__0;
                        v___x_1224_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1224_, 0, v_details_1222_);
                        v___x_1225_ =
                            l_IO_Error_otherErrorToString(v___x_1223_, v_osCode_1221_, v___x_1224_);
                        return v___x_1225_;
                    } else {
                        v_osCode_1226_ = leanh::lean_ctor_get_uint32(
                            v_x_1214_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v_details_1227_ = leanh::lean_ctor_get(v_x_1214_, 1);
                        leanh::lean_inc_ref(v_details_1227_);
                        leanh::lean_dec_ref_known(v_x_1214_, 2);
                        v_val_1228_ = leanh::lean_ctor_get(v_filename_1220_, 0);
                        v_isSharedCheck_1237_ =
                            (!leanh::lean_is_exclusive(v_filename_1220_)) as u8;
                        if v_isSharedCheck_1237_ == 0 {
                            v___x_1230_ = v_filename_1220_;
                            v_isShared_1231_ = v_isSharedCheck_1237_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1228_);
                            leanh::lean_dec(v_filename_1220_);
                            v___x_1230_ = leanh::lean_box(0);
                            v_isShared_1231_ = v_isSharedCheck_1237_;
                            state = 2;
                            continue;
                        }
                    }
                }
                1 => {
                    v_osCode_1238_ = leanh::lean_ctor_get_uint32(
                        v_x_1214_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    v_details_1239_ = leanh::lean_ctor_get(v_x_1214_, 0);
                    leanh::lean_inc_ref(v_details_1239_);
                    leanh::lean_dec_ref_known(v_x_1214_, 1);
                    v_code_1216_ = v_osCode_1238_;
                    v_details_1217_ = v_details_1239_;
                    state = 1;
                    continue;
                }
                2 => {
                    v_osCode_1240_ = leanh::lean_ctor_get_uint32(
                        v_x_1214_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    v_details_1241_ = leanh::lean_ctor_get(v_x_1214_, 0);
                    leanh::lean_inc_ref(v_details_1241_);
                    leanh::lean_dec_ref_known(v_x_1214_, 1);
                    v___x_1242_ = l_IO_Error_toString___closed__1;
                    v___x_1243_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1243_, 0, v_details_1241_);
                    v___x_1244_ =
                        l_IO_Error_otherErrorToString(v___x_1242_, v_osCode_1240_, v___x_1243_);
                    return v___x_1244_;
                }
                3 => {
                    v_osCode_1245_ = leanh::lean_ctor_get_uint32(
                        v_x_1214_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    v_details_1246_ = leanh::lean_ctor_get(v_x_1214_, 0);
                    leanh::lean_inc_ref(v_details_1246_);
                    leanh::lean_dec_ref_known(v_x_1214_, 1);
                    v___x_1247_ = l_IO_Error_toString___closed__2;
                    v___x_1248_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1248_, 0, v_details_1246_);
                    v___x_1249_ =
                        l_IO_Error_otherErrorToString(v___x_1247_, v_osCode_1245_, v___x_1248_);
                    return v___x_1249_;
                }
                4 => {
                    v_osCode_1250_ = leanh::lean_ctor_get_uint32(
                        v_x_1214_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    v_details_1251_ = leanh::lean_ctor_get(v_x_1214_, 0);
                    leanh::lean_inc_ref(v_details_1251_);
                    leanh::lean_dec_ref_known(v_x_1214_, 1);
                    v___x_1252_ = l_IO_Error_toString___closed__3;
                    v___x_1253_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1253_, 0, v_details_1251_);
                    v___x_1254_ =
                        l_IO_Error_otherErrorToString(v___x_1252_, v_osCode_1250_, v___x_1253_);
                    return v___x_1254_;
                }
                5 => {
                    v_osCode_1255_ = leanh::lean_ctor_get_uint32(
                        v_x_1214_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    leanh::lean_dec_ref_known(v_x_1214_, 1);
                    v___x_1256_ = l_IO_Error_toString___closed__4;
                    v___x_1257_ = leanh::lean_box(0);
                    v___x_1258_ =
                        l_IO_Error_otherErrorToString(v___x_1256_, v_osCode_1255_, v___x_1257_);
                    return v___x_1258_;
                }
                6 => {
                    v_osCode_1259_ = leanh::lean_ctor_get_uint32(
                        v_x_1214_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    leanh::lean_dec_ref_known(v_x_1214_, 1);
                    v___x_1260_ = l_IO_Error_toString___closed__5;
                    v___x_1261_ = leanh::lean_box(0);
                    v___x_1262_ =
                        l_IO_Error_otherErrorToString(v___x_1260_, v_osCode_1259_, v___x_1261_);
                    return v___x_1262_;
                }
                7 => {
                    v_osCode_1263_ = leanh::lean_ctor_get_uint32(
                        v_x_1214_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    v_details_1264_ = leanh::lean_ctor_get(v_x_1214_, 0);
                    leanh::lean_inc_ref(v_details_1264_);
                    leanh::lean_dec_ref_known(v_x_1214_, 1);
                    v___x_1265_ = l_IO_Error_toString___closed__6;
                    v___x_1266_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1266_, 0, v_details_1264_);
                    v___x_1267_ =
                        l_IO_Error_otherErrorToString(v___x_1265_, v_osCode_1263_, v___x_1266_);
                    return v___x_1267_;
                }
                8 => {
                    v_osCode_1268_ = leanh::lean_ctor_get_uint32(
                        v_x_1214_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    v_details_1269_ = leanh::lean_ctor_get(v_x_1214_, 0);
                    leanh::lean_inc_ref(v_details_1269_);
                    leanh::lean_dec_ref_known(v_x_1214_, 1);
                    v___x_1270_ = l_IO_Error_toString___closed__7;
                    v___x_1271_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1271_, 0, v_details_1269_);
                    v___x_1272_ =
                        l_IO_Error_otherErrorToString(v___x_1270_, v_osCode_1268_, v___x_1271_);
                    return v___x_1272_;
                }
                9 => {
                    v_osCode_1273_ = leanh::lean_ctor_get_uint32(
                        v_x_1214_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    v_details_1274_ = leanh::lean_ctor_get(v_x_1214_, 0);
                    leanh::lean_inc_ref(v_details_1274_);
                    leanh::lean_dec_ref_known(v_x_1214_, 1);
                    v___x_1275_ = l_IO_Error_toString___closed__8;
                    v___x_1276_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1276_, 0, v_details_1274_);
                    v___x_1277_ =
                        l_IO_Error_otherErrorToString(v___x_1275_, v_osCode_1273_, v___x_1276_);
                    return v___x_1277_;
                }
                10 => {
                    v_filename_1278_ = leanh::lean_ctor_get(v_x_1214_, 0);
                    leanh::lean_inc_ref(v_filename_1278_);
                    v_osCode_1279_ = leanh::lean_ctor_get_uint32(
                        v_x_1214_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v_details_1280_ = leanh::lean_ctor_get(v_x_1214_, 1);
                    leanh::lean_inc_ref(v_details_1280_);
                    leanh::lean_dec_ref_known(v_x_1214_, 2);
                    v___x_1281_ = l_IO_Error_toString___closed__9;
                    v___x_1282_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1282_, 0, v_details_1280_);
                    v___x_1283_ = l_IO_Error_fopenErrorToString(
                        v___x_1281_,
                        v_filename_1278_,
                        v_osCode_1279_,
                        v___x_1282_,
                    );
                    leanh::lean_dec_ref(v_filename_1278_);
                    return v___x_1283_;
                }
                11 => {
                    v_filename_1284_ = leanh::lean_ctor_get(v_x_1214_, 0);
                    leanh::lean_inc_ref(v_filename_1284_);
                    v_osCode_1285_ = leanh::lean_ctor_get_uint32(
                        v_x_1214_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    leanh::lean_dec_ref_known(v_x_1214_, 2);
                    v___x_1286_ = l_IO_Error_toString___closed__10;
                    v___x_1287_ = leanh::lean_box(0);
                    v___x_1288_ = l_IO_Error_fopenErrorToString(
                        v___x_1286_,
                        v_filename_1284_,
                        v_osCode_1285_,
                        v___x_1287_,
                    );
                    leanh::lean_dec_ref(v_filename_1284_);
                    return v___x_1288_;
                }
                12 => {
                    v_filename_1289_ = leanh::lean_ctor_get(v_x_1214_, 0);
                    leanh::lean_inc(v_filename_1289_);
                    if leanh::lean_obj_tag(v_filename_1289_) == 0 {
                        v_osCode_1290_ = leanh::lean_ctor_get_uint32(
                            v_x_1214_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v_details_1291_ = leanh::lean_ctor_get(v_x_1214_, 1);
                        leanh::lean_inc_ref(v_details_1291_);
                        leanh::lean_dec_ref_known(v_x_1214_, 2);
                        v___x_1292_ = l_IO_Error_toString___closed__11;
                        v___x_1293_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1293_, 0, v_details_1291_);
                        v___x_1294_ =
                            l_IO_Error_otherErrorToString(v___x_1292_, v_osCode_1290_, v___x_1293_);
                        return v___x_1294_;
                    } else {
                        v_osCode_1295_ = leanh::lean_ctor_get_uint32(
                            v_x_1214_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v_details_1296_ = leanh::lean_ctor_get(v_x_1214_, 1);
                        leanh::lean_inc_ref(v_details_1296_);
                        leanh::lean_dec_ref_known(v_x_1214_, 2);
                        v_val_1297_ = leanh::lean_ctor_get(v_filename_1289_, 0);
                        v_isSharedCheck_1306_ =
                            (!leanh::lean_is_exclusive(v_filename_1289_)) as u8;
                        if v_isSharedCheck_1306_ == 0 {
                            v___x_1299_ = v_filename_1289_;
                            v_isShared_1300_ = v_isSharedCheck_1306_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1297_);
                            leanh::lean_dec(v_filename_1289_);
                            v___x_1299_ = leanh::lean_box(0);
                            v_isShared_1300_ = v_isSharedCheck_1306_;
                            state = 4;
                            continue;
                        }
                    }
                }
                13 => {
                    v_filename_1307_ = leanh::lean_ctor_get(v_x_1214_, 0);
                    if leanh::lean_obj_tag(v_filename_1307_) == 0 {
                        v_osCode_1308_ = leanh::lean_ctor_get_uint32(
                            v_x_1214_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v_details_1309_ = leanh::lean_ctor_get(v_x_1214_, 1);
                        leanh::lean_inc_ref(v_details_1309_);
                        leanh::lean_dec_ref_known(v_x_1214_, 2);
                        v_code_1216_ = v_osCode_1308_;
                        v_details_1217_ = v_details_1309_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc_ref(v_filename_1307_);
                        v_osCode_1310_ = leanh::lean_ctor_get_uint32(
                            v_x_1214_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v_details_1311_ = leanh::lean_ctor_get(v_x_1214_, 1);
                        leanh::lean_inc_ref(v_details_1311_);
                        leanh::lean_dec_ref_known(v_x_1214_, 2);
                        v_val_1312_ = leanh::lean_ctor_get(v_filename_1307_, 0);
                        leanh::lean_inc(v_val_1312_);
                        leanh::lean_dec_ref_known(v_filename_1307_, 1);
                        v___x_1313_ = leanh::lean_box(0);
                        v___x_1314_ = l_IO_Error_fopenErrorToString(
                            v_details_1311_,
                            v_val_1312_,
                            v_osCode_1310_,
                            v___x_1313_,
                        );
                        leanh::lean_dec(v_val_1312_);
                        return v___x_1314_;
                    }
                }
                14 => {
                    v_filename_1315_ = leanh::lean_ctor_get(v_x_1214_, 0);
                    leanh::lean_inc(v_filename_1315_);
                    if leanh::lean_obj_tag(v_filename_1315_) == 0 {
                        v_osCode_1316_ = leanh::lean_ctor_get_uint32(
                            v_x_1214_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v_details_1317_ = leanh::lean_ctor_get(v_x_1214_, 1);
                        leanh::lean_inc_ref(v_details_1317_);
                        leanh::lean_dec_ref_known(v_x_1214_, 2);
                        v___x_1318_ = l_IO_Error_toString___closed__12;
                        v___x_1319_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1319_, 0, v_details_1317_);
                        v___x_1320_ =
                            l_IO_Error_otherErrorToString(v___x_1318_, v_osCode_1316_, v___x_1319_);
                        return v___x_1320_;
                    } else {
                        v_osCode_1321_ = leanh::lean_ctor_get_uint32(
                            v_x_1214_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v_details_1322_ = leanh::lean_ctor_get(v_x_1214_, 1);
                        leanh::lean_inc_ref(v_details_1322_);
                        leanh::lean_dec_ref_known(v_x_1214_, 2);
                        v_val_1323_ = leanh::lean_ctor_get(v_filename_1315_, 0);
                        v_isSharedCheck_1332_ =
                            (!leanh::lean_is_exclusive(v_filename_1315_)) as u8;
                        if v_isSharedCheck_1332_ == 0 {
                            v___x_1325_ = v_filename_1315_;
                            v_isShared_1326_ = v_isSharedCheck_1332_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1323_);
                            leanh::lean_dec(v_filename_1315_);
                            v___x_1325_ = leanh::lean_box(0);
                            v_isShared_1326_ = v_isSharedCheck_1332_;
                            state = 6;
                            continue;
                        }
                    }
                }
                15 => {
                    v_filename_1333_ = leanh::lean_ctor_get(v_x_1214_, 0);
                    leanh::lean_inc(v_filename_1333_);
                    if leanh::lean_obj_tag(v_filename_1333_) == 0 {
                        v_osCode_1334_ = leanh::lean_ctor_get_uint32(
                            v_x_1214_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v_details_1335_ = leanh::lean_ctor_get(v_x_1214_, 1);
                        leanh::lean_inc_ref(v_details_1335_);
                        leanh::lean_dec_ref_known(v_x_1214_, 2);
                        v___x_1336_ = l_IO_Error_toString___closed__13;
                        v___x_1337_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1337_, 0, v_details_1335_);
                        v___x_1338_ =
                            l_IO_Error_otherErrorToString(v___x_1336_, v_osCode_1334_, v___x_1337_);
                        return v___x_1338_;
                    } else {
                        v_osCode_1339_ = leanh::lean_ctor_get_uint32(
                            v_x_1214_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v_details_1340_ = leanh::lean_ctor_get(v_x_1214_, 1);
                        leanh::lean_inc_ref(v_details_1340_);
                        leanh::lean_dec_ref_known(v_x_1214_, 2);
                        v_val_1341_ = leanh::lean_ctor_get(v_filename_1333_, 0);
                        v_isSharedCheck_1350_ =
                            (!leanh::lean_is_exclusive(v_filename_1333_)) as u8;
                        if v_isSharedCheck_1350_ == 0 {
                            v___x_1343_ = v_filename_1333_;
                            v_isShared_1344_ = v_isSharedCheck_1350_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1341_);
                            leanh::lean_dec(v_filename_1333_);
                            v___x_1343_ = leanh::lean_box(0);
                            v_isShared_1344_ = v_isSharedCheck_1350_;
                            state = 8;
                            continue;
                        }
                    }
                }
                16 => {
                    v_filename_1351_ = leanh::lean_ctor_get(v_x_1214_, 0);
                    leanh::lean_inc(v_filename_1351_);
                    if leanh::lean_obj_tag(v_filename_1351_) == 0 {
                        v_osCode_1352_ = leanh::lean_ctor_get_uint32(
                            v_x_1214_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v_details_1353_ = leanh::lean_ctor_get(v_x_1214_, 1);
                        leanh::lean_inc_ref(v_details_1353_);
                        leanh::lean_dec_ref_known(v_x_1214_, 2);
                        v___x_1354_ = l_IO_Error_toString___closed__14;
                        v___x_1355_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1355_, 0, v_details_1353_);
                        v___x_1356_ =
                            l_IO_Error_otherErrorToString(v___x_1354_, v_osCode_1352_, v___x_1355_);
                        return v___x_1356_;
                    } else {
                        v_osCode_1357_ = leanh::lean_ctor_get_uint32(
                            v_x_1214_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v_details_1358_ = leanh::lean_ctor_get(v_x_1214_, 1);
                        leanh::lean_inc_ref(v_details_1358_);
                        leanh::lean_dec_ref_known(v_x_1214_, 2);
                        v_val_1359_ = leanh::lean_ctor_get(v_filename_1351_, 0);
                        v_isSharedCheck_1368_ =
                            (!leanh::lean_is_exclusive(v_filename_1351_)) as u8;
                        if v_isSharedCheck_1368_ == 0 {
                            v___x_1361_ = v_filename_1351_;
                            v_isShared_1362_ = v_isSharedCheck_1368_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1359_);
                            leanh::lean_dec(v_filename_1351_);
                            v___x_1361_ = leanh::lean_box(0);
                            v_isShared_1362_ = v_isSharedCheck_1368_;
                            state = 10;
                            continue;
                        }
                    }
                }
                17 => {
                    v___x_1369_ = l_IO_Error_toString___closed__15;
                    return v___x_1369_;
                }
                _ => {
                    v_msg_1370_ = leanh::lean_ctor_get(v_x_1214_, 0);
                    leanh::lean_inc_ref(v_msg_1370_);
                    leanh::lean_dec_ref_known(v_x_1214_, 1);
                    return v_msg_1370_;
                }
            },
            1 => {
                v___x_1218_ = leanh::lean_box(0);
                v___x_1219_ =
                    l_IO_Error_otherErrorToString(v_details_1217_, v_code_1216_, v___x_1218_);
                return v___x_1219_;
            }
            2 => {
                v___x_1232_ = l_IO_Error_toString___closed__0;
                if v_isShared_1231_ == 0 {
                    leanh::lean_ctor_set(v___x_1230_, 0, v_details_1227_);
                    v___x_1234_ = v___x_1230_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1236_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_details_1227_);
                    v___x_1234_ = v_reuseFailAlloc_1236_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1235_ = l_IO_Error_fopenErrorToString(
                    v___x_1232_,
                    v_val_1228_,
                    v_osCode_1226_,
                    v___x_1234_,
                );
                leanh::lean_dec(v_val_1228_);
                return v___x_1235_;
            }
            4 => {
                v___x_1301_ = l_IO_Error_toString___closed__11;
                if v_isShared_1300_ == 0 {
                    leanh::lean_ctor_set(v___x_1299_, 0, v_details_1296_);
                    v___x_1303_ = v___x_1299_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1305_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_details_1296_);
                    v___x_1303_ = v_reuseFailAlloc_1305_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1304_ = l_IO_Error_fopenErrorToString(
                    v___x_1301_,
                    v_val_1297_,
                    v_osCode_1295_,
                    v___x_1303_,
                );
                leanh::lean_dec(v_val_1297_);
                return v___x_1304_;
            }
            6 => {
                v___x_1327_ = l_IO_Error_toString___closed__12;
                if v_isShared_1326_ == 0 {
                    leanh::lean_ctor_set(v___x_1325_, 0, v_details_1322_);
                    v___x_1329_ = v___x_1325_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1331_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_details_1322_);
                    v___x_1329_ = v_reuseFailAlloc_1331_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1330_ = l_IO_Error_fopenErrorToString(
                    v___x_1327_,
                    v_val_1323_,
                    v_osCode_1321_,
                    v___x_1329_,
                );
                leanh::lean_dec(v_val_1323_);
                return v___x_1330_;
            }
            8 => {
                v___x_1345_ = l_IO_Error_toString___closed__13;
                if v_isShared_1344_ == 0 {
                    leanh::lean_ctor_set(v___x_1343_, 0, v_details_1340_);
                    v___x_1347_ = v___x_1343_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1349_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_details_1340_);
                    v___x_1347_ = v_reuseFailAlloc_1349_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1348_ = l_IO_Error_fopenErrorToString(
                    v___x_1345_,
                    v_val_1341_,
                    v_osCode_1339_,
                    v___x_1347_,
                );
                leanh::lean_dec(v_val_1341_);
                return v___x_1348_;
            }
            10 => {
                v___x_1363_ = l_IO_Error_toString___closed__14;
                if v_isShared_1362_ == 0 {
                    leanh::lean_ctor_set(v___x_1361_, 0, v_details_1358_);
                    v___x_1365_ = v___x_1361_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1367_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_details_1358_);
                    v___x_1365_ = v_reuseFailAlloc_1367_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_1366_ = l_IO_Error_fopenErrorToString(
                    v___x_1363_,
                    v_val_1359_,
                    v_osCode_1357_,
                    v___x_1365_,
                );
                leanh::lean_dec(v_val_1359_);
                return v___x_1366_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_System_IOError(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Modify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_System_IOError(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_System_IOError(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Modify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_IOError(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_System_IOError(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_System_IOError(builtin);
}
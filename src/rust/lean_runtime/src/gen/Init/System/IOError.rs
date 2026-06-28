// Lean compiler output
// Module: Init.System.IOError
// Imports: Init.Data.ToString.Basic Init.Data.String.Modify
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Modify::{
    initialize_Init_Data_String_Modify, runtime_initialize_Init_Data_String_Modify,
};
use crate::r#gen::Init::Data::ToString::Basic::{
    initialize_Init_Data_ToString_Basic, runtime_initialize_Init_Data_ToString_Basic,
};
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_utf8_get;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Modify::lean_string_utf8_set;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_uint32_add;
use crate::lean_imports_rs::Init::Prelude::{lean_uint32_dec_le, lean_uint32_to_nat};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_apply_3,
    lean_box, lean_box_uint32, lean_ctor_get, lean_ctor_get_uint32, lean_ctor_set,
    lean_ctor_set_uint32, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
    lean_unbox_uint32, lean_unsigned_to_nat,
};
pub static l_instInhabitedError___closed__0_value: LeanStringObject<37> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        40, 96, 73, 110, 104, 97, 98, 105, 116, 101, 100, 46, 100, 101, 102, 97, 117, 108, 116, 96,
        32, 102, 111, 114, 32, 96, 73, 79, 46, 69, 114, 114, 111, 114, 96, 41, 0,
    ],
};
static mut l_instInhabitedError___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instInhabitedError___closed__0_value) as *mut LeanObject;
pub static l_instInhabitedError___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 18,
    },
    m_objs: [core::ptr::addr_of!(l_instInhabitedError___closed__0_value) as *mut LeanObject],
};
static mut l_instInhabitedError___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_instInhabitedError___closed__1_value) as *mut LeanObject;
pub static mut l_instInhabitedError: *mut LeanObject =
    core::ptr::addr_of!(l_instInhabitedError___closed__1_value) as *mut LeanObject;
pub static l_instCoeStringError___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: lean_mk_io_user_error as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instCoeStringError___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instCoeStringError___closed__0_value) as *mut LeanObject;
pub static mut l_instCoeStringError: *mut LeanObject =
    core::ptr::addr_of!(l_instCoeStringError___closed__0_value) as *mut LeanObject;
pub static l_IO_Error_fopenErrorToString___closed__0_value: LeanStringObject<15> =
    LeanStringObject {
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
            32, 40, 101, 114, 114, 111, 114, 32, 99, 111, 100, 101, 58, 32, 0,
        ],
    };
static mut l_IO_Error_fopenErrorToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Error_fopenErrorToString___closed__0_value) as *mut LeanObject;
pub static l_IO_Error_fopenErrorToString___closed__1_value: LeanStringObject<11> =
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
        m_data: [41, 10, 32, 32, 102, 105, 108, 101, 58, 32, 0],
    };
static mut l_IO_Error_fopenErrorToString___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Error_fopenErrorToString___closed__1_value) as *mut LeanObject;
pub static l_IO_Error_fopenErrorToString___closed__2_value: LeanStringObject<3> =
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
        m_data: [44, 32, 0],
    };
static mut l_IO_Error_fopenErrorToString___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Error_fopenErrorToString___closed__2_value) as *mut LeanObject;
pub static l_IO_Error_otherErrorToString___closed__0_value: LeanStringObject<2> =
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
        m_data: [41, 0],
    };
static mut l_IO_Error_otherErrorToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Error_otherErrorToString___closed__0_value) as *mut LeanObject;
pub static l_IO_Error_toString___closed__0_value: LeanStringObject<15> = LeanStringObject {
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
        97, 108, 114, 101, 97, 100, 121, 32, 101, 120, 105, 115, 116, 115, 0,
    ],
};
static mut l_IO_Error_toString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__0_value) as *mut LeanObject;
pub static l_IO_Error_toString___closed__1_value: LeanStringObject<14> = LeanStringObject {
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
        114, 101, 115, 111, 117, 114, 99, 101, 32, 98, 117, 115, 121, 0,
    ],
};
static mut l_IO_Error_toString___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__1_value) as *mut LeanObject;
pub static l_IO_Error_toString___closed__2_value: LeanStringObject<18> = LeanStringObject {
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
        114, 101, 115, 111, 117, 114, 99, 101, 32, 118, 97, 110, 105, 115, 104, 101, 100, 0,
    ],
};
static mut l_IO_Error_toString___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__2_value) as *mut LeanObject;
pub static l_IO_Error_toString___closed__3_value: LeanStringObject<22> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_IO_Error_toString___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__3_value) as *mut LeanObject;
pub static l_IO_Error_toString___closed__4_value: LeanStringObject<15> = LeanStringObject {
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
        104, 97, 114, 100, 119, 97, 114, 101, 32, 102, 97, 117, 108, 116, 0,
    ],
};
static mut l_IO_Error_toString___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__4_value) as *mut LeanObject;
pub static l_IO_Error_toString___closed__5_value: LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        100, 105, 114, 101, 99, 116, 111, 114, 121, 32, 110, 111, 116, 32, 101, 109, 112, 116, 121,
        0,
    ],
};
static mut l_IO_Error_toString___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__5_value) as *mut LeanObject;
pub static l_IO_Error_toString___closed__6_value: LeanStringObject<18> = LeanStringObject {
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
        105, 108, 108, 101, 103, 97, 108, 32, 111, 112, 101, 114, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l_IO_Error_toString___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__6_value) as *mut LeanObject;
pub static l_IO_Error_toString___closed__7_value: LeanStringObject<15> = LeanStringObject {
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
        112, 114, 111, 116, 111, 99, 111, 108, 32, 101, 114, 114, 111, 114, 0,
    ],
};
static mut l_IO_Error_toString___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__7_value) as *mut LeanObject;
pub static l_IO_Error_toString___closed__8_value: LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_IO_Error_toString___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__8_value) as *mut LeanObject;
pub static l_IO_Error_toString___closed__9_value: LeanStringObject<24> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        105, 110, 116, 101, 114, 114, 117, 112, 116, 101, 100, 32, 115, 121, 115, 116, 101, 109,
        32, 99, 97, 108, 108, 0,
    ],
};
static mut l_IO_Error_toString___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__9_value) as *mut LeanObject;
pub static l_IO_Error_toString___closed__10_value: LeanStringObject<26> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        110, 111, 32, 115, 117, 99, 104, 32, 102, 105, 108, 101, 32, 111, 114, 32, 100, 105, 114,
        101, 99, 116, 111, 114, 121, 0,
    ],
};
static mut l_IO_Error_toString___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__10_value) as *mut LeanObject;
pub static l_IO_Error_toString___closed__11_value: LeanStringObject<17> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_IO_Error_toString___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__11_value) as *mut LeanObject;
pub static l_IO_Error_toString___closed__12_value: LeanStringObject<19> = LeanStringObject {
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
        114, 101, 115, 111, 117, 114, 99, 101, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 0,
    ],
};
static mut l_IO_Error_toString___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__12_value) as *mut LeanObject;
pub static l_IO_Error_toString___closed__13_value: LeanStringObject<19> = LeanStringObject {
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
        105, 110, 97, 112, 112, 114, 111, 112, 114, 105, 97, 116, 101, 32, 116, 121, 112, 101, 0,
    ],
};
static mut l_IO_Error_toString___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__13_value) as *mut LeanObject;
pub static l_IO_Error_toString___closed__14_value: LeanStringObject<14> = LeanStringObject {
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
        110, 111, 32, 115, 117, 99, 104, 32, 116, 104, 105, 110, 103, 0,
    ],
};
static mut l_IO_Error_toString___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__14_value) as *mut LeanObject;
pub static l_IO_Error_toString___closed__15_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_IO_Error_toString___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Error_toString___closed__15_value) as *mut LeanObject;
pub static l_IO_Error_instToString___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: lean_io_error_to_string as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_IO_Error_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Error_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_IO_Error_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_IO_Error_instToString___closed__0_value) as *mut LeanObject;
pub unsafe fn l_IO_Error_ctorIdx(mut v_x_687_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_687_) {
        0 => {
            let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
            v___x_688_ = lean_unsigned_to_nat(0);
            return v___x_688_;
        }
        1 => {
            let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
            v___x_689_ = lean_unsigned_to_nat(1);
            return v___x_689_;
        }
        2 => {
            let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
            v___x_690_ = lean_unsigned_to_nat(2);
            return v___x_690_;
        }
        3 => {
            let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
            v___x_691_ = lean_unsigned_to_nat(3);
            return v___x_691_;
        }
        4 => {
            let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
            v___x_692_ = lean_unsigned_to_nat(4);
            return v___x_692_;
        }
        5 => {
            let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
            v___x_693_ = lean_unsigned_to_nat(5);
            return v___x_693_;
        }
        6 => {
            let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
            v___x_694_ = lean_unsigned_to_nat(6);
            return v___x_694_;
        }
        7 => {
            let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
            v___x_695_ = lean_unsigned_to_nat(7);
            return v___x_695_;
        }
        8 => {
            let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
            v___x_696_ = lean_unsigned_to_nat(8);
            return v___x_696_;
        }
        9 => {
            let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
            v___x_697_ = lean_unsigned_to_nat(9);
            return v___x_697_;
        }
        10 => {
            let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
            v___x_698_ = lean_unsigned_to_nat(10);
            return v___x_698_;
        }
        11 => {
            let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
            v___x_699_ = lean_unsigned_to_nat(11);
            return v___x_699_;
        }
        12 => {
            let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
            v___x_700_ = lean_unsigned_to_nat(12);
            return v___x_700_;
        }
        13 => {
            let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
            v___x_701_ = lean_unsigned_to_nat(13);
            return v___x_701_;
        }
        14 => {
            let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
            v___x_702_ = lean_unsigned_to_nat(14);
            return v___x_702_;
        }
        15 => {
            let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
            v___x_703_ = lean_unsigned_to_nat(15);
            return v___x_703_;
        }
        16 => {
            let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
            v___x_704_ = lean_unsigned_to_nat(16);
            return v___x_704_;
        }
        17 => {
            let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
            v___x_705_ = lean_unsigned_to_nat(17);
            return v___x_705_;
        }
        _ => {
            let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
            v___x_706_ = lean_unsigned_to_nat(18);
            return v___x_706_;
        }
    }
}
pub unsafe fn l_IO_Error_ctorIdx___boxed(mut v_x_707_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_708_: *mut LeanObject = core::ptr::null_mut();
    v_res_708_ = l_IO_Error_ctorIdx(v_x_707_);
    lean_dec(v_x_707_);
    return v_res_708_;
}
pub unsafe fn l_IO_Error_ctorElim___redArg(
    mut v_t_709_: *mut LeanObject,
    mut v_k_710_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_709_) {
        0 => {
            let mut v_filename_711_: *mut LeanObject = core::ptr::null_mut();
            let mut v_osCode_712_: u32 = 0;
            let mut v_details_713_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
            v_filename_711_ = lean_ctor_get(v_t_709_, 0);
            lean_inc(v_filename_711_);
            v_osCode_712_ = lean_ctor_get_uint32(
                v_t_709_,
                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
            );
            v_details_713_ = lean_ctor_get(v_t_709_, 1);
            lean_inc_ref(v_details_713_);
            lean_dec_ref_known(v_t_709_, 2);
            v___x_714_ = lean_box_uint32(v_osCode_712_);
            v___x_715_ = lean_apply_3(v_k_710_, v_filename_711_, v___x_714_, v_details_713_);
            return v___x_715_;
        }
        10 => {
            let mut v_filename_716_: *mut LeanObject = core::ptr::null_mut();
            let mut v_osCode_717_: u32 = 0;
            let mut v_details_718_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
            v_filename_716_ = lean_ctor_get(v_t_709_, 0);
            lean_inc_ref(v_filename_716_);
            v_osCode_717_ = lean_ctor_get_uint32(
                v_t_709_,
                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
            );
            v_details_718_ = lean_ctor_get(v_t_709_, 1);
            lean_inc_ref(v_details_718_);
            lean_dec_ref_known(v_t_709_, 2);
            v___x_719_ = lean_box_uint32(v_osCode_717_);
            v___x_720_ = lean_apply_3(v_k_710_, v_filename_716_, v___x_719_, v_details_718_);
            return v___x_720_;
        }
        11 => {
            let mut v_filename_721_: *mut LeanObject = core::ptr::null_mut();
            let mut v_osCode_722_: u32 = 0;
            let mut v_details_723_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
            v_filename_721_ = lean_ctor_get(v_t_709_, 0);
            lean_inc_ref(v_filename_721_);
            v_osCode_722_ = lean_ctor_get_uint32(
                v_t_709_,
                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
            );
            v_details_723_ = lean_ctor_get(v_t_709_, 1);
            lean_inc_ref(v_details_723_);
            lean_dec_ref_known(v_t_709_, 2);
            v___x_724_ = lean_box_uint32(v_osCode_722_);
            v___x_725_ = lean_apply_3(v_k_710_, v_filename_721_, v___x_724_, v_details_723_);
            return v___x_725_;
        }
        12 => {
            let mut v_filename_726_: *mut LeanObject = core::ptr::null_mut();
            let mut v_osCode_727_: u32 = 0;
            let mut v_details_728_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
            v_filename_726_ = lean_ctor_get(v_t_709_, 0);
            lean_inc(v_filename_726_);
            v_osCode_727_ = lean_ctor_get_uint32(
                v_t_709_,
                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
            );
            v_details_728_ = lean_ctor_get(v_t_709_, 1);
            lean_inc_ref(v_details_728_);
            lean_dec_ref_known(v_t_709_, 2);
            v___x_729_ = lean_box_uint32(v_osCode_727_);
            v___x_730_ = lean_apply_3(v_k_710_, v_filename_726_, v___x_729_, v_details_728_);
            return v___x_730_;
        }
        13 => {
            let mut v_filename_731_: *mut LeanObject = core::ptr::null_mut();
            let mut v_osCode_732_: u32 = 0;
            let mut v_details_733_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
            v_filename_731_ = lean_ctor_get(v_t_709_, 0);
            lean_inc(v_filename_731_);
            v_osCode_732_ = lean_ctor_get_uint32(
                v_t_709_,
                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
            );
            v_details_733_ = lean_ctor_get(v_t_709_, 1);
            lean_inc_ref(v_details_733_);
            lean_dec_ref_known(v_t_709_, 2);
            v___x_734_ = lean_box_uint32(v_osCode_732_);
            v___x_735_ = lean_apply_3(v_k_710_, v_filename_731_, v___x_734_, v_details_733_);
            return v___x_735_;
        }
        14 => {
            let mut v_filename_736_: *mut LeanObject = core::ptr::null_mut();
            let mut v_osCode_737_: u32 = 0;
            let mut v_details_738_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
            v_filename_736_ = lean_ctor_get(v_t_709_, 0);
            lean_inc(v_filename_736_);
            v_osCode_737_ = lean_ctor_get_uint32(
                v_t_709_,
                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
            );
            v_details_738_ = lean_ctor_get(v_t_709_, 1);
            lean_inc_ref(v_details_738_);
            lean_dec_ref_known(v_t_709_, 2);
            v___x_739_ = lean_box_uint32(v_osCode_737_);
            v___x_740_ = lean_apply_3(v_k_710_, v_filename_736_, v___x_739_, v_details_738_);
            return v___x_740_;
        }
        15 => {
            let mut v_filename_741_: *mut LeanObject = core::ptr::null_mut();
            let mut v_osCode_742_: u32 = 0;
            let mut v_details_743_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
            v_filename_741_ = lean_ctor_get(v_t_709_, 0);
            lean_inc(v_filename_741_);
            v_osCode_742_ = lean_ctor_get_uint32(
                v_t_709_,
                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
            );
            v_details_743_ = lean_ctor_get(v_t_709_, 1);
            lean_inc_ref(v_details_743_);
            lean_dec_ref_known(v_t_709_, 2);
            v___x_744_ = lean_box_uint32(v_osCode_742_);
            v___x_745_ = lean_apply_3(v_k_710_, v_filename_741_, v___x_744_, v_details_743_);
            return v___x_745_;
        }
        16 => {
            let mut v_filename_746_: *mut LeanObject = core::ptr::null_mut();
            let mut v_osCode_747_: u32 = 0;
            let mut v_details_748_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
            v_filename_746_ = lean_ctor_get(v_t_709_, 0);
            lean_inc(v_filename_746_);
            v_osCode_747_ = lean_ctor_get_uint32(
                v_t_709_,
                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
            );
            v_details_748_ = lean_ctor_get(v_t_709_, 1);
            lean_inc_ref(v_details_748_);
            lean_dec_ref_known(v_t_709_, 2);
            v___x_749_ = lean_box_uint32(v_osCode_747_);
            v___x_750_ = lean_apply_3(v_k_710_, v_filename_746_, v___x_749_, v_details_748_);
            return v___x_750_;
        }
        17 => {
            return v_k_710_;
        }
        18 => {
            let mut v_msg_751_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
            v_msg_751_ = lean_ctor_get(v_t_709_, 0);
            lean_inc_ref(v_msg_751_);
            lean_dec_ref_known(v_t_709_, 1);
            v___x_752_ = lean_apply_1(v_k_710_, v_msg_751_);
            return v___x_752_;
        }
        _ => {
            let mut v_osCode_753_: u32 = 0;
            let mut v_details_754_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
            v_osCode_753_ = lean_ctor_get_uint32(
                v_t_709_,
                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            );
            v_details_754_ = lean_ctor_get(v_t_709_, 0);
            lean_inc_ref(v_details_754_);
            lean_dec(v_t_709_);
            v___x_755_ = lean_box_uint32(v_osCode_753_);
            v___x_756_ = lean_apply_2(v_k_710_, v___x_755_, v_details_754_);
            return v___x_756_;
        }
    }
}
pub unsafe fn l_IO_Error_ctorElim(
    mut v_motive_757_: *mut LeanObject,
    mut v_ctorIdx_758_: *mut LeanObject,
    mut v_t_759_: *mut LeanObject,
    mut v_h_760_: *mut LeanObject,
    mut v_k_761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    v___x_762_ = l_IO_Error_ctorElim___redArg(v_t_759_, v_k_761_);
    return v___x_762_;
}
pub unsafe fn l_IO_Error_ctorElim___boxed(
    mut v_motive_763_: *mut LeanObject,
    mut v_ctorIdx_764_: *mut LeanObject,
    mut v_t_765_: *mut LeanObject,
    mut v_h_766_: *mut LeanObject,
    mut v_k_767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_768_: *mut LeanObject = core::ptr::null_mut();
    v_res_768_ = l_IO_Error_ctorElim(v_motive_763_, v_ctorIdx_764_, v_t_765_, v_h_766_, v_k_767_);
    lean_dec(v_ctorIdx_764_);
    return v_res_768_;
}
pub unsafe fn l_IO_Error_alreadyExists_elim___redArg(
    mut v_t_769_: *mut LeanObject,
    mut v_alreadyExists_770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    v___x_771_ = l_IO_Error_ctorElim___redArg(v_t_769_, v_alreadyExists_770_);
    return v___x_771_;
}
pub unsafe fn l_IO_Error_alreadyExists_elim(
    mut v_motive_772_: *mut LeanObject,
    mut v_t_773_: *mut LeanObject,
    mut v_h_774_: *mut LeanObject,
    mut v_alreadyExists_775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    v___x_776_ = l_IO_Error_ctorElim___redArg(v_t_773_, v_alreadyExists_775_);
    return v___x_776_;
}
pub unsafe fn l_IO_Error_otherError_elim___redArg(
    mut v_t_777_: *mut LeanObject,
    mut v_otherError_778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    v___x_779_ = l_IO_Error_ctorElim___redArg(v_t_777_, v_otherError_778_);
    return v___x_779_;
}
pub unsafe fn l_IO_Error_otherError_elim(
    mut v_motive_780_: *mut LeanObject,
    mut v_t_781_: *mut LeanObject,
    mut v_h_782_: *mut LeanObject,
    mut v_otherError_783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
    v___x_784_ = l_IO_Error_ctorElim___redArg(v_t_781_, v_otherError_783_);
    return v___x_784_;
}
pub unsafe fn l_IO_Error_resourceBusy_elim___redArg(
    mut v_t_785_: *mut LeanObject,
    mut v_resourceBusy_786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    v___x_787_ = l_IO_Error_ctorElim___redArg(v_t_785_, v_resourceBusy_786_);
    return v___x_787_;
}
pub unsafe fn l_IO_Error_resourceBusy_elim(
    mut v_motive_788_: *mut LeanObject,
    mut v_t_789_: *mut LeanObject,
    mut v_h_790_: *mut LeanObject,
    mut v_resourceBusy_791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    v___x_792_ = l_IO_Error_ctorElim___redArg(v_t_789_, v_resourceBusy_791_);
    return v___x_792_;
}
pub unsafe fn l_IO_Error_resourceVanished_elim___redArg(
    mut v_t_793_: *mut LeanObject,
    mut v_resourceVanished_794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_795_: *mut LeanObject = core::ptr::null_mut();
    v___x_795_ = l_IO_Error_ctorElim___redArg(v_t_793_, v_resourceVanished_794_);
    return v___x_795_;
}
pub unsafe fn l_IO_Error_resourceVanished_elim(
    mut v_motive_796_: *mut LeanObject,
    mut v_t_797_: *mut LeanObject,
    mut v_h_798_: *mut LeanObject,
    mut v_resourceVanished_799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    v___x_800_ = l_IO_Error_ctorElim___redArg(v_t_797_, v_resourceVanished_799_);
    return v___x_800_;
}
pub unsafe fn l_IO_Error_unsupportedOperation_elim___redArg(
    mut v_t_801_: *mut LeanObject,
    mut v_unsupportedOperation_802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    v___x_803_ = l_IO_Error_ctorElim___redArg(v_t_801_, v_unsupportedOperation_802_);
    return v___x_803_;
}
pub unsafe fn l_IO_Error_unsupportedOperation_elim(
    mut v_motive_804_: *mut LeanObject,
    mut v_t_805_: *mut LeanObject,
    mut v_h_806_: *mut LeanObject,
    mut v_unsupportedOperation_807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    v___x_808_ = l_IO_Error_ctorElim___redArg(v_t_805_, v_unsupportedOperation_807_);
    return v___x_808_;
}
pub unsafe fn l_IO_Error_hardwareFault_elim___redArg(
    mut v_t_809_: *mut LeanObject,
    mut v_hardwareFault_810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    v___x_811_ = l_IO_Error_ctorElim___redArg(v_t_809_, v_hardwareFault_810_);
    return v___x_811_;
}
pub unsafe fn l_IO_Error_hardwareFault_elim(
    mut v_motive_812_: *mut LeanObject,
    mut v_t_813_: *mut LeanObject,
    mut v_h_814_: *mut LeanObject,
    mut v_hardwareFault_815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    v___x_816_ = l_IO_Error_ctorElim___redArg(v_t_813_, v_hardwareFault_815_);
    return v___x_816_;
}
pub unsafe fn l_IO_Error_unsatisfiedConstraints_elim___redArg(
    mut v_t_817_: *mut LeanObject,
    mut v_unsatisfiedConstraints_818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    v___x_819_ = l_IO_Error_ctorElim___redArg(v_t_817_, v_unsatisfiedConstraints_818_);
    return v___x_819_;
}
pub unsafe fn l_IO_Error_unsatisfiedConstraints_elim(
    mut v_motive_820_: *mut LeanObject,
    mut v_t_821_: *mut LeanObject,
    mut v_h_822_: *mut LeanObject,
    mut v_unsatisfiedConstraints_823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    v___x_824_ = l_IO_Error_ctorElim___redArg(v_t_821_, v_unsatisfiedConstraints_823_);
    return v___x_824_;
}
pub unsafe fn l_IO_Error_illegalOperation_elim___redArg(
    mut v_t_825_: *mut LeanObject,
    mut v_illegalOperation_826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    v___x_827_ = l_IO_Error_ctorElim___redArg(v_t_825_, v_illegalOperation_826_);
    return v___x_827_;
}
pub unsafe fn l_IO_Error_illegalOperation_elim(
    mut v_motive_828_: *mut LeanObject,
    mut v_t_829_: *mut LeanObject,
    mut v_h_830_: *mut LeanObject,
    mut v_illegalOperation_831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    v___x_832_ = l_IO_Error_ctorElim___redArg(v_t_829_, v_illegalOperation_831_);
    return v___x_832_;
}
pub unsafe fn l_IO_Error_protocolError_elim___redArg(
    mut v_t_833_: *mut LeanObject,
    mut v_protocolError_834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    v___x_835_ = l_IO_Error_ctorElim___redArg(v_t_833_, v_protocolError_834_);
    return v___x_835_;
}
pub unsafe fn l_IO_Error_protocolError_elim(
    mut v_motive_836_: *mut LeanObject,
    mut v_t_837_: *mut LeanObject,
    mut v_h_838_: *mut LeanObject,
    mut v_protocolError_839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    v___x_840_ = l_IO_Error_ctorElim___redArg(v_t_837_, v_protocolError_839_);
    return v___x_840_;
}
pub unsafe fn l_IO_Error_timeExpired_elim___redArg(
    mut v_t_841_: *mut LeanObject,
    mut v_timeExpired_842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    v___x_843_ = l_IO_Error_ctorElim___redArg(v_t_841_, v_timeExpired_842_);
    return v___x_843_;
}
pub unsafe fn l_IO_Error_timeExpired_elim(
    mut v_motive_844_: *mut LeanObject,
    mut v_t_845_: *mut LeanObject,
    mut v_h_846_: *mut LeanObject,
    mut v_timeExpired_847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    v___x_848_ = l_IO_Error_ctorElim___redArg(v_t_845_, v_timeExpired_847_);
    return v___x_848_;
}
pub unsafe fn l_IO_Error_interrupted_elim___redArg(
    mut v_t_849_: *mut LeanObject,
    mut v_interrupted_850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    v___x_851_ = l_IO_Error_ctorElim___redArg(v_t_849_, v_interrupted_850_);
    return v___x_851_;
}
pub unsafe fn l_IO_Error_interrupted_elim(
    mut v_motive_852_: *mut LeanObject,
    mut v_t_853_: *mut LeanObject,
    mut v_h_854_: *mut LeanObject,
    mut v_interrupted_855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    v___x_856_ = l_IO_Error_ctorElim___redArg(v_t_853_, v_interrupted_855_);
    return v___x_856_;
}
pub unsafe fn l_IO_Error_noFileOrDirectory_elim___redArg(
    mut v_t_857_: *mut LeanObject,
    mut v_noFileOrDirectory_858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    v___x_859_ = l_IO_Error_ctorElim___redArg(v_t_857_, v_noFileOrDirectory_858_);
    return v___x_859_;
}
pub unsafe fn l_IO_Error_noFileOrDirectory_elim(
    mut v_motive_860_: *mut LeanObject,
    mut v_t_861_: *mut LeanObject,
    mut v_h_862_: *mut LeanObject,
    mut v_noFileOrDirectory_863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    v___x_864_ = l_IO_Error_ctorElim___redArg(v_t_861_, v_noFileOrDirectory_863_);
    return v___x_864_;
}
pub unsafe fn l_IO_Error_invalidArgument_elim___redArg(
    mut v_t_865_: *mut LeanObject,
    mut v_invalidArgument_866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    v___x_867_ = l_IO_Error_ctorElim___redArg(v_t_865_, v_invalidArgument_866_);
    return v___x_867_;
}
pub unsafe fn l_IO_Error_invalidArgument_elim(
    mut v_motive_868_: *mut LeanObject,
    mut v_t_869_: *mut LeanObject,
    mut v_h_870_: *mut LeanObject,
    mut v_invalidArgument_871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    v___x_872_ = l_IO_Error_ctorElim___redArg(v_t_869_, v_invalidArgument_871_);
    return v___x_872_;
}
pub unsafe fn l_IO_Error_permissionDenied_elim___redArg(
    mut v_t_873_: *mut LeanObject,
    mut v_permissionDenied_874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    v___x_875_ = l_IO_Error_ctorElim___redArg(v_t_873_, v_permissionDenied_874_);
    return v___x_875_;
}
pub unsafe fn l_IO_Error_permissionDenied_elim(
    mut v_motive_876_: *mut LeanObject,
    mut v_t_877_: *mut LeanObject,
    mut v_h_878_: *mut LeanObject,
    mut v_permissionDenied_879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    v___x_880_ = l_IO_Error_ctorElim___redArg(v_t_877_, v_permissionDenied_879_);
    return v___x_880_;
}
pub unsafe fn l_IO_Error_resourceExhausted_elim___redArg(
    mut v_t_881_: *mut LeanObject,
    mut v_resourceExhausted_882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    v___x_883_ = l_IO_Error_ctorElim___redArg(v_t_881_, v_resourceExhausted_882_);
    return v___x_883_;
}
pub unsafe fn l_IO_Error_resourceExhausted_elim(
    mut v_motive_884_: *mut LeanObject,
    mut v_t_885_: *mut LeanObject,
    mut v_h_886_: *mut LeanObject,
    mut v_resourceExhausted_887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    v___x_888_ = l_IO_Error_ctorElim___redArg(v_t_885_, v_resourceExhausted_887_);
    return v___x_888_;
}
pub unsafe fn l_IO_Error_inappropriateType_elim___redArg(
    mut v_t_889_: *mut LeanObject,
    mut v_inappropriateType_890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    v___x_891_ = l_IO_Error_ctorElim___redArg(v_t_889_, v_inappropriateType_890_);
    return v___x_891_;
}
pub unsafe fn l_IO_Error_inappropriateType_elim(
    mut v_motive_892_: *mut LeanObject,
    mut v_t_893_: *mut LeanObject,
    mut v_h_894_: *mut LeanObject,
    mut v_inappropriateType_895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    v___x_896_ = l_IO_Error_ctorElim___redArg(v_t_893_, v_inappropriateType_895_);
    return v___x_896_;
}
pub unsafe fn l_IO_Error_noSuchThing_elim___redArg(
    mut v_t_897_: *mut LeanObject,
    mut v_noSuchThing_898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    v___x_899_ = l_IO_Error_ctorElim___redArg(v_t_897_, v_noSuchThing_898_);
    return v___x_899_;
}
pub unsafe fn l_IO_Error_noSuchThing_elim(
    mut v_motive_900_: *mut LeanObject,
    mut v_t_901_: *mut LeanObject,
    mut v_h_902_: *mut LeanObject,
    mut v_noSuchThing_903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    v___x_904_ = l_IO_Error_ctorElim___redArg(v_t_901_, v_noSuchThing_903_);
    return v___x_904_;
}
pub unsafe fn l_IO_Error_unexpectedEof_elim___redArg(
    mut v_t_905_: *mut LeanObject,
    mut v_unexpectedEof_906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    v___x_907_ = l_IO_Error_ctorElim___redArg(v_t_905_, v_unexpectedEof_906_);
    return v___x_907_;
}
pub unsafe fn l_IO_Error_unexpectedEof_elim(
    mut v_motive_908_: *mut LeanObject,
    mut v_t_909_: *mut LeanObject,
    mut v_h_910_: *mut LeanObject,
    mut v_unexpectedEof_911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    v___x_912_ = l_IO_Error_ctorElim___redArg(v_t_909_, v_unexpectedEof_911_);
    return v___x_912_;
}
pub unsafe fn l_IO_Error_userError_elim___redArg(
    mut v_t_913_: *mut LeanObject,
    mut v_userError_914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    v___x_915_ = l_IO_Error_ctorElim___redArg(v_t_913_, v_userError_914_);
    return v___x_915_;
}
pub unsafe fn l_IO_Error_userError_elim(
    mut v_motive_916_: *mut LeanObject,
    mut v_t_917_: *mut LeanObject,
    mut v_h_918_: *mut LeanObject,
    mut v_userError_919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    v___x_920_ = l_IO_Error_ctorElim___redArg(v_t_917_, v_userError_919_);
    return v___x_920_;
}
pub unsafe fn lean_mk_io_user_error(mut v_s_925_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    v___x_926_ = lean_alloc_ctor(18, 1, (0) as u32);
    lean_ctor_set(v___x_926_, 0, v_s_925_);
    return v___x_926_;
}
pub unsafe fn lean_mk_io_error_already_exists_file(
    mut v_a_929_: *mut LeanObject,
    mut v_a_930_: u32,
    mut v_a_931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    v___x_932_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_932_, 0, v_a_929_);
    v___x_933_ = lean_alloc_ctor(0, 2, (4) as u32);
    lean_ctor_set(v___x_933_, 0, v___x_932_);
    lean_ctor_set(v___x_933_, 1, v_a_931_);
    lean_ctor_set_uint32(
        v___x_933_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v_a_930_,
    );
    return v___x_933_;
}
pub unsafe fn l_IO_Error_mkAlreadyExistsFile___boxed(
    mut v_a_934_: *mut LeanObject,
    mut v_a_935_: *mut LeanObject,
    mut v_a_936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_20__boxed_937_: u32 = 0;
    let mut v_res_938_: *mut LeanObject = core::ptr::null_mut();
    v_a_20__boxed_937_ = lean_unbox_uint32(v_a_935_);
    lean_dec(v_a_935_);
    v_res_938_ = lean_mk_io_error_already_exists_file(v_a_934_, v_a_20__boxed_937_, v_a_936_);
    return v_res_938_;
}
pub unsafe fn lean_mk_io_error_eof(mut v_x_939_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    v___x_940_ = lean_box(17);
    return v___x_940_;
}
pub unsafe fn lean_mk_io_error_inappropriate_type_file(
    mut v_a_941_: *mut LeanObject,
    mut v_a_942_: u32,
    mut v_a_943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    v___x_944_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_944_, 0, v_a_941_);
    v___x_945_ = lean_alloc_ctor(15, 2, (4) as u32);
    lean_ctor_set(v___x_945_, 0, v___x_944_);
    lean_ctor_set(v___x_945_, 1, v_a_943_);
    lean_ctor_set_uint32(
        v___x_945_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v_a_942_,
    );
    return v___x_945_;
}
pub unsafe fn l_IO_Error_mkInappropriateTypeFile___boxed(
    mut v_a_946_: *mut LeanObject,
    mut v_a_947_: *mut LeanObject,
    mut v_a_948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_20__boxed_949_: u32 = 0;
    let mut v_res_950_: *mut LeanObject = core::ptr::null_mut();
    v_a_20__boxed_949_ = lean_unbox_uint32(v_a_947_);
    lean_dec(v_a_947_);
    v_res_950_ = lean_mk_io_error_inappropriate_type_file(v_a_946_, v_a_20__boxed_949_, v_a_948_);
    return v_res_950_;
}
pub unsafe fn lean_mk_io_error_interrupted(
    mut v_filename_951_: *mut LeanObject,
    mut v_osCode_952_: u32,
    mut v_details_953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    v___x_954_ = lean_alloc_ctor(10, 2, (4) as u32);
    lean_ctor_set(v___x_954_, 0, v_filename_951_);
    lean_ctor_set(v___x_954_, 1, v_details_953_);
    lean_ctor_set_uint32(
        v___x_954_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v_osCode_952_,
    );
    return v___x_954_;
}
pub unsafe fn l_IO_Error_mkInterrupted___boxed(
    mut v_filename_955_: *mut LeanObject,
    mut v_osCode_956_: *mut LeanObject,
    mut v_details_957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_osCode_boxed_958_: u32 = 0;
    let mut v_res_959_: *mut LeanObject = core::ptr::null_mut();
    v_osCode_boxed_958_ = lean_unbox_uint32(v_osCode_956_);
    lean_dec(v_osCode_956_);
    v_res_959_ = lean_mk_io_error_interrupted(v_filename_955_, v_osCode_boxed_958_, v_details_957_);
    return v_res_959_;
}
pub unsafe fn lean_mk_io_error_invalid_argument_file(
    mut v_a_960_: *mut LeanObject,
    mut v_a_961_: u32,
    mut v_a_962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    v___x_963_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_963_, 0, v_a_960_);
    v___x_964_ = lean_alloc_ctor(12, 2, (4) as u32);
    lean_ctor_set(v___x_964_, 0, v___x_963_);
    lean_ctor_set(v___x_964_, 1, v_a_962_);
    lean_ctor_set_uint32(
        v___x_964_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v_a_961_,
    );
    return v___x_964_;
}
pub unsafe fn l_IO_Error_mkInvalidArgumentFile___boxed(
    mut v_a_965_: *mut LeanObject,
    mut v_a_966_: *mut LeanObject,
    mut v_a_967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_20__boxed_968_: u32 = 0;
    let mut v_res_969_: *mut LeanObject = core::ptr::null_mut();
    v_a_20__boxed_968_ = lean_unbox_uint32(v_a_966_);
    lean_dec(v_a_966_);
    v_res_969_ = lean_mk_io_error_invalid_argument_file(v_a_965_, v_a_20__boxed_968_, v_a_967_);
    return v_res_969_;
}
pub unsafe fn lean_mk_io_error_no_file_or_directory(
    mut v_filename_970_: *mut LeanObject,
    mut v_osCode_971_: u32,
    mut v_details_972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    v___x_973_ = lean_alloc_ctor(11, 2, (4) as u32);
    lean_ctor_set(v___x_973_, 0, v_filename_970_);
    lean_ctor_set(v___x_973_, 1, v_details_972_);
    lean_ctor_set_uint32(
        v___x_973_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v_osCode_971_,
    );
    return v___x_973_;
}
pub unsafe fn l_IO_Error_mkNoFileOrDirectory___boxed(
    mut v_filename_974_: *mut LeanObject,
    mut v_osCode_975_: *mut LeanObject,
    mut v_details_976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_osCode_boxed_977_: u32 = 0;
    let mut v_res_978_: *mut LeanObject = core::ptr::null_mut();
    v_osCode_boxed_977_ = lean_unbox_uint32(v_osCode_975_);
    lean_dec(v_osCode_975_);
    v_res_978_ =
        lean_mk_io_error_no_file_or_directory(v_filename_974_, v_osCode_boxed_977_, v_details_976_);
    return v_res_978_;
}
pub unsafe fn lean_mk_io_error_no_such_thing_file(
    mut v_a_979_: *mut LeanObject,
    mut v_a_980_: u32,
    mut v_a_981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    v___x_982_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_982_, 0, v_a_979_);
    v___x_983_ = lean_alloc_ctor(16, 2, (4) as u32);
    lean_ctor_set(v___x_983_, 0, v___x_982_);
    lean_ctor_set(v___x_983_, 1, v_a_981_);
    lean_ctor_set_uint32(
        v___x_983_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v_a_980_,
    );
    return v___x_983_;
}
pub unsafe fn l_IO_Error_mkNoSuchThingFile___boxed(
    mut v_a_984_: *mut LeanObject,
    mut v_a_985_: *mut LeanObject,
    mut v_a_986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_20__boxed_987_: u32 = 0;
    let mut v_res_988_: *mut LeanObject = core::ptr::null_mut();
    v_a_20__boxed_987_ = lean_unbox_uint32(v_a_985_);
    lean_dec(v_a_985_);
    v_res_988_ = lean_mk_io_error_no_such_thing_file(v_a_984_, v_a_20__boxed_987_, v_a_986_);
    return v_res_988_;
}
pub unsafe fn lean_mk_io_error_permission_denied_file(
    mut v_a_989_: *mut LeanObject,
    mut v_a_990_: u32,
    mut v_a_991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    v___x_992_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_992_, 0, v_a_989_);
    v___x_993_ = lean_alloc_ctor(13, 2, (4) as u32);
    lean_ctor_set(v___x_993_, 0, v___x_992_);
    lean_ctor_set(v___x_993_, 1, v_a_991_);
    lean_ctor_set_uint32(
        v___x_993_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v_a_990_,
    );
    return v___x_993_;
}
pub unsafe fn l_IO_Error_mkPermissionDeniedFile___boxed(
    mut v_a_994_: *mut LeanObject,
    mut v_a_995_: *mut LeanObject,
    mut v_a_996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_20__boxed_997_: u32 = 0;
    let mut v_res_998_: *mut LeanObject = core::ptr::null_mut();
    v_a_20__boxed_997_ = lean_unbox_uint32(v_a_995_);
    lean_dec(v_a_995_);
    v_res_998_ = lean_mk_io_error_permission_denied_file(v_a_994_, v_a_20__boxed_997_, v_a_996_);
    return v_res_998_;
}
pub unsafe fn lean_mk_io_error_resource_exhausted_file(
    mut v_a_999_: *mut LeanObject,
    mut v_a_1000_: u32,
    mut v_a_1001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    v___x_1002_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1002_, 0, v_a_999_);
    v___x_1003_ = lean_alloc_ctor(14, 2, (4) as u32);
    lean_ctor_set(v___x_1003_, 0, v___x_1002_);
    lean_ctor_set(v___x_1003_, 1, v_a_1001_);
    lean_ctor_set_uint32(
        v___x_1003_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v_a_1000_,
    );
    return v___x_1003_;
}
pub unsafe fn l_IO_Error_mkResourceExhaustedFile___boxed(
    mut v_a_1004_: *mut LeanObject,
    mut v_a_1005_: *mut LeanObject,
    mut v_a_1006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_20__boxed_1007_: u32 = 0;
    let mut v_res_1008_: *mut LeanObject = core::ptr::null_mut();
    v_a_20__boxed_1007_ = lean_unbox_uint32(v_a_1005_);
    lean_dec(v_a_1005_);
    v_res_1008_ =
        lean_mk_io_error_resource_exhausted_file(v_a_1004_, v_a_20__boxed_1007_, v_a_1006_);
    return v_res_1008_;
}
pub unsafe fn lean_mk_io_error_unsupported_operation(
    mut v_osCode_1009_: u32,
    mut v_details_1010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    v___x_1011_ = lean_alloc_ctor(4, 1, (4) as u32);
    lean_ctor_set(v___x_1011_, 0, v_details_1010_);
    lean_ctor_set_uint32(
        v___x_1011_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v_osCode_1009_,
    );
    return v___x_1011_;
}
pub unsafe fn l_IO_Error_mkUnsupportedOperation___boxed(
    mut v_osCode_1012_: *mut LeanObject,
    mut v_details_1013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_osCode_boxed_1014_: u32 = 0;
    let mut v_res_1015_: *mut LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1014_ = lean_unbox_uint32(v_osCode_1012_);
    lean_dec(v_osCode_1012_);
    v_res_1015_ = lean_mk_io_error_unsupported_operation(v_osCode_boxed_1014_, v_details_1013_);
    return v_res_1015_;
}
pub unsafe fn lean_mk_io_error_resource_exhausted(
    mut v_osCode_1016_: u32,
    mut v_details_1017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    v___x_1018_ = lean_box(0);
    v___x_1019_ = lean_alloc_ctor(14, 2, (4) as u32);
    lean_ctor_set(v___x_1019_, 0, v___x_1018_);
    lean_ctor_set(v___x_1019_, 1, v_details_1017_);
    lean_ctor_set_uint32(
        v___x_1019_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v_osCode_1016_,
    );
    return v___x_1019_;
}
pub unsafe fn l_IO_Error_mkResourceExhausted___boxed(
    mut v_osCode_1020_: *mut LeanObject,
    mut v_details_1021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_osCode_boxed_1022_: u32 = 0;
    let mut v_res_1023_: *mut LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1022_ = lean_unbox_uint32(v_osCode_1020_);
    lean_dec(v_osCode_1020_);
    v_res_1023_ = lean_mk_io_error_resource_exhausted(v_osCode_boxed_1022_, v_details_1021_);
    return v_res_1023_;
}
pub unsafe fn lean_mk_io_error_already_exists(
    mut v_osCode_1024_: u32,
    mut v_details_1025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    v___x_1026_ = lean_box(0);
    v___x_1027_ = lean_alloc_ctor(0, 2, (4) as u32);
    lean_ctor_set(v___x_1027_, 0, v___x_1026_);
    lean_ctor_set(v___x_1027_, 1, v_details_1025_);
    lean_ctor_set_uint32(
        v___x_1027_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v_osCode_1024_,
    );
    return v___x_1027_;
}
pub unsafe fn l_IO_Error_mkAlreadyExists___boxed(
    mut v_osCode_1028_: *mut LeanObject,
    mut v_details_1029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_osCode_boxed_1030_: u32 = 0;
    let mut v_res_1031_: *mut LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1030_ = lean_unbox_uint32(v_osCode_1028_);
    lean_dec(v_osCode_1028_);
    v_res_1031_ = lean_mk_io_error_already_exists(v_osCode_boxed_1030_, v_details_1029_);
    return v_res_1031_;
}
pub unsafe fn lean_mk_io_error_inappropriate_type(
    mut v_osCode_1032_: u32,
    mut v_details_1033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    v___x_1034_ = lean_box(0);
    v___x_1035_ = lean_alloc_ctor(15, 2, (4) as u32);
    lean_ctor_set(v___x_1035_, 0, v___x_1034_);
    lean_ctor_set(v___x_1035_, 1, v_details_1033_);
    lean_ctor_set_uint32(
        v___x_1035_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v_osCode_1032_,
    );
    return v___x_1035_;
}
pub unsafe fn l_IO_Error_mkInappropriateType___boxed(
    mut v_osCode_1036_: *mut LeanObject,
    mut v_details_1037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_osCode_boxed_1038_: u32 = 0;
    let mut v_res_1039_: *mut LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1038_ = lean_unbox_uint32(v_osCode_1036_);
    lean_dec(v_osCode_1036_);
    v_res_1039_ = lean_mk_io_error_inappropriate_type(v_osCode_boxed_1038_, v_details_1037_);
    return v_res_1039_;
}
pub unsafe fn lean_mk_io_error_no_such_thing(
    mut v_osCode_1040_: u32,
    mut v_details_1041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    v___x_1042_ = lean_box(0);
    v___x_1043_ = lean_alloc_ctor(16, 2, (4) as u32);
    lean_ctor_set(v___x_1043_, 0, v___x_1042_);
    lean_ctor_set(v___x_1043_, 1, v_details_1041_);
    lean_ctor_set_uint32(
        v___x_1043_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v_osCode_1040_,
    );
    return v___x_1043_;
}
pub unsafe fn l_IO_Error_mkNoSuchThing___boxed(
    mut v_osCode_1044_: *mut LeanObject,
    mut v_details_1045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_osCode_boxed_1046_: u32 = 0;
    let mut v_res_1047_: *mut LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1046_ = lean_unbox_uint32(v_osCode_1044_);
    lean_dec(v_osCode_1044_);
    v_res_1047_ = lean_mk_io_error_no_such_thing(v_osCode_boxed_1046_, v_details_1045_);
    return v_res_1047_;
}
pub unsafe fn lean_mk_io_error_resource_vanished(
    mut v_osCode_1048_: u32,
    mut v_details_1049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    v___x_1050_ = lean_alloc_ctor(3, 1, (4) as u32);
    lean_ctor_set(v___x_1050_, 0, v_details_1049_);
    lean_ctor_set_uint32(
        v___x_1050_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v_osCode_1048_,
    );
    return v___x_1050_;
}
pub unsafe fn l_IO_Error_mkResourceVanished___boxed(
    mut v_osCode_1051_: *mut LeanObject,
    mut v_details_1052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_osCode_boxed_1053_: u32 = 0;
    let mut v_res_1054_: *mut LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1053_ = lean_unbox_uint32(v_osCode_1051_);
    lean_dec(v_osCode_1051_);
    v_res_1054_ = lean_mk_io_error_resource_vanished(v_osCode_boxed_1053_, v_details_1052_);
    return v_res_1054_;
}
pub unsafe fn lean_mk_io_error_resource_busy(
    mut v_osCode_1055_: u32,
    mut v_details_1056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    v___x_1057_ = lean_alloc_ctor(2, 1, (4) as u32);
    lean_ctor_set(v___x_1057_, 0, v_details_1056_);
    lean_ctor_set_uint32(
        v___x_1057_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v_osCode_1055_,
    );
    return v___x_1057_;
}
pub unsafe fn l_IO_Error_mkResourceBusy___boxed(
    mut v_osCode_1058_: *mut LeanObject,
    mut v_details_1059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_osCode_boxed_1060_: u32 = 0;
    let mut v_res_1061_: *mut LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1060_ = lean_unbox_uint32(v_osCode_1058_);
    lean_dec(v_osCode_1058_);
    v_res_1061_ = lean_mk_io_error_resource_busy(v_osCode_boxed_1060_, v_details_1059_);
    return v_res_1061_;
}
pub unsafe fn lean_mk_io_error_invalid_argument(
    mut v_osCode_1062_: u32,
    mut v_details_1063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    v___x_1064_ = lean_box(0);
    v___x_1065_ = lean_alloc_ctor(12, 2, (4) as u32);
    lean_ctor_set(v___x_1065_, 0, v___x_1064_);
    lean_ctor_set(v___x_1065_, 1, v_details_1063_);
    lean_ctor_set_uint32(
        v___x_1065_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v_osCode_1062_,
    );
    return v___x_1065_;
}
pub unsafe fn l_IO_Error_mkInvalidArgument___boxed(
    mut v_osCode_1066_: *mut LeanObject,
    mut v_details_1067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_osCode_boxed_1068_: u32 = 0;
    let mut v_res_1069_: *mut LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1068_ = lean_unbox_uint32(v_osCode_1066_);
    lean_dec(v_osCode_1066_);
    v_res_1069_ = lean_mk_io_error_invalid_argument(v_osCode_boxed_1068_, v_details_1067_);
    return v_res_1069_;
}
pub unsafe fn lean_mk_io_error_other_error(
    mut v_osCode_1070_: u32,
    mut v_details_1071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    v___x_1072_ = lean_alloc_ctor(1, 1, (4) as u32);
    lean_ctor_set(v___x_1072_, 0, v_details_1071_);
    lean_ctor_set_uint32(
        v___x_1072_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v_osCode_1070_,
    );
    return v___x_1072_;
}
pub unsafe fn l_IO_Error_mkOtherError___boxed(
    mut v_osCode_1073_: *mut LeanObject,
    mut v_details_1074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_osCode_boxed_1075_: u32 = 0;
    let mut v_res_1076_: *mut LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1075_ = lean_unbox_uint32(v_osCode_1073_);
    lean_dec(v_osCode_1073_);
    v_res_1076_ = lean_mk_io_error_other_error(v_osCode_boxed_1075_, v_details_1074_);
    return v_res_1076_;
}
pub unsafe fn lean_mk_io_error_permission_denied(
    mut v_osCode_1077_: u32,
    mut v_details_1078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    v___x_1079_ = lean_box(0);
    v___x_1080_ = lean_alloc_ctor(13, 2, (4) as u32);
    lean_ctor_set(v___x_1080_, 0, v___x_1079_);
    lean_ctor_set(v___x_1080_, 1, v_details_1078_);
    lean_ctor_set_uint32(
        v___x_1080_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v_osCode_1077_,
    );
    return v___x_1080_;
}
pub unsafe fn l_IO_Error_mkPermissionDenied___boxed(
    mut v_osCode_1081_: *mut LeanObject,
    mut v_details_1082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_osCode_boxed_1083_: u32 = 0;
    let mut v_res_1084_: *mut LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1083_ = lean_unbox_uint32(v_osCode_1081_);
    lean_dec(v_osCode_1081_);
    v_res_1084_ = lean_mk_io_error_permission_denied(v_osCode_boxed_1083_, v_details_1082_);
    return v_res_1084_;
}
pub unsafe fn lean_mk_io_error_hardware_fault(
    mut v_osCode_1085_: u32,
    mut v_details_1086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    v___x_1087_ = lean_alloc_ctor(5, 1, (4) as u32);
    lean_ctor_set(v___x_1087_, 0, v_details_1086_);
    lean_ctor_set_uint32(
        v___x_1087_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v_osCode_1085_,
    );
    return v___x_1087_;
}
pub unsafe fn l_IO_Error_mkHardwareFault___boxed(
    mut v_osCode_1088_: *mut LeanObject,
    mut v_details_1089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_osCode_boxed_1090_: u32 = 0;
    let mut v_res_1091_: *mut LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1090_ = lean_unbox_uint32(v_osCode_1088_);
    lean_dec(v_osCode_1088_);
    v_res_1091_ = lean_mk_io_error_hardware_fault(v_osCode_boxed_1090_, v_details_1089_);
    return v_res_1091_;
}
pub unsafe fn lean_mk_io_error_unsatisfied_constraints(
    mut v_osCode_1092_: u32,
    mut v_details_1093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    v___x_1094_ = lean_alloc_ctor(6, 1, (4) as u32);
    lean_ctor_set(v___x_1094_, 0, v_details_1093_);
    lean_ctor_set_uint32(
        v___x_1094_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v_osCode_1092_,
    );
    return v___x_1094_;
}
pub unsafe fn l_IO_Error_mkUnsatisfiedConstraints___boxed(
    mut v_osCode_1095_: *mut LeanObject,
    mut v_details_1096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_osCode_boxed_1097_: u32 = 0;
    let mut v_res_1098_: *mut LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1097_ = lean_unbox_uint32(v_osCode_1095_);
    lean_dec(v_osCode_1095_);
    v_res_1098_ = lean_mk_io_error_unsatisfied_constraints(v_osCode_boxed_1097_, v_details_1096_);
    return v_res_1098_;
}
pub unsafe fn lean_mk_io_error_illegal_operation(
    mut v_osCode_1099_: u32,
    mut v_details_1100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    v___x_1101_ = lean_alloc_ctor(7, 1, (4) as u32);
    lean_ctor_set(v___x_1101_, 0, v_details_1100_);
    lean_ctor_set_uint32(
        v___x_1101_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v_osCode_1099_,
    );
    return v___x_1101_;
}
pub unsafe fn l_IO_Error_mkIllegalOperation___boxed(
    mut v_osCode_1102_: *mut LeanObject,
    mut v_details_1103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_osCode_boxed_1104_: u32 = 0;
    let mut v_res_1105_: *mut LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1104_ = lean_unbox_uint32(v_osCode_1102_);
    lean_dec(v_osCode_1102_);
    v_res_1105_ = lean_mk_io_error_illegal_operation(v_osCode_boxed_1104_, v_details_1103_);
    return v_res_1105_;
}
pub unsafe fn lean_mk_io_error_protocol_error(
    mut v_osCode_1106_: u32,
    mut v_details_1107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    v___x_1108_ = lean_alloc_ctor(8, 1, (4) as u32);
    lean_ctor_set(v___x_1108_, 0, v_details_1107_);
    lean_ctor_set_uint32(
        v___x_1108_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v_osCode_1106_,
    );
    return v___x_1108_;
}
pub unsafe fn l_IO_Error_mkProtocolError___boxed(
    mut v_osCode_1109_: *mut LeanObject,
    mut v_details_1110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_osCode_boxed_1111_: u32 = 0;
    let mut v_res_1112_: *mut LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1111_ = lean_unbox_uint32(v_osCode_1109_);
    lean_dec(v_osCode_1109_);
    v_res_1112_ = lean_mk_io_error_protocol_error(v_osCode_boxed_1111_, v_details_1110_);
    return v_res_1112_;
}
pub unsafe fn lean_mk_io_error_time_expired(
    mut v_osCode_1113_: u32,
    mut v_details_1114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    v___x_1115_ = lean_alloc_ctor(9, 1, (4) as u32);
    lean_ctor_set(v___x_1115_, 0, v_details_1114_);
    lean_ctor_set_uint32(
        v___x_1115_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v_osCode_1113_,
    );
    return v___x_1115_;
}
pub unsafe fn l_IO_Error_mkTimeExpired___boxed(
    mut v_osCode_1116_: *mut LeanObject,
    mut v_details_1117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_osCode_boxed_1118_: u32 = 0;
    let mut v_res_1119_: *mut LeanObject = core::ptr::null_mut();
    v_osCode_boxed_1118_ = lean_unbox_uint32(v_osCode_1116_);
    lean_dec(v_osCode_1116_);
    v_res_1119_ = lean_mk_io_error_time_expired(v_osCode_boxed_1118_, v_details_1117_);
    return v_res_1119_;
}
pub unsafe fn l___private_Init_System_IOError_0__IO_Error_downCaseFirst(
    mut v_s_1120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: u32 = 0;
    let mut v___x_1123_: u32 = 0;
    let mut v___x_1124_: u8 = 0;
    v___x_1121_ = lean_unsigned_to_nat(0);
    v___x_1122_ = lean_string_utf8_get(v_s_1120_, v___x_1121_);
    v___x_1123_ = 65;
    v___x_1124_ = lean_uint32_dec_le(v___x_1123_, v___x_1122_);
    if v___x_1124_ == 0 {
        let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
        v___x_1125_ = lean_string_utf8_set(v_s_1120_, v___x_1121_, v___x_1122_);
        return v___x_1125_;
    } else {
        let mut v___x_1126_: u32 = 0;
        let mut v___x_1127_: u8 = 0;
        v___x_1126_ = 90;
        v___x_1127_ = lean_uint32_dec_le(v___x_1122_, v___x_1126_);
        if v___x_1127_ == 0 {
            let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
            v___x_1128_ = lean_string_utf8_set(v_s_1120_, v___x_1121_, v___x_1122_);
            return v___x_1128_;
        } else {
            let mut v___x_1129_: u32 = 0;
            let mut v___x_1130_: u32 = 0;
            let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
            v___x_1129_ = 32;
            v___x_1130_ = lean_uint32_add(v___x_1122_, v___x_1129_);
            v___x_1131_ = lean_string_utf8_set(v_s_1120_, v___x_1121_, v___x_1130_);
            return v___x_1131_;
        }
    }
}
pub unsafe fn l_IO_Error_fopenErrorToString(
    mut v_gist_1135_: *mut LeanObject,
    mut v_fn_1136_: *mut LeanObject,
    mut v_code_1137_: u32,
    mut v_x_1138_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1138_) == 0 {
        let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
        v___x_1139_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_gist_1135_);
        v___x_1140_ = l_IO_Error_fopenErrorToString___closed__0;
        v___x_1141_ = lean_string_append(v___x_1139_, v___x_1140_);
        v___x_1142_ = lean_uint32_to_nat(v_code_1137_);
        v___x_1143_ = l_Nat_reprFast(v___x_1142_);
        v___x_1144_ = lean_string_append(v___x_1141_, v___x_1143_);
        lean_dec_ref(v___x_1143_);
        v___x_1145_ = l_IO_Error_fopenErrorToString___closed__1;
        v___x_1146_ = lean_string_append(v___x_1144_, v___x_1145_);
        v___x_1147_ = lean_string_append(v___x_1146_, v_fn_1136_);
        return v___x_1147_;
    } else {
        let mut v_val_1148_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
        v_val_1148_ = lean_ctor_get(v_x_1138_, 0);
        lean_inc(v_val_1148_);
        lean_dec_ref_known(v_x_1138_, 1);
        v___x_1149_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_gist_1135_);
        v___x_1150_ = l_IO_Error_fopenErrorToString___closed__0;
        v___x_1151_ = lean_string_append(v___x_1149_, v___x_1150_);
        v___x_1152_ = lean_uint32_to_nat(v_code_1137_);
        v___x_1153_ = l_Nat_reprFast(v___x_1152_);
        v___x_1154_ = lean_string_append(v___x_1151_, v___x_1153_);
        lean_dec_ref(v___x_1153_);
        v___x_1155_ = l_IO_Error_fopenErrorToString___closed__2;
        v___x_1156_ = lean_string_append(v___x_1154_, v___x_1155_);
        v___x_1157_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_val_1148_);
        v___x_1158_ = lean_string_append(v___x_1156_, v___x_1157_);
        lean_dec_ref(v___x_1157_);
        v___x_1159_ = l_IO_Error_fopenErrorToString___closed__1;
        v___x_1160_ = lean_string_append(v___x_1158_, v___x_1159_);
        v___x_1161_ = lean_string_append(v___x_1160_, v_fn_1136_);
        return v___x_1161_;
    }
}
pub unsafe fn l_IO_Error_fopenErrorToString___boxed(
    mut v_gist_1162_: *mut LeanObject,
    mut v_fn_1163_: *mut LeanObject,
    mut v_code_1164_: *mut LeanObject,
    mut v_x_1165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_code_boxed_1166_: u32 = 0;
    let mut v_res_1167_: *mut LeanObject = core::ptr::null_mut();
    v_code_boxed_1166_ = lean_unbox_uint32(v_code_1164_);
    lean_dec(v_code_1164_);
    v_res_1167_ =
        l_IO_Error_fopenErrorToString(v_gist_1162_, v_fn_1163_, v_code_boxed_1166_, v_x_1165_);
    lean_dec_ref(v_fn_1163_);
    return v_res_1167_;
}
pub unsafe fn l_IO_Error_otherErrorToString(
    mut v_gist_1169_: *mut LeanObject,
    mut v_code_1170_: u32,
    mut v_x_1171_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1171_) == 0 {
        let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
        v___x_1172_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_gist_1169_);
        v___x_1173_ = l_IO_Error_fopenErrorToString___closed__0;
        v___x_1174_ = lean_string_append(v___x_1172_, v___x_1173_);
        v___x_1175_ = lean_uint32_to_nat(v_code_1170_);
        v___x_1176_ = l_Nat_reprFast(v___x_1175_);
        v___x_1177_ = lean_string_append(v___x_1174_, v___x_1176_);
        lean_dec_ref(v___x_1176_);
        v___x_1178_ = l_IO_Error_otherErrorToString___closed__0;
        v___x_1179_ = lean_string_append(v___x_1177_, v___x_1178_);
        return v___x_1179_;
    } else {
        let mut v_val_1180_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
        v_val_1180_ = lean_ctor_get(v_x_1171_, 0);
        lean_inc(v_val_1180_);
        lean_dec_ref_known(v_x_1171_, 1);
        v___x_1181_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_gist_1169_);
        v___x_1182_ = l_IO_Error_fopenErrorToString___closed__0;
        v___x_1183_ = lean_string_append(v___x_1181_, v___x_1182_);
        v___x_1184_ = lean_uint32_to_nat(v_code_1170_);
        v___x_1185_ = l_Nat_reprFast(v___x_1184_);
        v___x_1186_ = lean_string_append(v___x_1183_, v___x_1185_);
        lean_dec_ref(v___x_1185_);
        v___x_1187_ = l_IO_Error_fopenErrorToString___closed__2;
        v___x_1188_ = lean_string_append(v___x_1186_, v___x_1187_);
        v___x_1189_ = l___private_Init_System_IOError_0__IO_Error_downCaseFirst(v_val_1180_);
        v___x_1190_ = lean_string_append(v___x_1188_, v___x_1189_);
        lean_dec_ref(v___x_1189_);
        v___x_1191_ = l_IO_Error_otherErrorToString___closed__0;
        v___x_1192_ = lean_string_append(v___x_1190_, v___x_1191_);
        return v___x_1192_;
    }
}
pub unsafe fn l_IO_Error_otherErrorToString___boxed(
    mut v_gist_1193_: *mut LeanObject,
    mut v_code_1194_: *mut LeanObject,
    mut v_x_1195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_code_boxed_1196_: u32 = 0;
    let mut v_res_1197_: *mut LeanObject = core::ptr::null_mut();
    v_code_boxed_1196_ = lean_unbox_uint32(v_code_1194_);
    lean_dec(v_code_1194_);
    v_res_1197_ = l_IO_Error_otherErrorToString(v_gist_1193_, v_code_boxed_1196_, v_x_1195_);
    return v_res_1197_;
}
pub unsafe fn lean_io_error_to_string(mut v_x_1214_: *mut LeanObject) -> *mut LeanObject {
    let mut v_code_1216_: u32 = 0;
    let mut v_details_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_filename_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_osCode_1221_: u32 = 0;
    let mut v_details_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_osCode_1226_: u32 = 0;
    let mut v_details_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1231_: u8 = 0;
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1237_: u8 = 0;
    let mut v_osCode_1238_: u32 = 0;
    let mut v_details_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_osCode_1240_: u32 = 0;
    let mut v_details_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_osCode_1245_: u32 = 0;
    let mut v_details_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_osCode_1250_: u32 = 0;
    let mut v_details_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_osCode_1255_: u32 = 0;
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_osCode_1259_: u32 = 0;
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_osCode_1263_: u32 = 0;
    let mut v_details_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_osCode_1268_: u32 = 0;
    let mut v_details_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_osCode_1273_: u32 = 0;
    let mut v_details_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_filename_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_osCode_1279_: u32 = 0;
    let mut v_details_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_filename_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_osCode_1285_: u32 = 0;
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_filename_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_osCode_1290_: u32 = 0;
    let mut v_details_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_osCode_1295_: u32 = 0;
    let mut v_details_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1300_: u8 = 0;
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1306_: u8 = 0;
    let mut v_filename_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_osCode_1308_: u32 = 0;
    let mut v_details_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_osCode_1310_: u32 = 0;
    let mut v_details_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_filename_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_osCode_1316_: u32 = 0;
    let mut v_details_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_osCode_1321_: u32 = 0;
    let mut v_details_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1326_: u8 = 0;
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1332_: u8 = 0;
    let mut v_filename_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_osCode_1334_: u32 = 0;
    let mut v_details_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_osCode_1339_: u32 = 0;
    let mut v_details_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1344_: u8 = 0;
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1350_: u8 = 0;
    let mut v_filename_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_osCode_1352_: u32 = 0;
    let mut v_details_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_osCode_1357_: u32 = 0;
    let mut v_details_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1362_: u8 = 0;
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1368_: u8 = 0;
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_1214_) {
                0 => {
                    v_filename_1220_ = lean_ctor_get(v_x_1214_, 0);
                    lean_inc(v_filename_1220_);
                    if lean_obj_tag(v_filename_1220_) == 0 {
                        v_osCode_1221_ = lean_ctor_get_uint32(
                            v_x_1214_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v_details_1222_ = lean_ctor_get(v_x_1214_, 1);
                        lean_inc_ref(v_details_1222_);
                        lean_dec_ref_known(v_x_1214_, 2);
                        v___x_1223_ = l_IO_Error_toString___closed__0;
                        v___x_1224_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1224_, 0, v_details_1222_);
                        v___x_1225_ =
                            l_IO_Error_otherErrorToString(v___x_1223_, v_osCode_1221_, v___x_1224_);
                        return v___x_1225_;
                    } else {
                        v_osCode_1226_ = lean_ctor_get_uint32(
                            v_x_1214_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v_details_1227_ = lean_ctor_get(v_x_1214_, 1);
                        lean_inc_ref(v_details_1227_);
                        lean_dec_ref_known(v_x_1214_, 2);
                        v_val_1228_ = lean_ctor_get(v_filename_1220_, 0);
                        v_isSharedCheck_1237_ = (!lean_is_exclusive(v_filename_1220_)) as u8;
                        if v_isSharedCheck_1237_ == 0 {
                            v___x_1230_ = v_filename_1220_;
                            v_isShared_1231_ = v_isSharedCheck_1237_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_val_1228_);
                            lean_dec(v_filename_1220_);
                            v___x_1230_ = lean_box(0);
                            v_isShared_1231_ = v_isSharedCheck_1237_;
                            state = 2;
                            continue;
                        }
                    }
                }
                1 => {
                    v_osCode_1238_ = lean_ctor_get_uint32(
                        v_x_1214_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_details_1239_ = lean_ctor_get(v_x_1214_, 0);
                    lean_inc_ref(v_details_1239_);
                    lean_dec_ref_known(v_x_1214_, 1);
                    v_code_1216_ = v_osCode_1238_;
                    v_details_1217_ = v_details_1239_;
                    state = 1;
                    continue;
                }
                2 => {
                    v_osCode_1240_ = lean_ctor_get_uint32(
                        v_x_1214_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_details_1241_ = lean_ctor_get(v_x_1214_, 0);
                    lean_inc_ref(v_details_1241_);
                    lean_dec_ref_known(v_x_1214_, 1);
                    v___x_1242_ = l_IO_Error_toString___closed__1;
                    v___x_1243_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1243_, 0, v_details_1241_);
                    v___x_1244_ =
                        l_IO_Error_otherErrorToString(v___x_1242_, v_osCode_1240_, v___x_1243_);
                    return v___x_1244_;
                }
                3 => {
                    v_osCode_1245_ = lean_ctor_get_uint32(
                        v_x_1214_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_details_1246_ = lean_ctor_get(v_x_1214_, 0);
                    lean_inc_ref(v_details_1246_);
                    lean_dec_ref_known(v_x_1214_, 1);
                    v___x_1247_ = l_IO_Error_toString___closed__2;
                    v___x_1248_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1248_, 0, v_details_1246_);
                    v___x_1249_ =
                        l_IO_Error_otherErrorToString(v___x_1247_, v_osCode_1245_, v___x_1248_);
                    return v___x_1249_;
                }
                4 => {
                    v_osCode_1250_ = lean_ctor_get_uint32(
                        v_x_1214_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_details_1251_ = lean_ctor_get(v_x_1214_, 0);
                    lean_inc_ref(v_details_1251_);
                    lean_dec_ref_known(v_x_1214_, 1);
                    v___x_1252_ = l_IO_Error_toString___closed__3;
                    v___x_1253_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1253_, 0, v_details_1251_);
                    v___x_1254_ =
                        l_IO_Error_otherErrorToString(v___x_1252_, v_osCode_1250_, v___x_1253_);
                    return v___x_1254_;
                }
                5 => {
                    v_osCode_1255_ = lean_ctor_get_uint32(
                        v_x_1214_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    lean_dec_ref_known(v_x_1214_, 1);
                    v___x_1256_ = l_IO_Error_toString___closed__4;
                    v___x_1257_ = lean_box(0);
                    v___x_1258_ =
                        l_IO_Error_otherErrorToString(v___x_1256_, v_osCode_1255_, v___x_1257_);
                    return v___x_1258_;
                }
                6 => {
                    v_osCode_1259_ = lean_ctor_get_uint32(
                        v_x_1214_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    lean_dec_ref_known(v_x_1214_, 1);
                    v___x_1260_ = l_IO_Error_toString___closed__5;
                    v___x_1261_ = lean_box(0);
                    v___x_1262_ =
                        l_IO_Error_otherErrorToString(v___x_1260_, v_osCode_1259_, v___x_1261_);
                    return v___x_1262_;
                }
                7 => {
                    v_osCode_1263_ = lean_ctor_get_uint32(
                        v_x_1214_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_details_1264_ = lean_ctor_get(v_x_1214_, 0);
                    lean_inc_ref(v_details_1264_);
                    lean_dec_ref_known(v_x_1214_, 1);
                    v___x_1265_ = l_IO_Error_toString___closed__6;
                    v___x_1266_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1266_, 0, v_details_1264_);
                    v___x_1267_ =
                        l_IO_Error_otherErrorToString(v___x_1265_, v_osCode_1263_, v___x_1266_);
                    return v___x_1267_;
                }
                8 => {
                    v_osCode_1268_ = lean_ctor_get_uint32(
                        v_x_1214_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_details_1269_ = lean_ctor_get(v_x_1214_, 0);
                    lean_inc_ref(v_details_1269_);
                    lean_dec_ref_known(v_x_1214_, 1);
                    v___x_1270_ = l_IO_Error_toString___closed__7;
                    v___x_1271_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1271_, 0, v_details_1269_);
                    v___x_1272_ =
                        l_IO_Error_otherErrorToString(v___x_1270_, v_osCode_1268_, v___x_1271_);
                    return v___x_1272_;
                }
                9 => {
                    v_osCode_1273_ = lean_ctor_get_uint32(
                        v_x_1214_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_details_1274_ = lean_ctor_get(v_x_1214_, 0);
                    lean_inc_ref(v_details_1274_);
                    lean_dec_ref_known(v_x_1214_, 1);
                    v___x_1275_ = l_IO_Error_toString___closed__8;
                    v___x_1276_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1276_, 0, v_details_1274_);
                    v___x_1277_ =
                        l_IO_Error_otherErrorToString(v___x_1275_, v_osCode_1273_, v___x_1276_);
                    return v___x_1277_;
                }
                10 => {
                    v_filename_1278_ = lean_ctor_get(v_x_1214_, 0);
                    lean_inc_ref(v_filename_1278_);
                    v_osCode_1279_ = lean_ctor_get_uint32(
                        v_x_1214_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v_details_1280_ = lean_ctor_get(v_x_1214_, 1);
                    lean_inc_ref(v_details_1280_);
                    lean_dec_ref_known(v_x_1214_, 2);
                    v___x_1281_ = l_IO_Error_toString___closed__9;
                    v___x_1282_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1282_, 0, v_details_1280_);
                    v___x_1283_ = l_IO_Error_fopenErrorToString(
                        v___x_1281_,
                        v_filename_1278_,
                        v_osCode_1279_,
                        v___x_1282_,
                    );
                    lean_dec_ref(v_filename_1278_);
                    return v___x_1283_;
                }
                11 => {
                    v_filename_1284_ = lean_ctor_get(v_x_1214_, 0);
                    lean_inc_ref(v_filename_1284_);
                    v_osCode_1285_ = lean_ctor_get_uint32(
                        v_x_1214_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    lean_dec_ref_known(v_x_1214_, 2);
                    v___x_1286_ = l_IO_Error_toString___closed__10;
                    v___x_1287_ = lean_box(0);
                    v___x_1288_ = l_IO_Error_fopenErrorToString(
                        v___x_1286_,
                        v_filename_1284_,
                        v_osCode_1285_,
                        v___x_1287_,
                    );
                    lean_dec_ref(v_filename_1284_);
                    return v___x_1288_;
                }
                12 => {
                    v_filename_1289_ = lean_ctor_get(v_x_1214_, 0);
                    lean_inc(v_filename_1289_);
                    if lean_obj_tag(v_filename_1289_) == 0 {
                        v_osCode_1290_ = lean_ctor_get_uint32(
                            v_x_1214_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v_details_1291_ = lean_ctor_get(v_x_1214_, 1);
                        lean_inc_ref(v_details_1291_);
                        lean_dec_ref_known(v_x_1214_, 2);
                        v___x_1292_ = l_IO_Error_toString___closed__11;
                        v___x_1293_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1293_, 0, v_details_1291_);
                        v___x_1294_ =
                            l_IO_Error_otherErrorToString(v___x_1292_, v_osCode_1290_, v___x_1293_);
                        return v___x_1294_;
                    } else {
                        v_osCode_1295_ = lean_ctor_get_uint32(
                            v_x_1214_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v_details_1296_ = lean_ctor_get(v_x_1214_, 1);
                        lean_inc_ref(v_details_1296_);
                        lean_dec_ref_known(v_x_1214_, 2);
                        v_val_1297_ = lean_ctor_get(v_filename_1289_, 0);
                        v_isSharedCheck_1306_ = (!lean_is_exclusive(v_filename_1289_)) as u8;
                        if v_isSharedCheck_1306_ == 0 {
                            v___x_1299_ = v_filename_1289_;
                            v_isShared_1300_ = v_isSharedCheck_1306_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_1297_);
                            lean_dec(v_filename_1289_);
                            v___x_1299_ = lean_box(0);
                            v_isShared_1300_ = v_isSharedCheck_1306_;
                            state = 4;
                            continue;
                        }
                    }
                }
                13 => {
                    v_filename_1307_ = lean_ctor_get(v_x_1214_, 0);
                    if lean_obj_tag(v_filename_1307_) == 0 {
                        v_osCode_1308_ = lean_ctor_get_uint32(
                            v_x_1214_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v_details_1309_ = lean_ctor_get(v_x_1214_, 1);
                        lean_inc_ref(v_details_1309_);
                        lean_dec_ref_known(v_x_1214_, 2);
                        v_code_1216_ = v_osCode_1308_;
                        v_details_1217_ = v_details_1309_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc_ref(v_filename_1307_);
                        v_osCode_1310_ = lean_ctor_get_uint32(
                            v_x_1214_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v_details_1311_ = lean_ctor_get(v_x_1214_, 1);
                        lean_inc_ref(v_details_1311_);
                        lean_dec_ref_known(v_x_1214_, 2);
                        v_val_1312_ = lean_ctor_get(v_filename_1307_, 0);
                        lean_inc(v_val_1312_);
                        lean_dec_ref_known(v_filename_1307_, 1);
                        v___x_1313_ = lean_box(0);
                        v___x_1314_ = l_IO_Error_fopenErrorToString(
                            v_details_1311_,
                            v_val_1312_,
                            v_osCode_1310_,
                            v___x_1313_,
                        );
                        lean_dec(v_val_1312_);
                        return v___x_1314_;
                    }
                }
                14 => {
                    v_filename_1315_ = lean_ctor_get(v_x_1214_, 0);
                    lean_inc(v_filename_1315_);
                    if lean_obj_tag(v_filename_1315_) == 0 {
                        v_osCode_1316_ = lean_ctor_get_uint32(
                            v_x_1214_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v_details_1317_ = lean_ctor_get(v_x_1214_, 1);
                        lean_inc_ref(v_details_1317_);
                        lean_dec_ref_known(v_x_1214_, 2);
                        v___x_1318_ = l_IO_Error_toString___closed__12;
                        v___x_1319_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1319_, 0, v_details_1317_);
                        v___x_1320_ =
                            l_IO_Error_otherErrorToString(v___x_1318_, v_osCode_1316_, v___x_1319_);
                        return v___x_1320_;
                    } else {
                        v_osCode_1321_ = lean_ctor_get_uint32(
                            v_x_1214_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v_details_1322_ = lean_ctor_get(v_x_1214_, 1);
                        lean_inc_ref(v_details_1322_);
                        lean_dec_ref_known(v_x_1214_, 2);
                        v_val_1323_ = lean_ctor_get(v_filename_1315_, 0);
                        v_isSharedCheck_1332_ = (!lean_is_exclusive(v_filename_1315_)) as u8;
                        if v_isSharedCheck_1332_ == 0 {
                            v___x_1325_ = v_filename_1315_;
                            v_isShared_1326_ = v_isSharedCheck_1332_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_val_1323_);
                            lean_dec(v_filename_1315_);
                            v___x_1325_ = lean_box(0);
                            v_isShared_1326_ = v_isSharedCheck_1332_;
                            state = 6;
                            continue;
                        }
                    }
                }
                15 => {
                    v_filename_1333_ = lean_ctor_get(v_x_1214_, 0);
                    lean_inc(v_filename_1333_);
                    if lean_obj_tag(v_filename_1333_) == 0 {
                        v_osCode_1334_ = lean_ctor_get_uint32(
                            v_x_1214_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v_details_1335_ = lean_ctor_get(v_x_1214_, 1);
                        lean_inc_ref(v_details_1335_);
                        lean_dec_ref_known(v_x_1214_, 2);
                        v___x_1336_ = l_IO_Error_toString___closed__13;
                        v___x_1337_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1337_, 0, v_details_1335_);
                        v___x_1338_ =
                            l_IO_Error_otherErrorToString(v___x_1336_, v_osCode_1334_, v___x_1337_);
                        return v___x_1338_;
                    } else {
                        v_osCode_1339_ = lean_ctor_get_uint32(
                            v_x_1214_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v_details_1340_ = lean_ctor_get(v_x_1214_, 1);
                        lean_inc_ref(v_details_1340_);
                        lean_dec_ref_known(v_x_1214_, 2);
                        v_val_1341_ = lean_ctor_get(v_filename_1333_, 0);
                        v_isSharedCheck_1350_ = (!lean_is_exclusive(v_filename_1333_)) as u8;
                        if v_isSharedCheck_1350_ == 0 {
                            v___x_1343_ = v_filename_1333_;
                            v_isShared_1344_ = v_isSharedCheck_1350_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_val_1341_);
                            lean_dec(v_filename_1333_);
                            v___x_1343_ = lean_box(0);
                            v_isShared_1344_ = v_isSharedCheck_1350_;
                            state = 8;
                            continue;
                        }
                    }
                }
                16 => {
                    v_filename_1351_ = lean_ctor_get(v_x_1214_, 0);
                    lean_inc(v_filename_1351_);
                    if lean_obj_tag(v_filename_1351_) == 0 {
                        v_osCode_1352_ = lean_ctor_get_uint32(
                            v_x_1214_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v_details_1353_ = lean_ctor_get(v_x_1214_, 1);
                        lean_inc_ref(v_details_1353_);
                        lean_dec_ref_known(v_x_1214_, 2);
                        v___x_1354_ = l_IO_Error_toString___closed__14;
                        v___x_1355_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1355_, 0, v_details_1353_);
                        v___x_1356_ =
                            l_IO_Error_otherErrorToString(v___x_1354_, v_osCode_1352_, v___x_1355_);
                        return v___x_1356_;
                    } else {
                        v_osCode_1357_ = lean_ctor_get_uint32(
                            v_x_1214_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v_details_1358_ = lean_ctor_get(v_x_1214_, 1);
                        lean_inc_ref(v_details_1358_);
                        lean_dec_ref_known(v_x_1214_, 2);
                        v_val_1359_ = lean_ctor_get(v_filename_1351_, 0);
                        v_isSharedCheck_1368_ = (!lean_is_exclusive(v_filename_1351_)) as u8;
                        if v_isSharedCheck_1368_ == 0 {
                            v___x_1361_ = v_filename_1351_;
                            v_isShared_1362_ = v_isSharedCheck_1368_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_val_1359_);
                            lean_dec(v_filename_1351_);
                            v___x_1361_ = lean_box(0);
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
                    v_msg_1370_ = lean_ctor_get(v_x_1214_, 0);
                    lean_inc_ref(v_msg_1370_);
                    lean_dec_ref_known(v_x_1214_, 1);
                    return v_msg_1370_;
                }
            },
            1 => {
                v___x_1218_ = lean_box(0);
                v___x_1219_ =
                    l_IO_Error_otherErrorToString(v_details_1217_, v_code_1216_, v___x_1218_);
                return v___x_1219_;
            }
            2 => {
                v___x_1232_ = l_IO_Error_toString___closed__0;
                if v_isShared_1231_ == 0 {
                    lean_ctor_set(v___x_1230_, 0, v_details_1227_);
                    v___x_1234_ = v___x_1230_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_details_1227_);
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
                lean_dec(v_val_1228_);
                return v___x_1235_;
            }
            4 => {
                v___x_1301_ = l_IO_Error_toString___closed__11;
                if v_isShared_1300_ == 0 {
                    lean_ctor_set(v___x_1299_, 0, v_details_1296_);
                    v___x_1303_ = v___x_1299_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_details_1296_);
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
                lean_dec(v_val_1297_);
                return v___x_1304_;
            }
            6 => {
                v___x_1327_ = l_IO_Error_toString___closed__12;
                if v_isShared_1326_ == 0 {
                    lean_ctor_set(v___x_1325_, 0, v_details_1322_);
                    v___x_1329_ = v___x_1325_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_details_1322_);
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
                lean_dec(v_val_1323_);
                return v___x_1330_;
            }
            8 => {
                v___x_1345_ = l_IO_Error_toString___closed__13;
                if v_isShared_1344_ == 0 {
                    lean_ctor_set(v___x_1343_, 0, v_details_1340_);
                    v___x_1347_ = v___x_1343_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_details_1340_);
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
                lean_dec(v_val_1341_);
                return v___x_1348_;
            }
            10 => {
                v___x_1363_ = l_IO_Error_toString___closed__14;
                if v_isShared_1362_ == 0 {
                    lean_ctor_set(v___x_1361_, 0, v_details_1358_);
                    v___x_1365_ = v___x_1361_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_details_1358_);
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
                lean_dec(v_val_1359_);
                return v___x_1366_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_System_IOError(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Modify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_System_IOError(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_System_IOError(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Modify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_System_IOError(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_System_IOError(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_System_IOError(builtin);
}

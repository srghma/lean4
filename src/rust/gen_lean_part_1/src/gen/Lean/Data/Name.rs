// Lean compiler output
// Module: Lean.Data.Name
// Imports: Init.Data.Ord.Basic Init.Data.String.TakeDrop Init.Data.Ord.String Init.Data.Ord.UInt Init.Data.String.Search Init.Data.String.Length
use crate::ffi::{
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed, lean_ptr_addr, lean_string_compare, lean_string_dec_eq,
    lean_string_memcmp, lean_string_utf8_byte_size, lean_string_utf8_get_fast,
    lean_string_utf8_next_fast, lean_uint32_dec_eq, lean_uint32_dec_le, lean_uint64_dec_eq,
    lean_uint64_dec_lt, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::r#gen::Init::Data::List::Basic::{l_List_head_x3f___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::Ord::Basic::{
    initialize_Init_Data_Ord_Basic, l_instDecidableEqOrdering,
    runtime_initialize_Init_Data_Ord_Basic,
};
use crate::r#gen::Init::Data::Ord::String::{
    initialize_Init_Data_Ord_String, runtime_initialize_Init_Data_Ord_String,
};
use crate::r#gen::Init::Data::Ord::UInt::{
    initialize_Init_Data_Ord_UInt, runtime_initialize_Init_Data_Ord_UInt,
};
use crate::r#gen::Init::Data::String::Basic::{l_String_Slice_Pos_get_x3f, l_String_Slice_pos_x21};
use crate::r#gen::Init::Data::String::Length::{
    initialize_Init_Data_String_Length, runtime_initialize_Init_Data_String_Length,
};
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_num___override, l_Lean_Name_str___override};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
static mut l_Lean_Name_hashEx___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Name_hashEx___closed__0: u64 = 0;
pub static l_panic___at___00Lean_Name_getString_x21_spec__0___closed__0_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_panic___at___00Lean_Name_getString_x21_spec__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_Name_getString_x21_spec__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Name_getString_x21___closed__0_value: leanh::LeanStringObject<15> =
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
            76, 101, 97, 110, 46, 68, 97, 116, 97, 46, 78, 97, 109, 101, 0,
        ],
    };
static mut l_Lean_Name_getString_x21___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_getString_x21___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Name_getString_x21___closed__1_value: leanh::LeanStringObject<21> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            76, 101, 97, 110, 46, 78, 97, 109, 101, 46, 103, 101, 116, 83, 116, 114, 105, 110, 103,
            33, 0,
        ],
    };
static mut l_Lean_Name_getString_x21___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_getString_x21___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Name_getString_x21___closed__2_value: leanh::LeanStringObject<34> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97,
            115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
        ],
    };
static mut l_Lean_Name_getString_x21___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_getString_x21___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Name_getString_x21___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Name_getString_x21___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Name_isInternalDetail___closed__0_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [101, 113, 95, 0],
    };
static mut l_Lean_Name_isInternalDetail___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_isInternalDetail___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Name_isInternalDetail___closed__1_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [109, 97, 116, 99, 104, 95, 0],
    };
static mut l_Lean_Name_isInternalDetail___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_isInternalDetail___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Name_isInternalDetail___closed__2_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [112, 114, 111, 111, 102, 95, 0],
    };
static mut l_Lean_Name_isInternalDetail___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_isInternalDetail___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Name_isInternalDetail___closed__3_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [111, 109, 101, 103, 97, 95, 0],
    };
static mut l_Lean_Name_isInternalDetail___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_isInternalDetail___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Name_isInternalDetail___closed__4_value: leanh::LeanStringObject<2> =
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
        m_data: [95, 0],
    };
static mut l_Lean_Name_isInternalDetail___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_isInternalDetail___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Name_isInternalDetail___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Name_isInternalDetail___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Name_isImplementationDetail___closed__0_value: leanh::LeanStringObject<3> =
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
        m_data: [95, 95, 0],
    };
static mut l_Lean_Name_isImplementationDetail___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_isImplementationDetail___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Name_isImplementationDetail___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Name_isImplementationDetail___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__0_value:
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
static mut l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__1_value:
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
    m_data: [76, 105, 110, 116, 101, 114, 0],
};
static mut l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__2_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [83, 105, 109, 112, 114, 111, 99, 0],
};
static mut l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__3_value:
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
    m_data: [77, 101, 116, 97, 0],
};
static mut l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Name_isMetaprogramming___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
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
static mut l_Lean_Name_isMetaprogramming___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_isMetaprogramming___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Name_isMetaprogramming___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Name_isMetaprogramming___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Name_isMetaprogramming___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Name_isMetaprogramming___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Name_hashEx___closed__0() -> u64 {
    let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: u64 = 0;
    v___x_452_ = leanh::lean_unsigned_to_nat(1723);
    v___x_453_ = lean_uint64_of_nat(v___x_452_);
    return v___x_453_;
}
pub unsafe fn lean_name_hash_exported(mut v_a_454_: *mut leanh::LeanObject) -> u64 {
    if leanh::lean_obj_tag(v_a_454_) == 0 {
        let mut v___x_455_: u64 = 0;
        v___x_455_ = leanh::lean_uint64_once(
            core::ptr::addr_of_mut!(l_Lean_Name_hashEx___closed__0),
            core::ptr::addr_of_mut!(l_Lean_Name_hashEx___closed__0_once),
            _init_l_Lean_Name_hashEx___closed__0,
        );
        return v___x_455_;
    } else {
        let mut v_hash_456_: u64 = 0;
        v_hash_456_ = leanh::lean_ctor_get_uint64(
            v_a_454_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        );
        leanh::lean_dec(v_a_454_);
        return v_hash_456_;
    }
}
pub unsafe fn l_Lean_Name_hashEx___boxed(
    mut v_a_457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_458_: u64 = 0;
    let mut v_r_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_458_ = lean_name_hash_exported(v_a_457_);
    v_r_459_ = leanh::lean_box_uint64(v_res_458_);
    return v_r_459_;
}
pub unsafe fn l_Lean_Name_getPrefix(
    mut v_x_460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_460_) == 0 {
        return v_x_460_;
    } else {
        let mut v_pre_461_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_461_ = leanh::lean_ctor_get(v_x_460_, 0);
        leanh::lean_inc(v_pre_461_);
        return v_pre_461_;
    }
}
pub unsafe fn l_Lean_Name_getPrefix___boxed(
    mut v_x_462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_463_ = l_Lean_Name_getPrefix(v_x_462_);
    leanh::lean_dec(v_x_462_);
    return v_res_463_;
}
pub unsafe fn l_panic___at___00Lean_Name_getString_x21_spec__0(
    mut v_msg_465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_466_ = l_panic___at___00Lean_Name_getString_x21_spec__0___closed__0;
    v___x_467_ = lean_panic_fn_borrowed(v___x_466_, v_msg_465_);
    return v___x_467_;
}
pub unsafe fn _init_l_Lean_Name_getString_x21___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_471_ = l_Lean_Name_getString_x21___closed__2;
    v___x_472_ = leanh::lean_unsigned_to_nat(15);
    v___x_473_ = leanh::lean_unsigned_to_nat(31);
    v___x_474_ = l_Lean_Name_getString_x21___closed__1;
    v___x_475_ = l_Lean_Name_getString_x21___closed__0;
    v___x_476_ =
        l_mkPanicMessageWithDecl(v___x_475_, v___x_474_, v___x_473_, v___x_472_, v___x_471_);
    return v___x_476_;
}
pub unsafe fn l_Lean_Name_getString_x21(
    mut v_x_477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_477_) == 1 {
        let mut v_str_478_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_str_478_ = leanh::lean_ctor_get(v_x_477_, 1);
        leanh::lean_inc_ref(v_str_478_);
        return v_str_478_;
    } else {
        let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_479_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Name_getString_x21___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Name_getString_x21___closed__3_once),
            _init_l_Lean_Name_getString_x21___closed__3,
        );
        v___x_480_ = l_panic___at___00Lean_Name_getString_x21_spec__0(v___x_479_);
        return v___x_480_;
    }
}
pub unsafe fn l_Lean_Name_getString_x21___boxed(
    mut v_x_481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_482_ = l_Lean_Name_getString_x21(v_x_481_);
    leanh::lean_dec(v_x_481_);
    return v_res_482_;
}
pub unsafe fn l_Lean_Name_getNumParts(
    mut v_x_483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_483_) == 0 {
        let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_484_ = leanh::lean_unsigned_to_nat(0);
        return v___x_484_;
    } else {
        let mut v_pre_485_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_488_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_485_ = leanh::lean_ctor_get(v_x_483_, 0);
        v___x_486_ = l_Lean_Name_getNumParts(v_pre_485_);
        v___x_487_ = leanh::lean_unsigned_to_nat(1);
        v___x_488_ = lean_nat_add(v___x_486_, v___x_487_);
        leanh::lean_dec(v___x_486_);
        return v___x_488_;
    }
}
pub unsafe fn l_Lean_Name_getNumParts___boxed(
    mut v_x_489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_490_ = l_Lean_Name_getNumParts(v_x_489_);
    leanh::lean_dec(v_x_489_);
    return v_res_490_;
}
pub unsafe fn l_Lean_Name_updatePrefix(
    mut v_x_491_: *mut leanh::LeanObject,
    mut v_x_492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_491_) {
        0 => {
            leanh::lean_dec(v_x_492_);
            return v_x_491_;
        }
        1 => {
            let mut v_str_493_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_str_493_ = leanh::lean_ctor_get(v_x_491_, 1);
            leanh::lean_inc_ref(v_str_493_);
            leanh::lean_dec_ref_known(v_x_491_, 2);
            v___x_494_ = l_Lean_Name_str___override(v_x_492_, v_str_493_);
            return v___x_494_;
        }
        _ => {
            let mut v_i_495_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_i_495_ = leanh::lean_ctor_get(v_x_491_, 1);
            leanh::lean_inc(v_i_495_);
            leanh::lean_dec_ref_known(v_x_491_, 2);
            v___x_496_ = l_Lean_Name_num___override(v_x_492_, v_i_495_);
            return v___x_496_;
        }
    }
}
pub unsafe fn l_Lean_Name_componentsRev(
    mut v_x_497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_497_) {
        0 => {
            let mut v___x_498_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_498_ = leanh::lean_box(0);
            return v___x_498_;
        }
        1 => {
            let mut v_pre_499_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_str_500_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_501_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_pre_499_ = leanh::lean_ctor_get(v_x_497_, 0);
            leanh::lean_inc(v_pre_499_);
            v_str_500_ = leanh::lean_ctor_get(v_x_497_, 1);
            leanh::lean_inc_ref(v_str_500_);
            leanh::lean_dec_ref_known(v_x_497_, 2);
            v___x_501_ = leanh::lean_box(0);
            v___x_502_ = l_Lean_Name_str___override(v___x_501_, v_str_500_);
            v___x_503_ = l_Lean_Name_componentsRev(v_pre_499_);
            v___x_504_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_504_, 0, v___x_502_);
            leanh::lean_ctor_set(v___x_504_, 1, v___x_503_);
            return v___x_504_;
        }
        _ => {
            let mut v_pre_505_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_i_506_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_pre_505_ = leanh::lean_ctor_get(v_x_497_, 0);
            leanh::lean_inc(v_pre_505_);
            v_i_506_ = leanh::lean_ctor_get(v_x_497_, 1);
            leanh::lean_inc(v_i_506_);
            leanh::lean_dec_ref_known(v_x_497_, 2);
            v___x_507_ = leanh::lean_box(0);
            v___x_508_ = l_Lean_Name_num___override(v___x_507_, v_i_506_);
            v___x_509_ = l_Lean_Name_componentsRev(v_pre_505_);
            v___x_510_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_510_, 0, v___x_508_);
            leanh::lean_ctor_set(v___x_510_, 1, v___x_509_);
            return v___x_510_;
        }
    }
}
pub unsafe fn l_Lean_Name_components(
    mut v_n_511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_512_ = l_Lean_Name_componentsRev(v_n_511_);
    v___x_513_ = l_List_reverse___redArg(v___x_512_);
    return v___x_513_;
}
pub unsafe fn l_Lean_Name_eqStr(
    mut v_x_514_: *mut leanh::LeanObject,
    mut v_x_515_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_514_) == 1 {
        let mut v_pre_516_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_516_ = leanh::lean_ctor_get(v_x_514_, 0);
        if leanh::lean_obj_tag(v_pre_516_) == 0 {
            let mut v_str_517_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_518_: u8 = 0;
            v_str_517_ = leanh::lean_ctor_get(v_x_514_, 1);
            v___x_518_ = lean_string_dec_eq(v_str_517_, v_x_515_);
            return v___x_518_;
        } else {
            let mut v___x_519_: u8 = 0;
            v___x_519_ = 0;
            return v___x_519_;
        }
    } else {
        let mut v___x_520_: u8 = 0;
        v___x_520_ = 0;
        return v___x_520_;
    }
}
pub unsafe fn l_Lean_Name_eqStr___boxed(
    mut v_x_521_: *mut leanh::LeanObject,
    mut v_x_522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_523_: u8 = 0;
    let mut v_r_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_523_ = l_Lean_Name_eqStr(v_x_521_, v_x_522_);
    leanh::lean_dec_ref(v_x_522_);
    leanh::lean_dec(v_x_521_);
    v_r_524_ = leanh::lean_box((v_res_523_) as usize);
    return v_r_524_;
}
pub unsafe fn l_Lean_Name_isPrefixOf(
    mut v_x_525_: *mut leanh::LeanObject,
    mut v_x_526_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_527_: u8 = 0;
    let mut v_pre_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_526_) == 0 {
                    v___x_527_ = lean_name_eq(v_x_525_, v_x_526_);
                    return v___x_527_;
                } else {
                    v_pre_528_ = leanh::lean_ctor_get(v_x_526_, 0);
                    v___x_529_ = lean_name_eq(v_x_525_, v_x_526_);
                    if v___x_529_ == 0 {
                        v_x_526_ = v_pre_528_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_529_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Name_isPrefixOf___boxed(
    mut v_x_531_: *mut leanh::LeanObject,
    mut v_x_532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_533_: u8 = 0;
    let mut v_r_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_533_ = l_Lean_Name_isPrefixOf(v_x_531_, v_x_532_);
    leanh::lean_dec(v_x_532_);
    leanh::lean_dec(v_x_531_);
    v_r_534_ = leanh::lean_box((v_res_533_) as usize);
    return v_r_534_;
}
pub unsafe fn l_Lean_Name_isSuffixOf(
    mut v_x_535_: *mut leanh::LeanObject,
    mut v_x_536_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_537_: u8 = 0;
    let mut v_pre_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: u8 = 0;
    let mut v___x_544_: u8 = 0;
    let mut v_pre_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: u8 = 0;
    let mut v___x_551_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_535_) {
                0 => {
                    v___x_537_ = 1;
                    return v___x_537_;
                }
                1 => {
                    if leanh::lean_obj_tag(v_x_536_) == 1 {
                        v_pre_538_ = leanh::lean_ctor_get(v_x_535_, 0);
                        v_str_539_ = leanh::lean_ctor_get(v_x_535_, 1);
                        v_pre_540_ = leanh::lean_ctor_get(v_x_536_, 0);
                        v_str_541_ = leanh::lean_ctor_get(v_x_536_, 1);
                        v___x_542_ = lean_string_dec_eq(v_str_539_, v_str_541_);
                        if v___x_542_ == 0 {
                            return v___x_542_;
                        } else {
                            v_x_535_ = v_pre_538_;
                            v_x_536_ = v_pre_540_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_544_ = 0;
                        return v___x_544_;
                    }
                }
                _ => {
                    if leanh::lean_obj_tag(v_x_536_) == 2 {
                        v_pre_545_ = leanh::lean_ctor_get(v_x_535_, 0);
                        v_i_546_ = leanh::lean_ctor_get(v_x_535_, 1);
                        v_pre_547_ = leanh::lean_ctor_get(v_x_536_, 0);
                        v_i_548_ = leanh::lean_ctor_get(v_x_536_, 1);
                        v___x_549_ = lean_nat_dec_eq(v_i_546_, v_i_548_);
                        if v___x_549_ == 0 {
                            return v___x_549_;
                        } else {
                            v_x_535_ = v_pre_545_;
                            v_x_536_ = v_pre_547_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_551_ = 0;
                        return v___x_551_;
                    }
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Name_isSuffixOf___boxed(
    mut v_x_552_: *mut leanh::LeanObject,
    mut v_x_553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_554_: u8 = 0;
    let mut v_r_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_554_ = l_Lean_Name_isSuffixOf(v_x_552_, v_x_553_);
    leanh::lean_dec(v_x_553_);
    leanh::lean_dec(v_x_552_);
    v_r_555_ = leanh::lean_box((v_res_554_) as usize);
    return v_r_555_;
}
pub unsafe fn l_Lean_Name_cmp(
    mut v_x_556_: *mut leanh::LeanObject,
    mut v_x_557_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_x_556_) {
        0 => {
            if leanh::lean_obj_tag(v_x_557_) == 0 {
                let mut v___x_558_: u8 = 0;
                v___x_558_ = 1;
                return v___x_558_;
            } else {
                let mut v___x_559_: u8 = 0;
                v___x_559_ = 0;
                return v___x_559_;
            }
        }
        1 => {
            if leanh::lean_obj_tag(v_x_557_) == 1 {
                let mut v_pre_560_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_str_561_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_pre_562_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_str_563_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_564_: u8 = 0;
                v_pre_560_ = leanh::lean_ctor_get(v_x_556_, 0);
                v_str_561_ = leanh::lean_ctor_get(v_x_556_, 1);
                v_pre_562_ = leanh::lean_ctor_get(v_x_557_, 0);
                v_str_563_ = leanh::lean_ctor_get(v_x_557_, 1);
                v___x_564_ = l_Lean_Name_cmp(v_pre_560_, v_pre_562_);
                if v___x_564_ == 1 {
                    let mut v___x_565_: u8 = 0;
                    v___x_565_ = lean_string_compare(v_str_561_, v_str_563_);
                    return v___x_565_;
                } else {
                    return v___x_564_;
                }
            } else {
                let mut v___x_566_: u8 = 0;
                v___x_566_ = 2;
                return v___x_566_;
            }
        }
        _ => match leanh::lean_obj_tag(v_x_557_) {
            0 => {
                let mut v___x_567_: u8 = 0;
                v___x_567_ = 2;
                return v___x_567_;
            }
            1 => {
                let mut v___x_568_: u8 = 0;
                v___x_568_ = 0;
                return v___x_568_;
            }
            _ => {
                let mut v_pre_569_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_i_570_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_pre_571_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_i_572_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_573_: u8 = 0;
                v_pre_569_ = leanh::lean_ctor_get(v_x_556_, 0);
                v_i_570_ = leanh::lean_ctor_get(v_x_556_, 1);
                v_pre_571_ = leanh::lean_ctor_get(v_x_557_, 0);
                v_i_572_ = leanh::lean_ctor_get(v_x_557_, 1);
                v___x_573_ = l_Lean_Name_cmp(v_pre_569_, v_pre_571_);
                if v___x_573_ == 1 {
                    let mut v___x_574_: u8 = 0;
                    v___x_574_ = lean_nat_dec_lt(v_i_570_, v_i_572_);
                    if v___x_574_ == 0 {
                        let mut v___x_575_: u8 = 0;
                        v___x_575_ = lean_nat_dec_eq(v_i_570_, v_i_572_);
                        if v___x_575_ == 0 {
                            let mut v___x_576_: u8 = 0;
                            v___x_576_ = 2;
                            return v___x_576_;
                        } else {
                            return v___x_573_;
                        }
                    } else {
                        let mut v___x_577_: u8 = 0;
                        v___x_577_ = 0;
                        return v___x_577_;
                    }
                } else {
                    return v___x_573_;
                }
            }
        },
    }
}
pub unsafe fn l_Lean_Name_cmp___boxed(
    mut v_x_578_: *mut leanh::LeanObject,
    mut v_x_579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_580_: u8 = 0;
    let mut v_r_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_580_ = l_Lean_Name_cmp(v_x_578_, v_x_579_);
    leanh::lean_dec(v_x_579_);
    leanh::lean_dec(v_x_578_);
    v_r_581_ = leanh::lean_box((v_res_580_) as usize);
    return v_r_581_;
}
pub unsafe fn l_Lean_Name_lt(
    mut v_x_582_: *mut leanh::LeanObject,
    mut v_y_583_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_584_: u8 = 0;
    let mut v___x_585_: u8 = 0;
    let mut v___x_586_: u8 = 0;
    v___x_584_ = l_Lean_Name_cmp(v_x_582_, v_y_583_);
    v___x_585_ = 0;
    v___x_586_ = l_instDecidableEqOrdering(v___x_584_, v___x_585_);
    return v___x_586_;
}
pub unsafe fn l_Lean_Name_lt___boxed(
    mut v_x_587_: *mut leanh::LeanObject,
    mut v_y_588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_589_: u8 = 0;
    let mut v_r_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_589_ = l_Lean_Name_lt(v_x_587_, v_y_588_);
    leanh::lean_dec(v_y_588_);
    leanh::lean_dec(v_x_587_);
    v_r_590_ = leanh::lean_box((v_res_589_) as usize);
    return v_r_590_;
}
pub unsafe fn l_Lean_Name_quickCmpAux(
    mut v_x_591_: *mut leanh::LeanObject,
    mut v_x_592_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_593_: u8 = 0;
    let mut v___x_594_: u8 = 0;
    let mut v_pre_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: u8 = 0;
    let mut v___x_601_: u8 = 0;
    let mut v___x_602_: u8 = 0;
    let mut v___x_603_: u8 = 0;
    let mut v_pre_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: u8 = 0;
    let mut v___x_609_: u8 = 0;
    let mut v___x_610_: u8 = 0;
    let mut v___x_612_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_591_) {
                0 => {
                    if leanh::lean_obj_tag(v_x_592_) == 0 {
                        v___x_593_ = 1;
                        return v___x_593_;
                    } else {
                        v___x_594_ = 0;
                        return v___x_594_;
                    }
                }
                1 => {
                    if leanh::lean_obj_tag(v_x_592_) == 1 {
                        v_pre_595_ = leanh::lean_ctor_get(v_x_591_, 0);
                        v_str_596_ = leanh::lean_ctor_get(v_x_591_, 1);
                        v_pre_597_ = leanh::lean_ctor_get(v_x_592_, 0);
                        v_str_598_ = leanh::lean_ctor_get(v_x_592_, 1);
                        v___x_599_ = lean_string_compare(v_str_596_, v_str_598_);
                        if v___x_599_ == 1 {
                            v_x_591_ = v_pre_595_;
                            v_x_592_ = v_pre_597_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_599_;
                        }
                    } else {
                        v___x_601_ = 2;
                        return v___x_601_;
                    }
                }
                _ => match leanh::lean_obj_tag(v_x_592_) {
                    0 => {
                        v___x_602_ = 2;
                        return v___x_602_;
                    }
                    1 => {
                        v___x_603_ = 0;
                        return v___x_603_;
                    }
                    _ => {
                        v_pre_604_ = leanh::lean_ctor_get(v_x_591_, 0);
                        v_i_605_ = leanh::lean_ctor_get(v_x_591_, 1);
                        v_pre_606_ = leanh::lean_ctor_get(v_x_592_, 0);
                        v_i_607_ = leanh::lean_ctor_get(v_x_592_, 1);
                        v___x_608_ = lean_nat_dec_lt(v_i_605_, v_i_607_);
                        if v___x_608_ == 0 {
                            v___x_609_ = lean_nat_dec_eq(v_i_605_, v_i_607_);
                            if v___x_609_ == 0 {
                                v___x_610_ = 2;
                                return v___x_610_;
                            } else {
                                v_x_591_ = v_pre_604_;
                                v_x_592_ = v_pre_606_;
                                state = 0;
                                continue;
                            }
                        } else {
                            v___x_612_ = 0;
                            return v___x_612_;
                        }
                    }
                },
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Name_quickCmpAux___boxed(
    mut v_x_613_: *mut leanh::LeanObject,
    mut v_x_614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_615_: u8 = 0;
    let mut v_r_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_615_ = l_Lean_Name_quickCmpAux(v_x_613_, v_x_614_);
    leanh::lean_dec(v_x_614_);
    leanh::lean_dec(v_x_613_);
    v_r_616_ = leanh::lean_box((v_res_615_) as usize);
    return v_r_616_;
}
pub unsafe fn l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1(
    mut v_n_u2081_617_: *mut leanh::LeanObject,
    mut v_n_u2082_618_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_619_: usize = 0;
    let mut v___x_620_: usize = 0;
    let mut v___x_621_: u8 = 0;
    v___x_619_ = lean_ptr_addr(v_n_u2081_617_);
    v___x_620_ = lean_ptr_addr(v_n_u2082_618_);
    v___x_621_ = lean_usize_dec_eq(v___x_619_, v___x_620_);
    return v___x_621_;
}
pub unsafe fn l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1___boxed(
    mut v_n_u2081_622_: *mut leanh::LeanObject,
    mut v_n_u2082_623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_624_: u8 = 0;
    let mut v_r_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_624_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1(
        v_n_u2081_622_,
        v_n_u2082_623_,
    );
    leanh::lean_dec(v_n_u2082_623_);
    leanh::lean_dec(v_n_u2081_622_);
    v_r_625_ = leanh::lean_box((v_res_624_) as usize);
    return v_r_625_;
}
pub unsafe fn l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(
    mut v_n_u2081_626_: *mut leanh::LeanObject,
    mut v_n_u2082_627_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_629_: u64 = 0;
    let mut v___y_630_: u64 = 0;
    let mut v___x_631_: u8 = 0;
    let mut v___x_632_: u8 = 0;
    let mut v___x_633_: u8 = 0;
    let mut v___x_634_: u8 = 0;
    let mut v___x_635_: u8 = 0;
    let mut v___y_637_: u64 = 0;
    let mut v___x_638_: u64 = 0;
    let mut v_hash_639_: u64 = 0;
    let mut v___x_640_: u8 = 0;
    let mut v___x_641_: u64 = 0;
    let mut v_hash_642_: u64 = 0;
    let mut v___x_643_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_640_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl_unsafe__1(
                    v_n_u2081_626_,
                    v_n_u2082_627_,
                );
                if v___x_640_ == 0 {
                    if leanh::lean_obj_tag(v_n_u2081_626_) == 0 {
                        v___x_641_ = leanh::lean_uint64_once(
                            core::ptr::addr_of_mut!(l_Lean_Name_hashEx___closed__0),
                            core::ptr::addr_of_mut!(l_Lean_Name_hashEx___closed__0_once),
                            _init_l_Lean_Name_hashEx___closed__0,
                        );
                        v___y_637_ = v___x_641_;
                        state = 2;
                        continue;
                    } else {
                        v_hash_642_ = leanh::lean_ctor_get_uint64(
                            v_n_u2081_626_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_637_ = v_hash_642_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_643_ = 1;
                    return v___x_643_;
                }
            }
            1 => {
                v___x_631_ = lean_uint64_dec_lt(v___y_629_, v___y_630_);
                if v___x_631_ == 0 {
                    v___x_632_ = lean_uint64_dec_eq(v___y_629_, v___y_630_);
                    if v___x_632_ == 0 {
                        v___x_633_ = 2;
                        return v___x_633_;
                    } else {
                        v___x_634_ = l_Lean_Name_quickCmpAux(v_n_u2081_626_, v_n_u2082_627_);
                        return v___x_634_;
                    }
                } else {
                    v___x_635_ = 0;
                    return v___x_635_;
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_n_u2082_627_) == 0 {
                    v___x_638_ = leanh::lean_uint64_once(
                        core::ptr::addr_of_mut!(l_Lean_Name_hashEx___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Name_hashEx___closed__0_once),
                        _init_l_Lean_Name_hashEx___closed__0,
                    );
                    v___y_629_ = v___y_637_;
                    v___y_630_ = v___x_638_;
                    state = 1;
                    continue;
                } else {
                    v_hash_639_ = leanh::lean_ctor_get_uint64(
                        v_n_u2082_627_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_629_ = v___y_637_;
                    v___y_630_ = v_hash_639_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(
    mut v_n_u2081_644_: *mut leanh::LeanObject,
    mut v_n_u2082_645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_646_: u8 = 0;
    let mut v_r_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_646_ =
        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_n_u2081_644_, v_n_u2082_645_);
    leanh::lean_dec(v_n_u2082_645_);
    leanh::lean_dec(v_n_u2081_644_);
    v_r_647_ = leanh::lean_box((v_res_646_) as usize);
    return v_r_647_;
}
pub unsafe fn l_Lean_Name_quickLt(
    mut v_n_u2081_648_: *mut leanh::LeanObject,
    mut v_n_u2082_649_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_650_: u8 = 0;
    let mut v___x_651_: u8 = 0;
    let mut v___x_652_: u8 = 0;
    v___x_650_ =
        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_n_u2081_648_, v_n_u2082_649_);
    v___x_651_ = 0;
    v___x_652_ = l_instDecidableEqOrdering(v___x_650_, v___x_651_);
    return v___x_652_;
}
pub unsafe fn l_Lean_Name_quickLt___boxed(
    mut v_n_u2081_653_: *mut leanh::LeanObject,
    mut v_n_u2082_654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_655_: u8 = 0;
    let mut v_r_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_655_ = l_Lean_Name_quickLt(v_n_u2081_653_, v_n_u2082_654_);
    leanh::lean_dec(v_n_u2082_654_);
    leanh::lean_dec(v_n_u2081_653_);
    v_r_656_ = leanh::lean_box((v_res_655_) as usize);
    return v_r_656_;
}
pub unsafe fn l_Lean_Name_hasNum(mut v_x_657_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_658_: u8 = 0;
    let mut v_pre_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_657_) {
                0 => {
                    v___x_658_ = 0;
                    return v___x_658_;
                }
                1 => {
                    v_pre_659_ = leanh::lean_ctor_get(v_x_657_, 0);
                    v_x_657_ = v_pre_659_;
                    state = 0;
                    continue;
                }
                _ => {
                    v___x_661_ = 1;
                    return v___x_661_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Name_hasNum___boxed(
    mut v_x_662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_663_: u8 = 0;
    let mut v_r_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_663_ = l_Lean_Name_hasNum(v_x_662_);
    leanh::lean_dec(v_x_662_);
    v_r_664_ = leanh::lean_box((v_res_663_) as usize);
    return v_r_664_;
}
pub unsafe fn l_Lean_Name_isInternal(mut v_x_665_: *mut leanh::LeanObject) -> u8 {
    let mut v_pre_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_669_: u32 = 0;
    let mut v___x_670_: u32 = 0;
    let mut v___x_671_: u8 = 0;
    let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: u32 = 0;
    let mut v_val_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: u32 = 0;
    let mut v_pre_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_665_) {
                1 => {
                    v_pre_666_ = leanh::lean_ctor_get(v_x_665_, 0);
                    v_str_667_ = leanh::lean_ctor_get(v_x_665_, 1);
                    v___x_673_ = leanh::lean_unsigned_to_nat(0);
                    v___x_674_ = lean_string_utf8_byte_size(v_str_667_);
                    leanh::lean_inc_ref(v_str_667_);
                    v___x_675_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_675_, 0, v_str_667_);
                    leanh::lean_ctor_set(v___x_675_, 1, v___x_673_);
                    leanh::lean_ctor_set(v___x_675_, 2, v___x_674_);
                    v___x_676_ = l_String_Slice_Pos_get_x3f(v___x_675_, v___x_673_);
                    leanh::lean_dec_ref_known(v___x_675_, 3);
                    if leanh::lean_obj_tag(v___x_676_) == 0 {
                        v___x_677_ = 65;
                        v___y_669_ = v___x_677_;
                        state = 1;
                        continue;
                    } else {
                        v_val_678_ = leanh::lean_ctor_get(v___x_676_, 0);
                        leanh::lean_inc(v_val_678_);
                        leanh::lean_dec_ref_known(v___x_676_, 1);
                        v___x_679_ = leanh::lean_unbox_uint32(v_val_678_);
                        leanh::lean_dec(v_val_678_);
                        v___y_669_ = v___x_679_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_pre_680_ = leanh::lean_ctor_get(v_x_665_, 0);
                    v_x_665_ = v_pre_680_;
                    state = 0;
                    continue;
                }
                _ => {
                    v___x_682_ = 0;
                    return v___x_682_;
                }
            },
            1 => {
                v___x_670_ = 95;
                v___x_671_ = lean_uint32_dec_eq(v___y_669_, v___x_670_);
                if v___x_671_ == 0 {
                    v_x_665_ = v_pre_666_;
                    state = 0;
                    continue;
                } else {
                    return v___x_671_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Name_isInternal___boxed(
    mut v_x_683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_684_: u8 = 0;
    let mut v_r_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_684_ = l_Lean_Name_isInternal(v_x_683_);
    leanh::lean_dec(v_x_683_);
    v_r_685_ = leanh::lean_box((v_res_684_) as usize);
    return v_r_685_;
}
pub unsafe fn l_Lean_Name_isInternalOrNum(mut v_x_686_: *mut leanh::LeanObject) -> u8 {
    let mut v_pre_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_690_: u32 = 0;
    let mut v___x_691_: u32 = 0;
    let mut v___x_692_: u8 = 0;
    let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: u32 = 0;
    let mut v_val_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: u32 = 0;
    let mut v___x_701_: u8 = 0;
    let mut v___x_702_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_686_) {
                1 => {
                    v_pre_687_ = leanh::lean_ctor_get(v_x_686_, 0);
                    v_str_688_ = leanh::lean_ctor_get(v_x_686_, 1);
                    v___x_694_ = leanh::lean_unsigned_to_nat(0);
                    v___x_695_ = lean_string_utf8_byte_size(v_str_688_);
                    leanh::lean_inc_ref(v_str_688_);
                    v___x_696_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_696_, 0, v_str_688_);
                    leanh::lean_ctor_set(v___x_696_, 1, v___x_694_);
                    leanh::lean_ctor_set(v___x_696_, 2, v___x_695_);
                    v___x_697_ = l_String_Slice_Pos_get_x3f(v___x_696_, v___x_694_);
                    leanh::lean_dec_ref_known(v___x_696_, 3);
                    if leanh::lean_obj_tag(v___x_697_) == 0 {
                        v___x_698_ = 65;
                        v___y_690_ = v___x_698_;
                        state = 1;
                        continue;
                    } else {
                        v_val_699_ = leanh::lean_ctor_get(v___x_697_, 0);
                        leanh::lean_inc(v_val_699_);
                        leanh::lean_dec_ref_known(v___x_697_, 1);
                        v___x_700_ = leanh::lean_unbox_uint32(v_val_699_);
                        leanh::lean_dec(v_val_699_);
                        v___y_690_ = v___x_700_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v___x_701_ = 1;
                    return v___x_701_;
                }
                _ => {
                    v___x_702_ = 0;
                    return v___x_702_;
                }
            },
            1 => {
                v___x_691_ = 95;
                v___x_692_ = lean_uint32_dec_eq(v___y_690_, v___x_691_);
                if v___x_692_ == 0 {
                    v_x_686_ = v_pre_687_;
                    state = 0;
                    continue;
                } else {
                    return v___x_692_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Name_isInternalOrNum___boxed(
    mut v_x_703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_704_: u8 = 0;
    let mut v_r_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_704_ = l_Lean_Name_isInternalOrNum(v_x_703_);
    leanh::lean_dec(v_x_703_);
    v_r_705_ = leanh::lean_box((v_res_704_) as usize);
    return v_r_705_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg(
    mut v_pre_706_: *mut leanh::LeanObject,
    mut v_s_707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: u8 = 0;
    v___x_708_ = lean_string_utf8_byte_size(v_s_707_);
    v___x_709_ = lean_string_utf8_byte_size(v_pre_706_);
    v___x_710_ = lean_nat_dec_le(v___x_709_, v___x_708_);
    if v___x_710_ == 0 {
        let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_s_707_);
        v___x_711_ = leanh::lean_box(0);
        return v___x_711_;
    } else {
        let mut v___x_712_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_713_: u8 = 0;
        v___x_712_ = leanh::lean_unsigned_to_nat(0);
        v___x_713_ = lean_string_memcmp(v_s_707_, v_pre_706_, v___x_712_, v___x_712_, v___x_709_);
        if v___x_713_ == 0 {
            let mut v___x_714_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_s_707_);
            v___x_714_ = leanh::lean_box(0);
            return v___x_714_;
        } else {
            let mut v___x_715_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_716_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_717_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_718_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_s_707_);
            v___x_715_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_715_, 0, v_s_707_);
            leanh::lean_ctor_set(v___x_715_, 1, v___x_712_);
            leanh::lean_ctor_set(v___x_715_, 2, v___x_708_);
            v___x_716_ = l_String_Slice_pos_x21(v___x_715_, v___x_709_);
            leanh::lean_dec_ref_known(v___x_715_, 3);
            v___x_717_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_717_, 0, v_s_707_);
            leanh::lean_ctor_set(v___x_717_, 1, v___x_716_);
            leanh::lean_ctor_set(v___x_717_, 2, v___x_708_);
            v___x_718_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_718_, 0, v___x_717_);
            return v___x_718_;
        }
    }
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg___boxed(
    mut v_pre_719_: *mut leanh::LeanObject,
    mut v_s_720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_721_ = l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg(v_pre_719_, v_s_720_);
    leanh::lean_dec_ref(v_pre_719_);
    return v_res_721_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0(
    mut v_pre_722_: *mut leanh::LeanObject,
    mut v_s_723_: *mut leanh::LeanObject,
    mut v_pat_724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_725_ = l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg(v_pre_722_, v_s_723_);
    return v___x_725_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___boxed(
    mut v_pre_726_: *mut leanh::LeanObject,
    mut v_s_727_: *mut leanh::LeanObject,
    mut v_pat_728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_729_ = l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0(v_pre_726_, v_s_727_, v_pat_728_);
    leanh::lean_dec_ref(v_pat_728_);
    leanh::lean_dec_ref(v_pre_726_);
    return v_res_729_;
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__1(
    mut v_s_730_: *mut leanh::LeanObject,
    mut v_pos_731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: u8 = 0;
    let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: u8 = 0;
    let mut v___x_745_: u32 = 0;
    let mut v___y_747_: u8 = 0;
    let mut v___x_748_: u32 = 0;
    let mut v___x_749_: u8 = 0;
    let mut v___x_750_: u32 = 0;
    let mut v___x_751_: u8 = 0;
    let mut v___x_752_: u32 = 0;
    let mut v___x_753_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_732_ = leanh::lean_ctor_get(v_s_730_, 0);
                v_startInclusive_733_ = leanh::lean_ctor_get(v_s_730_, 1);
                v_endExclusive_734_ = leanh::lean_ctor_get(v_s_730_, 2);
                v___x_735_ = lean_nat_add(v_startInclusive_733_, v_pos_731_);
                v___x_742_ = leanh::lean_unsigned_to_nat(0);
                v___x_743_ = lean_nat_sub(v_endExclusive_734_, v___x_735_);
                v___x_744_ = lean_nat_dec_eq(v___x_742_, v___x_743_);
                leanh::lean_dec(v___x_743_);
                if v___x_744_ == 0 {
                    v___x_745_ = lean_string_utf8_get_fast(v_str_732_, v___x_735_);
                    v___x_750_ = 48;
                    v___x_751_ = lean_uint32_dec_le(v___x_750_, v___x_745_);
                    if v___x_751_ == 0 {
                        v___y_747_ = v___x_751_;
                        state = 2;
                        continue;
                    } else {
                        v___x_752_ = 57;
                        v___x_753_ = lean_uint32_dec_le(v___x_745_, v___x_752_);
                        v___y_747_ = v___x_753_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_735_);
                    return v_pos_731_;
                }
            }
            1 => {
                v___x_737_ = lean_string_utf8_next_fast(v_str_732_, v___x_735_);
                v___x_738_ = lean_nat_sub(v___x_737_, v___x_735_);
                leanh::lean_dec(v___x_735_);
                v___x_739_ = lean_nat_add(v_pos_731_, v___x_738_);
                leanh::lean_dec(v___x_738_);
                v___x_740_ = lean_nat_dec_lt(v_pos_731_, v___x_739_);
                if v___x_740_ == 0 {
                    leanh::lean_dec(v___x_739_);
                    return v_pos_731_;
                } else {
                    leanh::lean_dec(v_pos_731_);
                    v_pos_731_ = v___x_739_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_747_ == 0 {
                    v___x_748_ = 95;
                    v___x_749_ = lean_uint32_dec_eq(v___x_745_, v___x_748_);
                    if v___x_749_ == 0 {
                        leanh::lean_dec(v___x_735_);
                        return v_pos_731_;
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__1___boxed(
    mut v_s_754_: *mut leanh::LeanObject,
    mut v_pos_755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_756_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__1(v_s_754_, v_pos_755_);
    leanh::lean_dec_ref(v_s_754_);
    return v_res_756_;
}
pub unsafe fn l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(
    mut v_s_757_: *mut leanh::LeanObject,
    mut v_pre_758_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_759_ = l_String_dropPrefix_x3f___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__0___redArg(v_pre_758_, v_s_757_);
    if leanh::lean_obj_tag(v___x_759_) == 0 {
        let mut v___x_760_: u8 = 0;
        v___x_760_ = 0;
        return v___x_760_;
    } else {
        let mut v_val_761_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_startInclusive_762_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_endExclusive_763_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_766_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_767_: u8 = 0;
        v_val_761_ = leanh::lean_ctor_get(v___x_759_, 0);
        leanh::lean_inc(v_val_761_);
        leanh::lean_dec_ref_known(v___x_759_, 1);
        v_startInclusive_762_ = leanh::lean_ctor_get(v_val_761_, 1);
        leanh::lean_inc(v_startInclusive_762_);
        v_endExclusive_763_ = leanh::lean_ctor_get(v_val_761_, 2);
        leanh::lean_inc(v_endExclusive_763_);
        v___x_764_ = leanh::lean_unsigned_to_nat(0);
        v___x_765_ = l_String_Slice_Pos_skipWhile___at___00__private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix_spec__1(v_val_761_, v___x_764_);
        leanh::lean_dec(v_val_761_);
        v___x_766_ = lean_nat_sub(v_endExclusive_763_, v_startInclusive_762_);
        leanh::lean_dec(v_startInclusive_762_);
        leanh::lean_dec(v_endExclusive_763_);
        v___x_767_ = lean_nat_dec_eq(v___x_765_, v___x_766_);
        leanh::lean_dec(v___x_766_);
        leanh::lean_dec(v___x_765_);
        return v___x_767_;
    }
}
pub unsafe fn l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix___boxed(
    mut v_s_768_: *mut leanh::LeanObject,
    mut v_pre_769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_770_: u8 = 0;
    let mut v_r_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_770_ =
        l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_s_768_, v_pre_769_);
    leanh::lean_dec_ref(v_pre_769_);
    v_r_771_ = leanh::lean_box((v_res_770_) as usize);
    return v_r_771_;
}
pub unsafe fn _init_l_Lean_Name_isInternalDetail___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_777_ = l_Lean_Name_isInternalDetail___closed__4;
    v___x_778_ = lean_string_utf8_byte_size(v___x_777_);
    return v___x_778_;
}
pub unsafe fn l_Lean_Name_isInternalDetail(mut v_x_779_: *mut leanh::LeanObject) -> u8 {
    let mut v_pre_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: u8 = 0;
    let mut v___x_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: u8 = 0;
    let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: u8 = 0;
    let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: u8 = 0;
    let mut v___x_791_: u8 = 0;
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: u8 = 0;
    let mut v___x_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: u8 = 0;
    let mut v___x_798_: u8 = 0;
    let mut v___x_799_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_779_) {
                1 => {
                    v_pre_780_ = leanh::lean_ctor_get(v_x_779_, 0);
                    leanh::lean_inc(v_pre_780_);
                    v_str_781_ = leanh::lean_ctor_get(v_x_779_, 1);
                    leanh::lean_inc_ref(v_str_781_);
                    leanh::lean_dec_ref_known(v_x_779_, 2);
                    v___x_792_ = l_Lean_Name_isInternalDetail___closed__4;
                    v___x_793_ = lean_string_utf8_byte_size(v_str_781_);
                    v___x_794_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Name_isInternalDetail___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Name_isInternalDetail___closed__5_once),
                        _init_l_Lean_Name_isInternalDetail___closed__5,
                    );
                    v___x_795_ = lean_nat_dec_le(v___x_794_, v___x_793_);
                    if v___x_795_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_796_ = leanh::lean_unsigned_to_nat(0);
                        v___x_797_ = lean_string_memcmp(
                            v_str_781_, v___x_792_, v___x_796_, v___x_796_, v___x_794_,
                        );
                        if v___x_797_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_str_781_);
                            leanh::lean_dec(v_pre_780_);
                            return v___x_797_;
                        }
                    }
                }
                2 => {
                    leanh::lean_dec_ref_known(v_x_779_, 2);
                    v___x_798_ = 1;
                    return v___x_798_;
                }
                _ => {
                    v___x_799_ = l_Lean_Name_isInternalOrNum(v_x_779_);
                    leanh::lean_dec(v_x_779_);
                    return v___x_799_;
                }
            },
            1 => {
                v___x_783_ = l_Lean_Name_isInternalDetail___closed__0;
                leanh::lean_inc_ref(v_str_781_);
                v___x_784_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(
                    v_str_781_, v___x_783_,
                );
                if v___x_784_ == 0 {
                    v___x_785_ = l_Lean_Name_isInternalDetail___closed__1;
                    leanh::lean_inc_ref(v_str_781_);
                    v___x_786_ =
                        l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(
                            v_str_781_, v___x_785_,
                        );
                    if v___x_786_ == 0 {
                        v___x_787_ = l_Lean_Name_isInternalDetail___closed__2;
                        leanh::lean_inc_ref(v_str_781_);
                        v___x_788_ =
                            l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(
                                v_str_781_, v___x_787_,
                            );
                        if v___x_788_ == 0 {
                            v___x_789_ = l_Lean_Name_isInternalDetail___closed__3;
                            v___x_790_ = l___private_Lean_Data_Name_0__Lean_Name_isInternalDetail_matchPrefix(v_str_781_, v___x_789_);
                            if v___x_790_ == 0 {
                                v___x_791_ = l_Lean_Name_isInternalOrNum(v_pre_780_);
                                leanh::lean_dec(v_pre_780_);
                                return v___x_791_;
                            } else {
                                leanh::lean_dec(v_pre_780_);
                                return v___x_790_;
                            }
                        } else {
                            leanh::lean_dec_ref(v_str_781_);
                            leanh::lean_dec(v_pre_780_);
                            return v___x_788_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_str_781_);
                        leanh::lean_dec(v_pre_780_);
                        return v___x_786_;
                    }
                } else {
                    leanh::lean_dec_ref(v_str_781_);
                    leanh::lean_dec(v_pre_780_);
                    return v___x_784_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Name_isInternalDetail___boxed(
    mut v_x_800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_801_: u8 = 0;
    let mut v_r_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_801_ = l_Lean_Name_isInternalDetail(v_x_800_);
    v_r_802_ = leanh::lean_box((v_res_801_) as usize);
    return v_r_802_;
}
pub unsafe fn _init_l_Lean_Name_isImplementationDetail___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_804_ = l_Lean_Name_isImplementationDetail___closed__0;
    v___x_805_ = lean_string_utf8_byte_size(v___x_804_);
    return v___x_805_;
}
pub unsafe fn l_Lean_Name_isImplementationDetail(
    mut v_x_806_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_807_: u8 = 0;
    let mut v_pre_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: u8 = 0;
    let mut v___x_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: u8 = 0;
    let mut v_pre_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_806_) {
                0 => {
                    v___x_807_ = 0;
                    return v___x_807_;
                }
                1 => {
                    v_pre_808_ = leanh::lean_ctor_get(v_x_806_, 0);
                    if leanh::lean_obj_tag(v_pre_808_) == 0 {
                        v_str_809_ = leanh::lean_ctor_get(v_x_806_, 1);
                        v___x_810_ = l_Lean_Name_isImplementationDetail___closed__0;
                        v___x_811_ = lean_string_utf8_byte_size(v_str_809_);
                        v___x_812_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Name_isImplementationDetail___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lean_Name_isImplementationDetail___closed__1_once
                            ),
                            _init_l_Lean_Name_isImplementationDetail___closed__1,
                        );
                        v___x_813_ = lean_nat_dec_le(v___x_812_, v___x_811_);
                        if v___x_813_ == 0 {
                            return v___x_813_;
                        } else {
                            v___x_814_ = leanh::lean_unsigned_to_nat(0);
                            v___x_815_ = lean_string_memcmp(
                                v_str_809_, v___x_810_, v___x_814_, v___x_814_, v___x_812_,
                            );
                            return v___x_815_;
                        }
                    } else {
                        v_x_806_ = v_pre_808_;
                        state = 0;
                        continue;
                    }
                }
                _ => {
                    v_pre_817_ = leanh::lean_ctor_get(v_x_806_, 0);
                    v_x_806_ = v_pre_817_;
                    state = 0;
                    continue;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Name_isImplementationDetail___boxed(
    mut v_x_819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_820_: u8 = 0;
    let mut v_r_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_820_ = l_Lean_Name_isImplementationDetail(v_x_819_);
    leanh::lean_dec(v_x_819_);
    v_r_821_ = leanh::lean_box((v_res_820_) as usize);
    return v_r_821_;
}
pub unsafe fn l_Lean_Name_isAtomic(mut v_x_822_: *mut leanh::LeanObject) -> u8 {
    if leanh::lean_obj_tag(v_x_822_) == 0 {
        let mut v___x_823_: u8 = 0;
        v___x_823_ = 1;
        return v___x_823_;
    } else {
        let mut v_pre_824_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_824_ = leanh::lean_ctor_get(v_x_822_, 0);
        if leanh::lean_obj_tag(v_pre_824_) == 0 {
            let mut v___x_825_: u8 = 0;
            v___x_825_ = 1;
            return v___x_825_;
        } else {
            let mut v___x_826_: u8 = 0;
            v___x_826_ = 0;
            return v___x_826_;
        }
    }
}
pub unsafe fn l_Lean_Name_isAtomic___boxed(
    mut v_x_827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_828_: u8 = 0;
    let mut v_r_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_828_ = l_Lean_Name_isAtomic(v_x_827_);
    leanh::lean_dec(v_x_827_);
    v_r_829_ = leanh::lean_box((v_res_828_) as usize);
    return v_r_829_;
}
pub unsafe fn l_Lean_Name_isAnonymous(mut v_x_830_: *mut leanh::LeanObject) -> u8 {
    if leanh::lean_obj_tag(v_x_830_) == 0 {
        let mut v___x_831_: u8 = 0;
        v___x_831_ = 1;
        return v___x_831_;
    } else {
        let mut v___x_832_: u8 = 0;
        v___x_832_ = 0;
        return v___x_832_;
    }
}
pub unsafe fn l_Lean_Name_isAnonymous___boxed(
    mut v_x_833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_834_: u8 = 0;
    let mut v_r_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_834_ = l_Lean_Name_isAnonymous(v_x_833_);
    leanh::lean_dec(v_x_833_);
    v_r_835_ = leanh::lean_box((v_res_834_) as usize);
    return v_r_835_;
}
pub unsafe fn l_Lean_Name_isStr(mut v_x_836_: *mut leanh::LeanObject) -> u8 {
    if leanh::lean_obj_tag(v_x_836_) == 1 {
        let mut v___x_837_: u8 = 0;
        v___x_837_ = 1;
        return v___x_837_;
    } else {
        let mut v___x_838_: u8 = 0;
        v___x_838_ = 0;
        return v___x_838_;
    }
}
pub unsafe fn l_Lean_Name_isStr___boxed(
    mut v_x_839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_840_: u8 = 0;
    let mut v_r_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_840_ = l_Lean_Name_isStr(v_x_839_);
    leanh::lean_dec(v_x_839_);
    v_r_841_ = leanh::lean_box((v_res_840_) as usize);
    return v_r_841_;
}
pub unsafe fn l_Lean_Name_isNum(mut v_x_842_: *mut leanh::LeanObject) -> u8 {
    if leanh::lean_obj_tag(v_x_842_) == 2 {
        let mut v___x_843_: u8 = 0;
        v___x_843_ = 1;
        return v___x_843_;
    } else {
        let mut v___x_844_: u8 = 0;
        v___x_844_ = 0;
        return v___x_844_;
    }
}
pub unsafe fn l_Lean_Name_isNum___boxed(
    mut v_x_845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_846_: u8 = 0;
    let mut v_r_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_846_ = l_Lean_Name_isNum(v_x_845_);
    leanh::lean_dec(v_x_845_);
    v_r_847_ = leanh::lean_box((v_res_846_) as usize);
    return v_r_847_;
}
pub unsafe fn l_Lean_Name_anyS(
    mut v_n_848_: *mut leanh::LeanObject,
    mut v_f_849_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_pre_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: u8 = 0;
    let mut v___x_855_: u8 = 0;
    let mut v_pre_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_n_848_) {
                1 => {
                    v_pre_850_ = leanh::lean_ctor_get(v_n_848_, 0);
                    leanh::lean_inc(v_pre_850_);
                    v_str_851_ = leanh::lean_ctor_get(v_n_848_, 1);
                    leanh::lean_inc_ref(v_str_851_);
                    leanh::lean_dec_ref_known(v_n_848_, 2);
                    leanh::lean_inc_ref(v_f_849_);
                    v___x_852_ = leanh::lean_apply_1(v_f_849_, v_str_851_);
                    v___x_853_ = (leanh::lean_unbox(v___x_852_) as u8);
                    if v___x_853_ == 0 {
                        v_n_848_ = v_pre_850_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_pre_850_);
                        leanh::lean_dec_ref(v_f_849_);
                        v___x_855_ = (leanh::lean_unbox(v___x_852_) as u8);
                        return v___x_855_;
                    }
                }
                2 => {
                    v_pre_856_ = leanh::lean_ctor_get(v_n_848_, 0);
                    leanh::lean_inc(v_pre_856_);
                    leanh::lean_dec_ref_known(v_n_848_, 2);
                    v_n_848_ = v_pre_856_;
                    state = 0;
                    continue;
                }
                _ => {
                    leanh::lean_dec_ref(v_f_849_);
                    leanh::lean_dec(v_n_848_);
                    v___x_858_ = 0;
                    return v___x_858_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Name_anyS___boxed(
    mut v_n_859_: *mut leanh::LeanObject,
    mut v_f_860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_861_: u8 = 0;
    let mut v_r_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_861_ = l_Lean_Name_anyS(v_n_859_, v_f_860_);
    v_r_862_ = leanh::lean_box((v_res_861_) as usize);
    return v_r_862_;
}
pub unsafe fn l_List_any___at___00Lean_Name_isMetaprogramming_spec__0(
    mut v_x_867_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_868_: u8 = 0;
    let mut v_head_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: u8 = 0;
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: u8 = 0;
    let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: u8 = 0;
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: u8 = 0;
    let mut v_tail_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_867_) == 0 {
                    v___x_868_ = 0;
                    return v___x_868_;
                } else {
                    v_head_869_ = leanh::lean_ctor_get(v_x_867_, 0);
                    if leanh::lean_obj_tag(v_head_869_) == 1 {
                        v_pre_870_ = leanh::lean_ctor_get(v_head_869_, 0);
                        if leanh::lean_obj_tag(v_pre_870_) == 0 {
                            v_tail_871_ = leanh::lean_ctor_get(v_x_867_, 1);
                            v_str_872_ = leanh::lean_ctor_get(v_head_869_, 1);
                            v___x_873_ =
                                l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__0;
                            v___x_874_ = lean_string_dec_eq(v_str_872_, v___x_873_);
                            if v___x_874_ == 0 {
                                v___x_875_ = l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__1;
                                v___x_876_ = lean_string_dec_eq(v_str_872_, v___x_875_);
                                if v___x_876_ == 0 {
                                    v___x_877_ = l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__2;
                                    v___x_878_ = lean_string_dec_eq(v_str_872_, v___x_877_);
                                    if v___x_878_ == 0 {
                                        v___x_879_ = l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___closed__3;
                                        v___x_880_ = lean_string_dec_eq(v_str_872_, v___x_879_);
                                        if v___x_880_ == 0 {
                                            v_x_867_ = v_tail_871_;
                                            state = 0;
                                            continue;
                                        } else {
                                            return v___x_880_;
                                        }
                                    } else {
                                        return v___x_878_;
                                    }
                                } else {
                                    return v___x_876_;
                                }
                            } else {
                                return v___x_874_;
                            }
                        } else {
                            v_tail_882_ = leanh::lean_ctor_get(v_x_867_, 1);
                            v_x_867_ = v_tail_882_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_tail_884_ = leanh::lean_ctor_get(v_x_867_, 1);
                        v_x_867_ = v_tail_884_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_any___at___00Lean_Name_isMetaprogramming_spec__0___boxed(
    mut v_x_886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_887_: u8 = 0;
    let mut v_r_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_887_ = l_List_any___at___00Lean_Name_isMetaprogramming_spec__0(v_x_886_);
    leanh::lean_dec(v_x_886_);
    v_r_888_ = leanh::lean_box((v_res_887_) as usize);
    return v_r_888_;
}
pub unsafe fn l_Lean_Name_isMetaprogramming(mut v_n_892_: *mut leanh::LeanObject) -> u8 {
    let mut v_components_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_components_893_ = l_Lean_Name_components(v_n_892_);
    v___x_894_ = l_List_head_x3f___redArg(v_components_893_);
    if leanh::lean_obj_tag(v___x_894_) == 0 {
        let mut v___x_895_: u8 = 0;
        v___x_895_ = l_List_any___at___00Lean_Name_isMetaprogramming_spec__0(v_components_893_);
        leanh::lean_dec(v_components_893_);
        return v___x_895_;
    } else {
        let mut v_val_896_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_898_: u8 = 0;
        v_val_896_ = leanh::lean_ctor_get(v___x_894_, 0);
        leanh::lean_inc(v_val_896_);
        leanh::lean_dec_ref_known(v___x_894_, 1);
        v___x_897_ = l_Lean_Name_isMetaprogramming___closed__1;
        v___x_898_ = lean_name_eq(v_val_896_, v___x_897_);
        leanh::lean_dec(v_val_896_);
        if v___x_898_ == 0 {
            let mut v___x_899_: u8 = 0;
            v___x_899_ = l_List_any___at___00Lean_Name_isMetaprogramming_spec__0(v_components_893_);
            leanh::lean_dec(v_components_893_);
            return v___x_899_;
        } else {
            leanh::lean_dec(v_components_893_);
            return v___x_898_;
        }
    }
}
pub unsafe fn l_Lean_Name_isMetaprogramming___boxed(
    mut v_n_900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_901_: u8 = 0;
    let mut v_r_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_901_ = l_Lean_Name_isMetaprogramming(v_n_900_);
    v_r_902_ = leanh::lean_box((v_res_901_) as usize);
    return v_r_902_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Name(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Ord_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord_String(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord_UInt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Length(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Name(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Name(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Ord_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Ord_String(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Ord_UInt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Length(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Name(builtin);
}
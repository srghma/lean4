// Lean compiler output
// Module: Init.Data.String.Defs
// Imports: Init.Data.String.PosRaw Init.Data.ByteArray.Lemmas Init.Omega
use crate::ffi::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed, lean_string_append, lean_string_from_utf8_unchecked,
    lean_string_get_byte_fast, lean_string_push, lean_string_to_utf8, lean_string_utf8_byte_size,
};
use crate::r#gen::Init::Data::ByteArray::Lemmas::{
    initialize_Init_Data_ByteArray_Lemmas, runtime_initialize_Init_Data_ByteArray_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Basic::l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop;
use crate::r#gen::Init::Data::String::PosRaw::{
    initialize_Init_Data_String_PosRaw, runtime_initialize_Init_Data_String_PosRaw,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_List_foldl___redArg, l_String_toRawSubstring_x27, l_instInhabitedUInt8,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
pub static l_instAppendString___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_String_append___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instAppendString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instAppendString___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instAppendString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instAppendString___closed__0_value) as *mut leanh::LeanObject;
pub static l_String_join___closed__0_value: leanh::LeanStringObject<1> =
    leanh::LeanStringObject {
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
static mut l_String_join___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_join___closed__0_value) as *mut leanh::LeanObject;
pub static l_String_instInhabitedSlice___closed__0_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_String_join___closed__0_value) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_String_instInhabitedSlice___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_instInhabitedSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_String_instInhabitedSlice: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_instInhabitedSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_String_instCoeSlice___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_String_toSlice as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_String_instCoeSlice___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_instCoeSlice___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_String_instCoeSlice: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_instCoeSlice___closed__0_value) as *mut leanh::LeanObject;
pub static l_String_instHAddRawSlice___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_String_instHAddRawSlice___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_String_instHAddRawSlice___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_instHAddRawSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_String_instHAddRawSlice: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_instHAddRawSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_String_instHAddSliceRaw___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_String_instHAddSliceRaw___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_String_instHAddSliceRaw___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_instHAddSliceRaw___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_String_instHAddSliceRaw: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_instHAddSliceRaw___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_String_instHSubRawSlice___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_String_instHSubRawSlice___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_String_instHSubRawSlice___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_instHSubRawSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_String_instHSubRawSlice: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_instHSubRawSlice___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_String_Slice_getUTF8Byte_x21___closed__0_value: leanh::LeanStringObject<22> =
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
            73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 83, 116, 114, 105, 110, 103, 46, 68, 101,
            102, 115, 0,
        ],
    };
static mut l_String_Slice_getUTF8Byte_x21___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_getUTF8Byte_x21___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_String_Slice_getUTF8Byte_x21___closed__1_value: leanh::LeanStringObject<26> =
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
            83, 116, 114, 105, 110, 103, 46, 83, 108, 105, 99, 101, 46, 103, 101, 116, 85, 84, 70,
            56, 66, 121, 116, 101, 33, 0,
        ],
    };
static mut l_String_Slice_getUTF8Byte_x21___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_getUTF8Byte_x21___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_String_Slice_getUTF8Byte_x21___closed__2_value: leanh::LeanStringObject<38> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 38,
        m_capacity: 38,
        m_length: 37,
        m_data: [
            83, 116, 114, 105, 110, 103, 32, 115, 108, 105, 99, 101, 32, 97, 99, 99, 101, 115, 115,
            32, 105, 115, 32, 111, 117, 116, 32, 111, 102, 32, 98, 111, 117, 110, 100, 115, 46, 0,
        ],
    };
static mut l_String_Slice_getUTF8Byte_x21___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_getUTF8Byte_x21___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_String_Slice_getUTF8Byte_x21___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_String_Slice_getUTF8Byte_x21___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_String_fromUTF8___redArg(
    mut v_a_481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_a_481_);
    v___x_482_ = lean_string_from_utf8_unchecked(v_a_481_);
    return v___x_482_;
}
pub unsafe fn l_String_fromUTF8___redArg___boxed(
    mut v_a_483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_484_ = l_String_fromUTF8___redArg(v_a_483_);
    leanh::lean_dec_ref(v_a_483_);
    return v_res_484_;
}
pub unsafe fn l_String_fromUTF8(
    mut v_a_485_: *mut leanh::LeanObject,
    mut v_h_486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_a_485_);
    v___x_487_ = lean_string_from_utf8_unchecked(v_a_485_);
    return v___x_487_;
}
pub unsafe fn l_String_fromUTF8___boxed(
    mut v_a_488_: *mut leanh::LeanObject,
    mut v_h_489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_490_ = l_String_fromUTF8(v_a_488_, v_h_489_);
    leanh::lean_dec_ref(v_a_488_);
    return v_res_490_;
}
pub unsafe fn l_String_toUTF8___boxed(
    mut v_a_492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_493_ = lean_string_to_utf8(v_a_492_);
    leanh::lean_dec_ref(v_a_492_);
    return v_res_493_;
}
pub unsafe fn l_String_append___boxed(
    mut v_s_496_: *mut leanh::LeanObject,
    mut v_t_497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_498_ = lean_string_append(v_s_496_, v_t_497_);
    leanh::lean_dec_ref(v_t_497_);
    return v_res_498_;
}
pub unsafe fn l___private_Init_Data_String_Defs_0__String_push_match__1_splitter___redArg(
    mut v_x_501_: *mut leanh::LeanObject,
    mut v_x_502_: u32,
    mut v_h__1_503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toByteArray_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toByteArray_504_ = lean_string_to_utf8(v_x_501_);
    v___x_505_ = leanh::lean_box_uint32(v_x_502_);
    v___x_506_ = leanh::lean_apply_3(
        v_h__1_503_,
        v_toByteArray_504_,
        leanh::lean_box(0),
        v___x_505_,
    );
    return v___x_506_;
}
pub unsafe fn l___private_Init_Data_String_Defs_0__String_push_match__1_splitter___redArg___boxed(
    mut v_x_507_: *mut leanh::LeanObject,
    mut v_x_508_: *mut leanh::LeanObject,
    mut v_h__1_509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_18__boxed_510_: u32 = 0;
    let mut v_res_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_18__boxed_510_ = leanh::lean_unbox_uint32(v_x_508_);
    leanh::lean_dec(v_x_508_);
    v_res_511_ = l___private_Init_Data_String_Defs_0__String_push_match__1_splitter___redArg(
        v_x_507_,
        v_x_18__boxed_510_,
        v_h__1_509_,
    );
    return v_res_511_;
}
pub unsafe fn l___private_Init_Data_String_Defs_0__String_push_match__1_splitter(
    mut v_motive_512_: *mut leanh::LeanObject,
    mut v_x_513_: *mut leanh::LeanObject,
    mut v_x_514_: u32,
    mut v_h__1_515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toByteArray_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toByteArray_516_ = lean_string_to_utf8(v_x_513_);
    v___x_517_ = leanh::lean_box_uint32(v_x_514_);
    v___x_518_ = leanh::lean_apply_3(
        v_h__1_515_,
        v_toByteArray_516_,
        leanh::lean_box(0),
        v___x_517_,
    );
    return v___x_518_;
}
pub unsafe fn l___private_Init_Data_String_Defs_0__String_push_match__1_splitter___boxed(
    mut v_motive_519_: *mut leanh::LeanObject,
    mut v_x_520_: *mut leanh::LeanObject,
    mut v_x_521_: *mut leanh::LeanObject,
    mut v_h__1_522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_30__boxed_523_: u32 = 0;
    let mut v_res_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_30__boxed_523_ = leanh::lean_unbox_uint32(v_x_521_);
    leanh::lean_dec(v_x_521_);
    v_res_524_ = l___private_Init_Data_String_Defs_0__String_push_match__1_splitter(
        v_motive_519_,
        v_x_520_,
        v_x_30__boxed_523_,
        v_h__1_522_,
    );
    return v_res_524_;
}
pub unsafe fn l_String_rawStartPos(
    mut v___s_525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_526_ = leanh::lean_unsigned_to_nat(0);
    return v___x_526_;
}
pub unsafe fn l_String_rawStartPos___boxed(
    mut v___s_527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_528_ = l_String_rawStartPos(v___s_527_);
    leanh::lean_dec_ref(v___s_527_);
    return v_res_528_;
}
pub unsafe fn l_String_pushn___lam__0(
    mut v_c_529_: u32,
    mut v_s_530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_531_ = lean_string_push(v_s_530_, v_c_529_);
    return v___x_531_;
}
pub unsafe fn l_String_pushn___lam__0___boxed(
    mut v_c_532_: *mut leanh::LeanObject,
    mut v_s_533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_534_: u32 = 0;
    let mut v_res_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_534_ = leanh::lean_unbox_uint32(v_c_532_);
    leanh::lean_dec(v_c_532_);
    v_res_535_ = l_String_pushn___lam__0(v_c_boxed_534_, v_s_533_);
    return v_res_535_;
}
pub unsafe fn l_String_pushn(
    mut v_s_536_: *mut leanh::LeanObject,
    mut v_c_537_: u32,
    mut v_n_538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_539_ = leanh::lean_box_uint32(v_c_537_);
    v___f_540_ = leanh::lean_alloc_closure(
        l_String_pushn___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_540_, 0, v___x_539_);
    v___x_541_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop(
        leanh::lean_box(0),
        v___f_540_,
        v_n_538_,
        v_s_536_,
    );
    return v___x_541_;
}
pub unsafe fn l_String_pushn___boxed(
    mut v_s_542_: *mut leanh::LeanObject,
    mut v_c_543_: *mut leanh::LeanObject,
    mut v_n_544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_545_: u32 = 0;
    let mut v_res_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_545_ = leanh::lean_unbox_uint32(v_c_543_);
    leanh::lean_dec(v_c_543_);
    v_res_546_ = l_String_pushn(v_s_542_, v_c_boxed_545_, v_n_544_);
    return v_res_546_;
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(
    mut v_c_547_: u32,
    mut v_x_548_: *mut leanh::LeanObject,
    mut v_x_549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_551_: u8 = 0;
    let mut v_one_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_550_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_551_ = lean_nat_dec_eq(v_x_548_, v_zero_550_);
                if v_isZero_551_ == 1 {
                    leanh::lean_dec(v_x_548_);
                    return v_x_549_;
                } else {
                    v_one_552_ = leanh::lean_unsigned_to_nat(1);
                    v_n_553_ = lean_nat_sub(v_x_548_, v_one_552_);
                    leanh::lean_dec(v_x_548_);
                    v___x_554_ = lean_string_push(v_x_549_, v_c_547_);
                    v_x_548_ = v_n_553_;
                    v_x_549_ = v___x_554_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0___boxed(
    mut v_c_556_: *mut leanh::LeanObject,
    mut v_x_557_: *mut leanh::LeanObject,
    mut v_x_558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_559_: u32 = 0;
    let mut v_res_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_559_ = leanh::lean_unbox_uint32(v_c_556_);
    leanh::lean_dec(v_c_556_);
    v_res_560_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(v_c_boxed_559_, v_x_557_, v_x_558_);
    return v_res_560_;
}
pub unsafe fn lean_string_pushn(
    mut v_s_561_: *mut leanh::LeanObject,
    mut v_c_562_: u32,
    mut v_n_563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_564_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00String_Internal_pushnImpl_spec__0(v_c_562_, v_n_563_, v_s_561_);
    return v___x_564_;
}
pub unsafe fn l_String_Internal_pushnImpl___boxed(
    mut v_s_565_: *mut leanh::LeanObject,
    mut v_c_566_: *mut leanh::LeanObject,
    mut v_n_567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_568_: u32 = 0;
    let mut v_res_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_568_ = leanh::lean_unbox_uint32(v_c_566_);
    leanh::lean_dec(v_c_566_);
    v_res_569_ = lean_string_pushn(v_s_565_, v_c_boxed_568_, v_n_567_);
    return v_res_569_;
}
pub unsafe fn l_String_isEmpty(mut v_s_570_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: u8 = 0;
    v___x_571_ = lean_string_utf8_byte_size(v_s_570_);
    v___x_572_ = leanh::lean_unsigned_to_nat(0);
    v___x_573_ = lean_nat_dec_eq(v___x_571_, v___x_572_);
    return v___x_573_;
}
pub unsafe fn l_String_isEmpty___boxed(
    mut v_s_574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_575_: u8 = 0;
    let mut v_r_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_575_ = l_String_isEmpty(v_s_574_);
    leanh::lean_dec_ref(v_s_574_);
    v_r_576_ = leanh::lean_box((v_res_575_) as usize);
    return v_r_576_;
}
pub unsafe fn lean_string_isempty(mut v_s_577_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: u8 = 0;
    v___x_578_ = lean_string_utf8_byte_size(v_s_577_);
    leanh::lean_dec_ref(v_s_577_);
    v___x_579_ = leanh::lean_unsigned_to_nat(0);
    v___x_580_ = lean_nat_dec_eq(v___x_578_, v___x_579_);
    return v___x_580_;
}
pub unsafe fn l_String_Internal_isEmptyImpl___boxed(
    mut v_s_581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_582_: u8 = 0;
    let mut v_r_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_582_ = lean_string_isempty(v_s_581_);
    v_r_583_ = leanh::lean_box((v_res_582_) as usize);
    return v_r_583_;
}
pub unsafe fn l_String_join(
    mut v_l_585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_586_ = l_instAppendString___closed__0;
    v___x_587_ = l_String_join___closed__0;
    v___x_588_ = l_List_foldl___redArg(v___f_586_, v___x_587_, v_l_585_);
    return v___x_588_;
}
pub unsafe fn l___private_Init_Data_String_Defs_0__String_intercalate_go(
    mut v_acc_589_: *mut leanh::LeanObject,
    mut v_s_590_: *mut leanh::LeanObject,
    mut v_a_591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_591_) == 0 {
                    return v_acc_589_;
                } else {
                    v_head_592_ = leanh::lean_ctor_get(v_a_591_, 0);
                    v_tail_593_ = leanh::lean_ctor_get(v_a_591_, 1);
                    v___x_594_ = lean_string_append(v_acc_589_, v_s_590_);
                    v___x_595_ = lean_string_append(v___x_594_, v_head_592_);
                    v_acc_589_ = v___x_595_;
                    v_a_591_ = v_tail_593_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Defs_0__String_intercalate_go___boxed(
    mut v_acc_597_: *mut leanh::LeanObject,
    mut v_s_598_: *mut leanh::LeanObject,
    mut v_a_599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_600_ =
        l___private_Init_Data_String_Defs_0__String_intercalate_go(v_acc_597_, v_s_598_, v_a_599_);
    leanh::lean_dec(v_a_599_);
    leanh::lean_dec_ref(v_s_598_);
    return v_res_600_;
}
pub unsafe fn l_String_intercalate(
    mut v_s_601_: *mut leanh::LeanObject,
    mut v_x_602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_602_) == 0 {
        let mut v___x_603_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_603_ = l_String_join___closed__0;
        return v___x_603_;
    } else {
        let mut v_head_604_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_605_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_606_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_604_ = leanh::lean_ctor_get(v_x_602_, 0);
        leanh::lean_inc(v_head_604_);
        v_tail_605_ = leanh::lean_ctor_get(v_x_602_, 1);
        leanh::lean_inc(v_tail_605_);
        leanh::lean_dec_ref_known(v_x_602_, 2);
        v___x_606_ = l___private_Init_Data_String_Defs_0__String_intercalate_go(
            v_head_604_,
            v_s_601_,
            v_tail_605_,
        );
        leanh::lean_dec(v_tail_605_);
        return v___x_606_;
    }
}
pub unsafe fn l_String_intercalate___boxed(
    mut v_s_607_: *mut leanh::LeanObject,
    mut v_x_608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_609_ = l_String_intercalate(v_s_607_, v_x_608_);
    leanh::lean_dec_ref(v_s_607_);
    return v_res_609_;
}
pub unsafe fn lean_string_intercalate(
    mut v_s_610_: *mut leanh::LeanObject,
    mut v_a_611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_612_ = l_String_intercalate(v_s_610_, v_a_611_);
    leanh::lean_dec_ref(v_s_610_);
    return v___x_612_;
}
pub unsafe fn l_String_instDecidableEqPos_decEq___redArg(
    mut v_x_613_: *mut leanh::LeanObject,
    mut v_x_614_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_615_: u8 = 0;
    v___x_615_ = lean_nat_dec_eq(v_x_613_, v_x_614_);
    return v___x_615_;
}
pub unsafe fn l_String_instDecidableEqPos_decEq___redArg___boxed(
    mut v_x_616_: *mut leanh::LeanObject,
    mut v_x_617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_618_: u8 = 0;
    let mut v_r_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_618_ = l_String_instDecidableEqPos_decEq___redArg(v_x_616_, v_x_617_);
    leanh::lean_dec(v_x_617_);
    leanh::lean_dec(v_x_616_);
    v_r_619_ = leanh::lean_box((v_res_618_) as usize);
    return v_r_619_;
}
pub unsafe fn l_String_instDecidableEqPos_decEq(
    mut v_s_620_: *mut leanh::LeanObject,
    mut v_x_621_: *mut leanh::LeanObject,
    mut v_x_622_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_623_: u8 = 0;
    v___x_623_ = lean_nat_dec_eq(v_x_621_, v_x_622_);
    return v___x_623_;
}
pub unsafe fn l_String_instDecidableEqPos_decEq___boxed(
    mut v_s_624_: *mut leanh::LeanObject,
    mut v_x_625_: *mut leanh::LeanObject,
    mut v_x_626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_627_: u8 = 0;
    let mut v_r_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_627_ = l_String_instDecidableEqPos_decEq(v_s_624_, v_x_625_, v_x_626_);
    leanh::lean_dec(v_x_626_);
    leanh::lean_dec(v_x_625_);
    leanh::lean_dec_ref(v_s_624_);
    v_r_628_ = leanh::lean_box((v_res_627_) as usize);
    return v_r_628_;
}
pub unsafe fn l_String_instDecidableEqPos___redArg(
    mut v_x_629_: *mut leanh::LeanObject,
    mut v_x_630_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_631_: u8 = 0;
    v___x_631_ = lean_nat_dec_eq(v_x_629_, v_x_630_);
    return v___x_631_;
}
pub unsafe fn l_String_instDecidableEqPos___redArg___boxed(
    mut v_x_632_: *mut leanh::LeanObject,
    mut v_x_633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_634_: u8 = 0;
    let mut v_r_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_634_ = l_String_instDecidableEqPos___redArg(v_x_632_, v_x_633_);
    leanh::lean_dec(v_x_633_);
    leanh::lean_dec(v_x_632_);
    v_r_635_ = leanh::lean_box((v_res_634_) as usize);
    return v_r_635_;
}
pub unsafe fn l_String_instDecidableEqPos(
    mut v_s_636_: *mut leanh::LeanObject,
    mut v_x_637_: *mut leanh::LeanObject,
    mut v_x_638_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_639_: u8 = 0;
    v___x_639_ = lean_nat_dec_eq(v_x_637_, v_x_638_);
    return v___x_639_;
}
pub unsafe fn l_String_instDecidableEqPos___boxed(
    mut v_s_640_: *mut leanh::LeanObject,
    mut v_x_641_: *mut leanh::LeanObject,
    mut v_x_642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_643_: u8 = 0;
    let mut v_r_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_643_ = l_String_instDecidableEqPos(v_s_640_, v_x_641_, v_x_642_);
    leanh::lean_dec(v_x_642_);
    leanh::lean_dec(v_x_641_);
    leanh::lean_dec_ref(v_s_640_);
    v_r_644_ = leanh::lean_box((v_res_643_) as usize);
    return v_r_644_;
}
pub unsafe fn l_String_startPos(
    mut v_s_645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_646_ = leanh::lean_unsigned_to_nat(0);
    return v___x_646_;
}
pub unsafe fn l_String_startPos___boxed(
    mut v_s_647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_648_ = l_String_startPos(v_s_647_);
    leanh::lean_dec_ref(v_s_647_);
    return v_res_648_;
}
pub unsafe fn l_String_instInhabitedPos(
    mut v_s_649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_650_ = leanh::lean_unsigned_to_nat(0);
    return v___x_650_;
}
pub unsafe fn l_String_instInhabitedPos___boxed(
    mut v_s_651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_652_ = l_String_instInhabitedPos(v_s_651_);
    leanh::lean_dec_ref(v_s_651_);
    return v_res_652_;
}
pub unsafe fn l_String_endPos(
    mut v_s_653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_654_ = lean_string_utf8_byte_size(v_s_653_);
    return v___x_654_;
}
pub unsafe fn l_String_endPos___boxed(
    mut v_s_655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_656_ = l_String_endPos(v_s_655_);
    leanh::lean_dec_ref(v_s_655_);
    return v_res_656_;
}
pub unsafe fn l_String_instLEPos(
    mut v_s_657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_658_ = leanh::lean_box(0);
    return v___x_658_;
}
pub unsafe fn l_String_instLEPos___boxed(
    mut v_s_659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_660_ = l_String_instLEPos(v_s_659_);
    leanh::lean_dec_ref(v_s_659_);
    return v_res_660_;
}
pub unsafe fn l_String_instLTPos(
    mut v_s_661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_662_ = leanh::lean_box(0);
    return v___x_662_;
}
pub unsafe fn l_String_instLTPos___boxed(
    mut v_s_663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_664_ = l_String_instLTPos(v_s_663_);
    leanh::lean_dec_ref(v_s_663_);
    return v_res_664_;
}
pub unsafe fn l_String_instDecidableLePos___redArg(
    mut v_l_665_: *mut leanh::LeanObject,
    mut v_r_666_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_667_: u8 = 0;
    v___x_667_ = lean_nat_dec_le(v_l_665_, v_r_666_);
    return v___x_667_;
}
pub unsafe fn l_String_instDecidableLePos___redArg___boxed(
    mut v_l_668_: *mut leanh::LeanObject,
    mut v_r_669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_670_: u8 = 0;
    let mut v_r_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_670_ = l_String_instDecidableLePos___redArg(v_l_668_, v_r_669_);
    leanh::lean_dec(v_r_669_);
    leanh::lean_dec(v_l_668_);
    v_r_671_ = leanh::lean_box((v_res_670_) as usize);
    return v_r_671_;
}
pub unsafe fn l_String_instDecidableLePos(
    mut v_s_672_: *mut leanh::LeanObject,
    mut v_l_673_: *mut leanh::LeanObject,
    mut v_r_674_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_675_: u8 = 0;
    v___x_675_ = lean_nat_dec_le(v_l_673_, v_r_674_);
    return v___x_675_;
}
pub unsafe fn l_String_instDecidableLePos___boxed(
    mut v_s_676_: *mut leanh::LeanObject,
    mut v_l_677_: *mut leanh::LeanObject,
    mut v_r_678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_679_: u8 = 0;
    let mut v_r_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_679_ = l_String_instDecidableLePos(v_s_676_, v_l_677_, v_r_678_);
    leanh::lean_dec(v_r_678_);
    leanh::lean_dec(v_l_677_);
    leanh::lean_dec_ref(v_s_676_);
    v_r_680_ = leanh::lean_box((v_res_679_) as usize);
    return v_r_680_;
}
pub unsafe fn l_String_instDecidableLtPos___redArg(
    mut v_l_681_: *mut leanh::LeanObject,
    mut v_r_682_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_683_: u8 = 0;
    v___x_683_ = lean_nat_dec_lt(v_l_681_, v_r_682_);
    return v___x_683_;
}
pub unsafe fn l_String_instDecidableLtPos___redArg___boxed(
    mut v_l_684_: *mut leanh::LeanObject,
    mut v_r_685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_686_: u8 = 0;
    let mut v_r_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_686_ = l_String_instDecidableLtPos___redArg(v_l_684_, v_r_685_);
    leanh::lean_dec(v_r_685_);
    leanh::lean_dec(v_l_684_);
    v_r_687_ = leanh::lean_box((v_res_686_) as usize);
    return v_r_687_;
}
pub unsafe fn l_String_instDecidableLtPos(
    mut v_s_688_: *mut leanh::LeanObject,
    mut v_l_689_: *mut leanh::LeanObject,
    mut v_r_690_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_691_: u8 = 0;
    v___x_691_ = lean_nat_dec_lt(v_l_689_, v_r_690_);
    return v___x_691_;
}
pub unsafe fn l_String_instDecidableLtPos___boxed(
    mut v_s_692_: *mut leanh::LeanObject,
    mut v_l_693_: *mut leanh::LeanObject,
    mut v_r_694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_695_: u8 = 0;
    let mut v_r_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_695_ = l_String_instDecidableLtPos(v_s_692_, v_l_693_, v_r_694_);
    leanh::lean_dec(v_r_694_);
    leanh::lean_dec(v_l_693_);
    leanh::lean_dec_ref(v_s_692_);
    v_r_696_ = leanh::lean_box((v_res_695_) as usize);
    return v_r_696_;
}
pub unsafe fn l_String_toSlice(
    mut v_s_701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_702_ = leanh::lean_unsigned_to_nat(0);
    v___x_703_ = lean_string_utf8_byte_size(v_s_701_);
    v___x_704_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_704_, 0, v_s_701_);
    leanh::lean_ctor_set(v___x_704_, 1, v___x_702_);
    leanh::lean_ctor_set(v___x_704_, 2, v___x_703_);
    return v___x_704_;
}
pub unsafe fn l_String_Slice_utf8ByteSize(
    mut v_s_707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startInclusive_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_708_ = leanh::lean_ctor_get(v_s_707_, 1);
    v_endExclusive_709_ = leanh::lean_ctor_get(v_s_707_, 2);
    v___x_710_ = lean_nat_sub(v_endExclusive_709_, v_startInclusive_708_);
    return v___x_710_;
}
pub unsafe fn l_String_Slice_utf8ByteSize___boxed(
    mut v_s_711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_712_ = l_String_Slice_utf8ByteSize(v_s_711_);
    leanh::lean_dec_ref(v_s_711_);
    return v_res_712_;
}
pub unsafe fn l_String_instHAddRawSlice___lam__0(
    mut v_p_713_: *mut leanh::LeanObject,
    mut v_s_714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startInclusive_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_715_ = leanh::lean_ctor_get(v_s_714_, 1);
    v_endExclusive_716_ = leanh::lean_ctor_get(v_s_714_, 2);
    v___x_717_ = lean_nat_sub(v_endExclusive_716_, v_startInclusive_715_);
    v___x_718_ = lean_nat_add(v_p_713_, v___x_717_);
    leanh::lean_dec(v___x_717_);
    return v___x_718_;
}
pub unsafe fn l_String_instHAddRawSlice___lam__0___boxed(
    mut v_p_719_: *mut leanh::LeanObject,
    mut v_s_720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_721_ = l_String_instHAddRawSlice___lam__0(v_p_719_, v_s_720_);
    leanh::lean_dec_ref(v_s_720_);
    leanh::lean_dec(v_p_719_);
    return v_res_721_;
}
pub unsafe fn l_String_instHAddSliceRaw___lam__0(
    mut v_s_724_: *mut leanh::LeanObject,
    mut v_p_725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startInclusive_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_726_ = leanh::lean_ctor_get(v_s_724_, 1);
    v_endExclusive_727_ = leanh::lean_ctor_get(v_s_724_, 2);
    v___x_728_ = lean_nat_sub(v_endExclusive_727_, v_startInclusive_726_);
    v___x_729_ = lean_nat_add(v___x_728_, v_p_725_);
    leanh::lean_dec(v___x_728_);
    return v___x_729_;
}
pub unsafe fn l_String_instHAddSliceRaw___lam__0___boxed(
    mut v_s_730_: *mut leanh::LeanObject,
    mut v_p_731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_732_ = l_String_instHAddSliceRaw___lam__0(v_s_730_, v_p_731_);
    leanh::lean_dec(v_p_731_);
    leanh::lean_dec_ref(v_s_730_);
    return v_res_732_;
}
pub unsafe fn l_String_instHSubRawSlice___lam__0(
    mut v_p_735_: *mut leanh::LeanObject,
    mut v_s_736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startInclusive_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_737_ = leanh::lean_ctor_get(v_s_736_, 1);
    v_endExclusive_738_ = leanh::lean_ctor_get(v_s_736_, 2);
    v___x_739_ = lean_nat_sub(v_endExclusive_738_, v_startInclusive_737_);
    v___x_740_ = lean_nat_sub(v_p_735_, v___x_739_);
    leanh::lean_dec(v___x_739_);
    return v___x_740_;
}
pub unsafe fn l_String_instHSubRawSlice___lam__0___boxed(
    mut v_p_741_: *mut leanh::LeanObject,
    mut v_s_742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_743_ = l_String_instHSubRawSlice___lam__0(v_p_741_, v_s_742_);
    leanh::lean_dec_ref(v_s_742_);
    leanh::lean_dec(v_p_741_);
    return v_res_743_;
}
pub unsafe fn l_String_Slice_rawEndPos(
    mut v_s_746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startInclusive_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_747_ = leanh::lean_ctor_get(v_s_746_, 1);
    v_endExclusive_748_ = leanh::lean_ctor_get(v_s_746_, 2);
    v___x_749_ = lean_nat_sub(v_endExclusive_748_, v_startInclusive_747_);
    return v___x_749_;
}
pub unsafe fn l_String_Slice_rawEndPos___boxed(
    mut v_s_750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_751_ = l_String_Slice_rawEndPos(v_s_750_);
    leanh::lean_dec_ref(v_s_750_);
    return v_res_751_;
}
pub unsafe fn l_String_Slice_getUTF8Byte___redArg(
    mut v_s_752_: *mut leanh::LeanObject,
    mut v_p_753_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_str_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: u8 = 0;
    v_str_754_ = leanh::lean_ctor_get(v_s_752_, 0);
    v_startInclusive_755_ = leanh::lean_ctor_get(v_s_752_, 1);
    v___x_756_ = lean_nat_add(v_startInclusive_755_, v_p_753_);
    v___x_757_ = lean_string_get_byte_fast(v_str_754_, v___x_756_);
    return v___x_757_;
}
pub unsafe fn l_String_Slice_getUTF8Byte___redArg___boxed(
    mut v_s_758_: *mut leanh::LeanObject,
    mut v_p_759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_760_: u8 = 0;
    let mut v_r_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_760_ = l_String_Slice_getUTF8Byte___redArg(v_s_758_, v_p_759_);
    leanh::lean_dec(v_p_759_);
    leanh::lean_dec_ref(v_s_758_);
    v_r_761_ = leanh::lean_box((v_res_760_) as usize);
    return v_r_761_;
}
pub unsafe fn l_String_Slice_getUTF8Byte(
    mut v_s_762_: *mut leanh::LeanObject,
    mut v_p_763_: *mut leanh::LeanObject,
    mut v_h_764_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_str_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: u8 = 0;
    v_str_765_ = leanh::lean_ctor_get(v_s_762_, 0);
    v_startInclusive_766_ = leanh::lean_ctor_get(v_s_762_, 1);
    v___x_767_ = lean_nat_add(v_startInclusive_766_, v_p_763_);
    v___x_768_ = lean_string_get_byte_fast(v_str_765_, v___x_767_);
    return v___x_768_;
}
pub unsafe fn l_String_Slice_getUTF8Byte___boxed(
    mut v_s_769_: *mut leanh::LeanObject,
    mut v_p_770_: *mut leanh::LeanObject,
    mut v_h_771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_772_: u8 = 0;
    let mut v_r_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_772_ = l_String_Slice_getUTF8Byte(v_s_769_, v_p_770_, v_h_771_);
    leanh::lean_dec(v_p_770_);
    leanh::lean_dec_ref(v_s_769_);
    v_r_773_ = leanh::lean_box((v_res_772_) as usize);
    return v_r_773_;
}
pub unsafe fn l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(
    mut v_msg_774_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_775_: u8 = 0;
    let mut v___x_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: u8 = 0;
    v___x_775_ = l_instInhabitedUInt8;
    v___x_776_ = leanh::lean_box((v___x_775_) as usize);
    v___x_777_ = lean_panic_fn_borrowed(v___x_776_, v_msg_774_);
    leanh::lean_dec(v___x_776_);
    v___x_778_ = (leanh::lean_unbox(v___x_777_) as u8);
    leanh::lean_dec(v___x_777_);
    return v___x_778_;
}
pub unsafe fn l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0___boxed(
    mut v_msg_779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_780_: u8 = 0;
    let mut v_r_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_780_ = l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(v_msg_779_);
    v_r_781_ = leanh::lean_box((v_res_780_) as usize);
    return v_r_781_;
}
pub unsafe fn _init_l_String_Slice_getUTF8Byte_x21___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_785_ = l_String_Slice_getUTF8Byte_x21___closed__2;
    v___x_786_ = leanh::lean_unsigned_to_nat(4);
    v___x_787_ = leanh::lean_unsigned_to_nat(512);
    v___x_788_ = l_String_Slice_getUTF8Byte_x21___closed__1;
    v___x_789_ = l_String_Slice_getUTF8Byte_x21___closed__0;
    v___x_790_ =
        l_mkPanicMessageWithDecl(v___x_789_, v___x_788_, v___x_787_, v___x_786_, v___x_785_);
    return v___x_790_;
}
pub unsafe fn l_String_Slice_getUTF8Byte_x21(
    mut v_s_791_: *mut leanh::LeanObject,
    mut v_p_792_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_str_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: u8 = 0;
    v_str_793_ = leanh::lean_ctor_get(v_s_791_, 0);
    v_startInclusive_794_ = leanh::lean_ctor_get(v_s_791_, 1);
    v_endExclusive_795_ = leanh::lean_ctor_get(v_s_791_, 2);
    v___x_796_ = lean_nat_sub(v_endExclusive_795_, v_startInclusive_794_);
    v___x_797_ = lean_nat_dec_lt(v_p_792_, v___x_796_);
    leanh::lean_dec(v___x_796_);
    if v___x_797_ == 0 {
        let mut v___x_798_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_799_: u8 = 0;
        v___x_798_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_String_Slice_getUTF8Byte_x21___closed__3),
            core::ptr::addr_of_mut!(l_String_Slice_getUTF8Byte_x21___closed__3_once),
            _init_l_String_Slice_getUTF8Byte_x21___closed__3,
        );
        v___x_799_ = l_panic___at___00String_Slice_getUTF8Byte_x21_spec__0(v___x_798_);
        return v___x_799_;
    } else {
        let mut v___x_800_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_801_: u8 = 0;
        v___x_800_ = lean_nat_add(v_startInclusive_794_, v_p_792_);
        v___x_801_ = lean_string_get_byte_fast(v_str_793_, v___x_800_);
        return v___x_801_;
    }
}
pub unsafe fn l_String_Slice_getUTF8Byte_x21___boxed(
    mut v_s_802_: *mut leanh::LeanObject,
    mut v_p_803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_804_: u8 = 0;
    let mut v_r_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_804_ = l_String_Slice_getUTF8Byte_x21(v_s_802_, v_p_803_);
    leanh::lean_dec(v_p_803_);
    leanh::lean_dec_ref(v_s_802_);
    v_r_805_ = leanh::lean_box((v_res_804_) as usize);
    return v_r_805_;
}
pub unsafe fn l_String_Slice_instDecidableEqPos_decEq___redArg(
    mut v_x_806_: *mut leanh::LeanObject,
    mut v_x_807_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_808_: u8 = 0;
    v___x_808_ = lean_nat_dec_eq(v_x_806_, v_x_807_);
    return v___x_808_;
}
pub unsafe fn l_String_Slice_instDecidableEqPos_decEq___redArg___boxed(
    mut v_x_809_: *mut leanh::LeanObject,
    mut v_x_810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_811_: u8 = 0;
    let mut v_r_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_811_ = l_String_Slice_instDecidableEqPos_decEq___redArg(v_x_809_, v_x_810_);
    leanh::lean_dec(v_x_810_);
    leanh::lean_dec(v_x_809_);
    v_r_812_ = leanh::lean_box((v_res_811_) as usize);
    return v_r_812_;
}
pub unsafe fn l_String_Slice_instDecidableEqPos_decEq(
    mut v_s_813_: *mut leanh::LeanObject,
    mut v_x_814_: *mut leanh::LeanObject,
    mut v_x_815_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_816_: u8 = 0;
    v___x_816_ = lean_nat_dec_eq(v_x_814_, v_x_815_);
    return v___x_816_;
}
pub unsafe fn l_String_Slice_instDecidableEqPos_decEq___boxed(
    mut v_s_817_: *mut leanh::LeanObject,
    mut v_x_818_: *mut leanh::LeanObject,
    mut v_x_819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_820_: u8 = 0;
    let mut v_r_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_820_ = l_String_Slice_instDecidableEqPos_decEq(v_s_817_, v_x_818_, v_x_819_);
    leanh::lean_dec(v_x_819_);
    leanh::lean_dec(v_x_818_);
    leanh::lean_dec_ref(v_s_817_);
    v_r_821_ = leanh::lean_box((v_res_820_) as usize);
    return v_r_821_;
}
pub unsafe fn l_String_Slice_instDecidableEqPos___redArg(
    mut v_x_822_: *mut leanh::LeanObject,
    mut v_x_823_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_824_: u8 = 0;
    v___x_824_ = lean_nat_dec_eq(v_x_822_, v_x_823_);
    return v___x_824_;
}
pub unsafe fn l_String_Slice_instDecidableEqPos___redArg___boxed(
    mut v_x_825_: *mut leanh::LeanObject,
    mut v_x_826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_827_: u8 = 0;
    let mut v_r_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_827_ = l_String_Slice_instDecidableEqPos___redArg(v_x_825_, v_x_826_);
    leanh::lean_dec(v_x_826_);
    leanh::lean_dec(v_x_825_);
    v_r_828_ = leanh::lean_box((v_res_827_) as usize);
    return v_r_828_;
}
pub unsafe fn l_String_Slice_instDecidableEqPos(
    mut v_s_829_: *mut leanh::LeanObject,
    mut v_x_830_: *mut leanh::LeanObject,
    mut v_x_831_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_832_: u8 = 0;
    v___x_832_ = lean_nat_dec_eq(v_x_830_, v_x_831_);
    return v___x_832_;
}
pub unsafe fn l_String_Slice_instDecidableEqPos___boxed(
    mut v_s_833_: *mut leanh::LeanObject,
    mut v_x_834_: *mut leanh::LeanObject,
    mut v_x_835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_836_: u8 = 0;
    let mut v_r_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_836_ = l_String_Slice_instDecidableEqPos(v_s_833_, v_x_834_, v_x_835_);
    leanh::lean_dec(v_x_835_);
    leanh::lean_dec(v_x_834_);
    leanh::lean_dec_ref(v_s_833_);
    v_r_837_ = leanh::lean_box((v_res_836_) as usize);
    return v_r_837_;
}
pub unsafe fn l_String_Slice_startPos(
    mut v_s_838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_839_ = leanh::lean_unsigned_to_nat(0);
    return v___x_839_;
}
pub unsafe fn l_String_Slice_startPos___boxed(
    mut v_s_840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_841_ = l_String_Slice_startPos(v_s_840_);
    leanh::lean_dec_ref(v_s_840_);
    return v_res_841_;
}
pub unsafe fn l_String_instInhabitedPos__1(
    mut v_s_842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_843_ = leanh::lean_unsigned_to_nat(0);
    return v___x_843_;
}
pub unsafe fn l_String_instInhabitedPos__1___boxed(
    mut v_s_844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_845_ = l_String_instInhabitedPos__1(v_s_844_);
    leanh::lean_dec_ref(v_s_844_);
    return v_res_845_;
}
pub unsafe fn l_String_Slice_endPos(
    mut v_s_846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startInclusive_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_847_ = leanh::lean_ctor_get(v_s_846_, 1);
    v_endExclusive_848_ = leanh::lean_ctor_get(v_s_846_, 2);
    v___x_849_ = lean_nat_sub(v_endExclusive_848_, v_startInclusive_847_);
    return v___x_849_;
}
pub unsafe fn l_String_Slice_endPos___boxed(
    mut v_s_850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_851_ = l_String_Slice_endPos(v_s_850_);
    leanh::lean_dec_ref(v_s_850_);
    return v_res_851_;
}
pub unsafe fn l_String_instLEPos__1(
    mut v_s_852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_853_ = leanh::lean_box(0);
    return v___x_853_;
}
pub unsafe fn l_String_instLEPos__1___boxed(
    mut v_s_854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_855_ = l_String_instLEPos__1(v_s_854_);
    leanh::lean_dec_ref(v_s_854_);
    return v_res_855_;
}
pub unsafe fn l_String_instLTPos__1(
    mut v_s_856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_857_ = leanh::lean_box(0);
    return v___x_857_;
}
pub unsafe fn l_String_instLTPos__1___boxed(
    mut v_s_858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_859_ = l_String_instLTPos__1(v_s_858_);
    leanh::lean_dec_ref(v_s_858_);
    return v_res_859_;
}
pub unsafe fn l_String_instDecidableLePos__1___redArg(
    mut v_l_860_: *mut leanh::LeanObject,
    mut v_r_861_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_862_: u8 = 0;
    v___x_862_ = lean_nat_dec_le(v_l_860_, v_r_861_);
    return v___x_862_;
}
pub unsafe fn l_String_instDecidableLePos__1___redArg___boxed(
    mut v_l_863_: *mut leanh::LeanObject,
    mut v_r_864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_865_: u8 = 0;
    let mut v_r_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_865_ = l_String_instDecidableLePos__1___redArg(v_l_863_, v_r_864_);
    leanh::lean_dec(v_r_864_);
    leanh::lean_dec(v_l_863_);
    v_r_866_ = leanh::lean_box((v_res_865_) as usize);
    return v_r_866_;
}
pub unsafe fn l_String_instDecidableLePos__1(
    mut v_s_867_: *mut leanh::LeanObject,
    mut v_l_868_: *mut leanh::LeanObject,
    mut v_r_869_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_870_: u8 = 0;
    v___x_870_ = lean_nat_dec_le(v_l_868_, v_r_869_);
    return v___x_870_;
}
pub unsafe fn l_String_instDecidableLePos__1___boxed(
    mut v_s_871_: *mut leanh::LeanObject,
    mut v_l_872_: *mut leanh::LeanObject,
    mut v_r_873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_874_: u8 = 0;
    let mut v_r_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_874_ = l_String_instDecidableLePos__1(v_s_871_, v_l_872_, v_r_873_);
    leanh::lean_dec(v_r_873_);
    leanh::lean_dec(v_l_872_);
    leanh::lean_dec_ref(v_s_871_);
    v_r_875_ = leanh::lean_box((v_res_874_) as usize);
    return v_r_875_;
}
pub unsafe fn l_String_instDecidableLtPos__1___redArg(
    mut v_l_876_: *mut leanh::LeanObject,
    mut v_r_877_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_878_: u8 = 0;
    v___x_878_ = lean_nat_dec_lt(v_l_876_, v_r_877_);
    return v___x_878_;
}
pub unsafe fn l_String_instDecidableLtPos__1___redArg___boxed(
    mut v_l_879_: *mut leanh::LeanObject,
    mut v_r_880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_881_: u8 = 0;
    let mut v_r_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_881_ = l_String_instDecidableLtPos__1___redArg(v_l_879_, v_r_880_);
    leanh::lean_dec(v_r_880_);
    leanh::lean_dec(v_l_879_);
    v_r_882_ = leanh::lean_box((v_res_881_) as usize);
    return v_r_882_;
}
pub unsafe fn l_String_instDecidableLtPos__1(
    mut v_s_883_: *mut leanh::LeanObject,
    mut v_l_884_: *mut leanh::LeanObject,
    mut v_r_885_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_886_: u8 = 0;
    v___x_886_ = lean_nat_dec_lt(v_l_884_, v_r_885_);
    return v___x_886_;
}
pub unsafe fn l_String_instDecidableLtPos__1___boxed(
    mut v_s_887_: *mut leanh::LeanObject,
    mut v_l_888_: *mut leanh::LeanObject,
    mut v_r_889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_890_: u8 = 0;
    let mut v_r_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_890_ = l_String_instDecidableLtPos__1(v_s_887_, v_l_888_, v_r_889_);
    leanh::lean_dec(v_r_889_);
    leanh::lean_dec(v_l_888_);
    leanh::lean_dec_ref(v_s_887_);
    v_r_891_ = leanh::lean_box((v_res_890_) as usize);
    return v_r_891_;
}
pub unsafe fn l_String_instDecidableIsAtEnd(
    mut v_s_892_: *mut leanh::LeanObject,
    mut v_pos_893_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: u8 = 0;
    v___x_894_ = lean_string_utf8_byte_size(v_s_892_);
    v___x_895_ = lean_nat_dec_eq(v_pos_893_, v___x_894_);
    return v___x_895_;
}
pub unsafe fn l_String_instDecidableIsAtEnd___boxed(
    mut v_s_896_: *mut leanh::LeanObject,
    mut v_pos_897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_898_: u8 = 0;
    let mut v_r_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_898_ = l_String_instDecidableIsAtEnd(v_s_896_, v_pos_897_);
    leanh::lean_dec(v_pos_897_);
    leanh::lean_dec_ref(v_s_896_);
    v_r_899_ = leanh::lean_box((v_res_898_) as usize);
    return v_r_899_;
}
pub unsafe fn l_String_instDecidableIsAtEnd__1(
    mut v_s_900_: *mut leanh::LeanObject,
    mut v_pos_901_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_startInclusive_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: u8 = 0;
    v_startInclusive_902_ = leanh::lean_ctor_get(v_s_900_, 1);
    v_endExclusive_903_ = leanh::lean_ctor_get(v_s_900_, 2);
    v___x_904_ = lean_nat_sub(v_endExclusive_903_, v_startInclusive_902_);
    v___x_905_ = lean_nat_dec_eq(v_pos_901_, v___x_904_);
    leanh::lean_dec(v___x_904_);
    return v___x_905_;
}
pub unsafe fn l_String_instDecidableIsAtEnd__1___boxed(
    mut v_s_906_: *mut leanh::LeanObject,
    mut v_pos_907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_908_: u8 = 0;
    let mut v_r_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_908_ = l_String_instDecidableIsAtEnd__1(v_s_906_, v_pos_907_);
    leanh::lean_dec(v_pos_907_);
    leanh::lean_dec_ref(v_s_906_);
    v_r_909_ = leanh::lean_box((v_res_908_) as usize);
    return v_r_909_;
}
pub unsafe fn l_String_Slice_Pos_byte___redArg(
    mut v_s_910_: *mut leanh::LeanObject,
    mut v_pos_911_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_str_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: u8 = 0;
    v_str_912_ = leanh::lean_ctor_get(v_s_910_, 0);
    v_startInclusive_913_ = leanh::lean_ctor_get(v_s_910_, 1);
    v___x_914_ = lean_nat_add(v_startInclusive_913_, v_pos_911_);
    v___x_915_ = lean_string_get_byte_fast(v_str_912_, v___x_914_);
    return v___x_915_;
}
pub unsafe fn l_String_Slice_Pos_byte___redArg___boxed(
    mut v_s_916_: *mut leanh::LeanObject,
    mut v_pos_917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_918_: u8 = 0;
    let mut v_r_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_918_ = l_String_Slice_Pos_byte___redArg(v_s_916_, v_pos_917_);
    leanh::lean_dec(v_pos_917_);
    leanh::lean_dec_ref(v_s_916_);
    v_r_919_ = leanh::lean_box((v_res_918_) as usize);
    return v_r_919_;
}
pub unsafe fn l_String_Slice_Pos_byte(
    mut v_s_920_: *mut leanh::LeanObject,
    mut v_pos_921_: *mut leanh::LeanObject,
    mut v_h_922_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_str_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: u8 = 0;
    v_str_923_ = leanh::lean_ctor_get(v_s_920_, 0);
    v_startInclusive_924_ = leanh::lean_ctor_get(v_s_920_, 1);
    v___x_925_ = lean_nat_add(v_startInclusive_924_, v_pos_921_);
    v___x_926_ = lean_string_get_byte_fast(v_str_923_, v___x_925_);
    return v___x_926_;
}
pub unsafe fn l_String_Slice_Pos_byte___boxed(
    mut v_s_927_: *mut leanh::LeanObject,
    mut v_pos_928_: *mut leanh::LeanObject,
    mut v_h_929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_930_: u8 = 0;
    let mut v_r_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_930_ = l_String_Slice_Pos_byte(v_s_927_, v_pos_928_, v_h_929_);
    leanh::lean_dec(v_pos_928_);
    leanh::lean_dec_ref(v_s_927_);
    v_r_931_ = leanh::lean_box((v_res_930_) as usize);
    return v_r_931_;
}
pub unsafe fn l_String_Slice_isEmpty(mut v_s_932_: *mut leanh::LeanObject) -> u8 {
    let mut v_startInclusive_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: u8 = 0;
    v_startInclusive_933_ = leanh::lean_ctor_get(v_s_932_, 1);
    v_endExclusive_934_ = leanh::lean_ctor_get(v_s_932_, 2);
    v___x_935_ = lean_nat_sub(v_endExclusive_934_, v_startInclusive_933_);
    v___x_936_ = leanh::lean_unsigned_to_nat(0);
    v___x_937_ = lean_nat_dec_eq(v___x_935_, v___x_936_);
    leanh::lean_dec(v___x_935_);
    return v___x_937_;
}
pub unsafe fn l_String_Slice_isEmpty___boxed(
    mut v_s_938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_939_: u8 = 0;
    let mut v_r_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_939_ = l_String_Slice_isEmpty(v_s_938_);
    leanh::lean_dec_ref(v_s_938_);
    v_r_940_ = leanh::lean_box((v_res_939_) as usize);
    return v_r_940_;
}
pub unsafe fn l_String_toSubstring(
    mut v_s_941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_942_ = leanh::lean_unsigned_to_nat(0);
    v___x_943_ = lean_string_utf8_byte_size(v_s_941_);
    v___x_944_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_944_, 0, v_s_941_);
    leanh::lean_ctor_set(v___x_944_, 1, v___x_942_);
    leanh::lean_ctor_set(v___x_944_, 2, v___x_943_);
    return v___x_944_;
}
pub unsafe fn l_String_toSubstring_x27(
    mut v_s_945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_946_ = l_String_toRawSubstring_x27(v_s_945_);
    return v___x_946_;
}
pub unsafe fn l_String_startValidPos(
    mut v_s_947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_948_ = leanh::lean_unsigned_to_nat(0);
    return v___x_948_;
}
pub unsafe fn l_String_startValidPos___boxed(
    mut v_s_949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_950_ = l_String_startValidPos(v_s_949_);
    leanh::lean_dec_ref(v_s_949_);
    return v_res_950_;
}
pub unsafe fn l_String_endValidPos(
    mut v_s_951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_952_ = lean_string_utf8_byte_size(v_s_951_);
    return v___x_952_;
}
pub unsafe fn l_String_endValidPos___boxed(
    mut v_s_953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_954_ = l_String_endValidPos(v_s_953_);
    leanh::lean_dec_ref(v_s_953_);
    return v_res_954_;
}
pub unsafe fn l_String_bytes(
    mut v_s_955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_956_ = lean_string_to_utf8(v_s_955_);
    return v___x_956_;
}
pub unsafe fn l_String_lengthAssumingAscii(
    mut v_s_957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_958_ = lean_string_utf8_byte_size(v_s_957_);
    return v___x_958_;
}
pub unsafe fn l_String_lengthAssumingAscii___boxed(
    mut v_s_959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_960_ = l_String_lengthAssumingAscii(v_s_959_);
    leanh::lean_dec_ref(v_s_959_);
    return v_res_960_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Defs(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_PosRaw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ByteArray_Lemmas(builtin);
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
pub unsafe fn meta_initialize_Init_Data_String_Defs(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_Defs(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_PosRaw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ByteArray_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Defs(builtin);
}
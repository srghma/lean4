// Lean compiler output
// Module: Std.Internal.Parsec.String
// Imports: Std.Internal.Parsec.Basic Init.Data.String.Slice Init.Data.String.Termination Init.Data.String.Length
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Basic::{
    l_String_Slice_Pos_get_x21, l_String_Slice_Pos_next_x21, l_String_Slice_Pos_nextn,
};
use crate::r#gen::Init::Data::String::Length::{
    initialize_Init_Data_String_Length, runtime_initialize_Init_Data_String_Length,
};
use crate::r#gen::Init::Data::String::Slice::{
    initialize_Init_Data_String_Slice, runtime_initialize_Init_Data_String_Slice,
};
use crate::r#gen::Init::Data::String::Termination::{
    initialize_Init_Data_String_Termination, runtime_initialize_Init_Data_String_Termination,
};
use crate::r#gen::Std::Internal::Parsec::Basic::{
    initialize_Std_Internal_Parsec_Basic, runtime_initialize_Std_Internal_Parsec_Basic,
};
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_extract, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Length::lean_string_length;
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_mul, lean_nat_sub,
    lean_string_utf8_byte_size, lean_uint32_dec_eq, lean_uint32_dec_le, lean_uint32_to_nat,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_box, lean_box_uint32,
    lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
    lean_unbox_uint32, lean_unsigned_to_nat,
};
pub static l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__0_value:
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
    m_fun: l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__0_value
) as *mut LeanObject;
pub static l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__1_value:
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
    m_fun: l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__1
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__1_value
) as *mut LeanObject;
pub static l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__2_value:
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
    m_fun: l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__2_value
) as *mut LeanObject;
pub static l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__3_value:
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
    m_fun: l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__3___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__3_value
) as *mut LeanObject;
pub static l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__4_value:
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
    m_fun: l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__4
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__4_value
) as *mut LeanObject;
pub static l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__5_value:
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
    m_fun: l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__5___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__5_value
) as *mut LeanObject;
pub static l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__6_value:
    LeanCtorObject<6> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 6
            + 0) as u16,
        other: 6,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__1_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__2_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__4_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__5_value
        ) as *mut LeanObject,
    ],
};
static mut l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__6_value
) as *mut LeanObject;
pub static mut l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw: *mut LeanObject = core::ptr::addr_of!(
    l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___closed__6_value
)
    as *mut LeanObject;
pub static l_Std_Internal_Parsec_String_Parser_run___redArg___closed__0_value: LeanStringObject<8> =
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
        m_data: [111, 102, 102, 115, 101, 116, 32, 0],
    };
static mut l_Std_Internal_Parsec_String_Parser_run___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_String_Parser_run___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Internal_Parsec_String_Parser_run___redArg___closed__1_value: LeanStringObject<3> =
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
        m_data: [58, 32, 0],
    };
static mut l_Std_Internal_Parsec_String_Parser_run___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_String_Parser_run___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Internal_Parsec_String_Parser_run___redArg___closed__2_value: LeanStringObject<
    24,
> = LeanStringObject {
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
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 101, 110, 100, 32, 111, 102, 32, 105,
        110, 112, 117, 116, 0,
    ],
};
static mut l_Std_Internal_Parsec_String_Parser_run___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_String_Parser_run___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Internal_Parsec_String_pstring___closed__0_value: LeanStringObject<11> =
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
        m_data: [101, 120, 112, 101, 99, 116, 101, 100, 58, 32, 0],
    };
static mut l_Std_Internal_Parsec_String_pstring___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_String_pstring___closed__0_value) as *mut LeanObject;
pub static l_Std_Internal_Parsec_String_pchar___closed__0_value: LeanStringObject<12> =
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
        m_data: [101, 120, 112, 101, 99, 116, 101, 100, 58, 32, 39, 0],
    };
static mut l_Std_Internal_Parsec_String_pchar___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_String_pchar___closed__0_value) as *mut LeanObject;
pub static l_Std_Internal_Parsec_String_pchar___closed__1_value: LeanStringObject<1> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Internal_Parsec_String_pchar___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_String_pchar___closed__1_value) as *mut LeanObject;
pub static l_Std_Internal_Parsec_String_pchar___closed__2_value: LeanStringObject<2> =
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
        m_data: [39, 0],
    };
static mut l_Std_Internal_Parsec_String_pchar___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_String_pchar___closed__2_value) as *mut LeanObject;
pub static l_Std_Internal_Parsec_String_digit___closed__0_value: LeanStringObject<15> =
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
            100, 105, 103, 105, 116, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
        ],
    };
static mut l_Std_Internal_Parsec_String_digit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_String_digit___closed__0_value) as *mut LeanObject;
pub static l_Std_Internal_Parsec_String_digit___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Internal_Parsec_String_digit___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Internal_Parsec_String_digit___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_String_digit___closed__1_value) as *mut LeanObject;
pub static l_Std_Internal_Parsec_String_hexDigit___closed__0_value: LeanStringObject<19> =
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
            104, 101, 120, 32, 100, 105, 103, 105, 116, 32, 101, 120, 112, 101, 99, 116, 101, 100,
            0,
        ],
    };
static mut l_Std_Internal_Parsec_String_hexDigit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_String_hexDigit___closed__0_value) as *mut LeanObject;
pub static l_Std_Internal_Parsec_String_hexDigit___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Internal_Parsec_String_hexDigit___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Internal_Parsec_String_hexDigit___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_String_hexDigit___closed__1_value) as *mut LeanObject;
pub static l_Std_Internal_Parsec_String_asciiLetter___closed__0_value: LeanStringObject<22> =
    LeanStringObject {
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
            65, 83, 67, 73, 73, 32, 108, 101, 116, 116, 101, 114, 32, 101, 120, 112, 101, 99, 116,
            101, 100, 0,
        ],
    };
static mut l_Std_Internal_Parsec_String_asciiLetter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_String_asciiLetter___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Internal_Parsec_String_asciiLetter___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Internal_Parsec_String_asciiLetter___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Internal_Parsec_String_asciiLetter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_Parsec_String_asciiLetter___closed__1_value)
        as *mut LeanObject;
pub unsafe fn l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__0(
    mut v_it_462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_463_: *mut LeanObject = core::ptr::null_mut();
    v_snd_463_ = lean_ctor_get(v_it_462_, 1);
    lean_inc(v_snd_463_);
    return v_snd_463_;
}
pub unsafe fn l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__0___boxed(
    mut v_it_464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_465_: *mut LeanObject = core::ptr::null_mut();
    v_res_465_ = l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__0(v_it_464_);
    lean_dec_ref(v_it_464_);
    return v_res_465_;
}
pub unsafe fn l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__1(
    mut v_it_466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_471_: u8 = 0;
    let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_479_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_467_ = lean_ctor_get(v_it_466_, 0);
                v_snd_468_ = lean_ctor_get(v_it_466_, 1);
                v_isSharedCheck_479_ = (!lean_is_exclusive(v_it_466_)) as u8;
                if v_isSharedCheck_479_ == 0 {
                    v___x_470_ = v_it_466_;
                    v_isShared_471_ = v_isSharedCheck_479_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_468_);
                    lean_inc(v_fst_467_);
                    lean_dec(v_it_466_);
                    v___x_470_ = lean_box(0);
                    v_isShared_471_ = v_isSharedCheck_479_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_472_ = lean_unsigned_to_nat(0);
                v___x_473_ = lean_string_utf8_byte_size(v_fst_467_);
                lean_inc(v_fst_467_);
                v___x_474_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_474_, 0, v_fst_467_);
                lean_ctor_set(v___x_474_, 1, v___x_472_);
                lean_ctor_set(v___x_474_, 2, v___x_473_);
                v___x_475_ = l_String_Slice_Pos_next_x21(v___x_474_, v_snd_468_);
                lean_dec(v_snd_468_);
                lean_dec_ref_known(v___x_474_, 3);
                if v_isShared_471_ == 0 {
                    lean_ctor_set(v___x_470_, 1, v___x_475_);
                    v___x_477_ = v___x_470_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_478_, 0, v_fst_467_);
                    lean_ctor_set(v_reuseFailAlloc_478_, 1, v___x_475_);
                    v___x_477_ = v_reuseFailAlloc_478_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_477_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__2(
    mut v_it_480_: *mut LeanObject,
) -> u32 {
    let mut v_fst_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_486_: u32 = 0;
    v_fst_481_ = lean_ctor_get(v_it_480_, 0);
    v_snd_482_ = lean_ctor_get(v_it_480_, 1);
    v___x_483_ = lean_unsigned_to_nat(0);
    v___x_484_ = lean_string_utf8_byte_size(v_fst_481_);
    lean_inc(v_fst_481_);
    v___x_485_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_485_, 0, v_fst_481_);
    lean_ctor_set(v___x_485_, 1, v___x_483_);
    lean_ctor_set(v___x_485_, 2, v___x_484_);
    v___x_486_ = l_String_Slice_Pos_get_x21(v___x_485_, v_snd_482_);
    lean_dec_ref_known(v___x_485_, 3);
    return v___x_486_;
}
pub unsafe fn l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__2___boxed(
    mut v_it_487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_488_: u32 = 0;
    let mut v_r_489_: *mut LeanObject = core::ptr::null_mut();
    v_res_488_ = l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__2(v_it_487_);
    lean_dec_ref(v_it_487_);
    v_r_489_ = lean_box_uint32(v_res_488_);
    return v_r_489_;
}
pub unsafe fn l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__3(
    mut v_it_490_: *mut LeanObject,
) -> u8 {
    let mut v_fst_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_494_: u8 = 0;
    v_fst_491_ = lean_ctor_get(v_it_490_, 0);
    v_snd_492_ = lean_ctor_get(v_it_490_, 1);
    v___x_493_ = lean_string_utf8_byte_size(v_fst_491_);
    v___x_494_ = lean_nat_dec_eq(v_snd_492_, v___x_493_);
    if v___x_494_ == 0 {
        let mut v___x_495_: u8 = 0;
        v___x_495_ = 1;
        return v___x_495_;
    } else {
        let mut v___x_496_: u8 = 0;
        v___x_496_ = 0;
        return v___x_496_;
    }
}
pub unsafe fn l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__3___boxed(
    mut v_it_497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_498_: u8 = 0;
    let mut v_r_499_: *mut LeanObject = core::ptr::null_mut();
    v_res_498_ = l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__3(v_it_497_);
    lean_dec_ref(v_it_497_);
    v_r_499_ = lean_box((v_res_498_) as usize);
    return v_r_499_;
}
pub unsafe fn l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__4(
    mut v_it_500_: *mut LeanObject,
    mut v_h_501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_506_: u8 = 0;
    let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_511_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_502_ = lean_ctor_get(v_it_500_, 0);
                v_snd_503_ = lean_ctor_get(v_it_500_, 1);
                v_isSharedCheck_511_ = (!lean_is_exclusive(v_it_500_)) as u8;
                if v_isSharedCheck_511_ == 0 {
                    v___x_505_ = v_it_500_;
                    v_isShared_506_ = v_isSharedCheck_511_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_503_);
                    lean_inc(v_fst_502_);
                    lean_dec(v_it_500_);
                    v___x_505_ = lean_box(0);
                    v_isShared_506_ = v_isSharedCheck_511_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_507_ = lean_string_utf8_next_fast(v_fst_502_, v_snd_503_);
                lean_dec(v_snd_503_);
                if v_isShared_506_ == 0 {
                    lean_ctor_set(v___x_505_, 1, v___x_507_);
                    v___x_509_ = v___x_505_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_510_, 0, v_fst_502_);
                    lean_ctor_set(v_reuseFailAlloc_510_, 1, v___x_507_);
                    v___x_509_ = v_reuseFailAlloc_510_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_509_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__5(
    mut v_it_512_: *mut LeanObject,
    mut v_h_513_: *mut LeanObject,
) -> u32 {
    let mut v_fst_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_516_: u32 = 0;
    v_fst_514_ = lean_ctor_get(v_it_512_, 0);
    v_snd_515_ = lean_ctor_get(v_it_512_, 1);
    v___x_516_ = lean_string_utf8_get_fast(v_fst_514_, v_snd_515_);
    return v___x_516_;
}
pub unsafe fn l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__5___boxed(
    mut v_it_517_: *mut LeanObject,
    mut v_h_518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_519_: u32 = 0;
    let mut v_r_520_: *mut LeanObject = core::ptr::null_mut();
    v_res_519_ =
        l_Std_Internal_Parsec_String_instInputSigmaStringPosCharRaw___lam__5(v_it_517_, v_h_518_);
    lean_dec_ref(v_it_517_);
    v_r_520_ = lean_box_uint32(v_res_519_);
    return v_r_520_;
}
pub unsafe fn l_Std_Internal_Parsec_String_Parser_run___redArg(
    mut v_p_538_: *mut LeanObject,
    mut v_s_539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_561_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_540_ = lean_unsigned_to_nat(0);
                v___x_541_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_541_, 0, v_s_539_);
                lean_ctor_set(v___x_541_, 1, v___x_540_);
                v___x_542_ = lean_apply_1(v_p_538_, v___x_541_);
                if lean_obj_tag(v___x_542_) == 0 {
                    v_res_543_ = lean_ctor_get(v___x_542_, 1);
                    lean_inc(v_res_543_);
                    lean_dec_ref_known(v___x_542_, 2);
                    v___x_544_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_544_, 0, v_res_543_);
                    return v___x_544_;
                } else {
                    v_pos_545_ = lean_ctor_get(v___x_542_, 0);
                    lean_inc(v_pos_545_);
                    v_err_546_ = lean_ctor_get(v___x_542_, 1);
                    lean_inc(v_err_546_);
                    lean_dec_ref_known(v___x_542_, 2);
                    v_snd_547_ = lean_ctor_get(v_pos_545_, 1);
                    lean_inc(v_snd_547_);
                    lean_dec(v_pos_545_);
                    v___x_548_ = l_Std_Internal_Parsec_String_Parser_run___redArg___closed__0;
                    v___x_549_ = l_Nat_reprFast(v_snd_547_);
                    v___x_550_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_550_, 0, v___x_549_);
                    v___x_551_ = l_Std_Format_defWidth;
                    v___x_552_ =
                        l_Std_Format_pretty(v___x_550_, v___x_551_, v___x_540_, v___x_540_);
                    v___x_553_ = lean_string_append(v___x_548_, v___x_552_);
                    lean_dec_ref(v___x_552_);
                    v___x_554_ = l_Std_Internal_Parsec_String_Parser_run___redArg___closed__1;
                    v___x_555_ = lean_string_append(v___x_553_, v___x_554_);
                    if lean_obj_tag(v_err_546_) == 0 {
                        v___x_560_ = l_Std_Internal_Parsec_String_Parser_run___redArg___closed__2;
                        v___y_557_ = v___x_560_;
                        state = 1;
                        continue;
                    } else {
                        v_s_561_ = lean_ctor_get(v_err_546_, 0);
                        lean_inc_ref(v_s_561_);
                        lean_dec_ref_known(v_err_546_, 1);
                        v___y_557_ = v_s_561_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_558_ = lean_string_append(v___x_555_, v___y_557_);
                lean_dec_ref(v___y_557_);
                v___x_559_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_559_, 0, v___x_558_);
                return v___x_559_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_String_Parser_run(
    mut v_00_u03b1_562_: *mut LeanObject,
    mut v_p_563_: *mut LeanObject,
    mut v_s_564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
    v___x_565_ = l_Std_Internal_Parsec_String_Parser_run___redArg(v_p_563_, v_s_564_);
    return v___x_565_;
}
pub unsafe fn l_Std_Internal_Parsec_String_pstring(
    mut v_s_567_: *mut LeanObject,
    mut v_it_568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_579_: u8 = 0;
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_581_: u8 = 0;
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_584_: u8 = 0;
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_592_: u8 = 0;
    let mut v_unused_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_594_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_574_ = lean_ctor_get(v_it_568_, 0);
                v_snd_575_ = lean_ctor_get(v_it_568_, 1);
                v___x_576_ = lean_string_utf8_byte_size(v_fst_574_);
                v___x_577_ = lean_string_utf8_byte_size(v_s_567_);
                v___x_578_ = lean_nat_sub(v___x_576_, v_snd_575_);
                v___x_579_ = lean_nat_dec_le(v___x_577_, v___x_578_);
                lean_dec(v___x_578_);
                if v___x_579_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_580_ = lean_unsigned_to_nat(0);
                    v___x_581_ = lean_string_memcmp(
                        v_fst_574_, v_s_567_, v_snd_575_, v___x_580_, v___x_577_,
                    );
                    if v___x_581_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_575_);
                        lean_inc(v_fst_574_);
                        v_isSharedCheck_592_ = (!lean_is_exclusive(v_it_568_)) as u8;
                        if v_isSharedCheck_592_ == 0 {
                            v_unused_593_ = lean_ctor_get(v_it_568_, 1);
                            lean_dec(v_unused_593_);
                            v_unused_594_ = lean_ctor_get(v_it_568_, 0);
                            lean_dec(v_unused_594_);
                            v___x_583_ = v_it_568_;
                            v_isShared_584_ = v_isSharedCheck_592_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v_it_568_);
                            v___x_583_ = lean_box(0);
                            v_isShared_584_ = v_isSharedCheck_592_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_570_ = l_Std_Internal_Parsec_String_pstring___closed__0;
                v___x_571_ = lean_string_append(v___x_570_, v_s_567_);
                lean_dec_ref(v_s_567_);
                v___x_572_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_572_, 0, v___x_571_);
                v___x_573_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_573_, 0, v_it_568_);
                lean_ctor_set(v___x_573_, 1, v___x_572_);
                return v___x_573_;
            }
            2 => {
                v___x_585_ = lean_string_length(v_s_567_);
                lean_inc(v_fst_574_);
                v___x_586_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_586_, 0, v_fst_574_);
                lean_ctor_set(v___x_586_, 1, v___x_580_);
                lean_ctor_set(v___x_586_, 2, v___x_576_);
                v___x_587_ = l_String_Slice_Pos_nextn(v___x_586_, v_snd_575_, v___x_585_);
                lean_dec_ref_known(v___x_586_, 3);
                if v_isShared_584_ == 0 {
                    lean_ctor_set(v___x_583_, 1, v___x_587_);
                    v___x_589_ = v___x_583_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_591_, 0, v_fst_574_);
                    lean_ctor_set(v_reuseFailAlloc_591_, 1, v___x_587_);
                    v___x_589_ = v_reuseFailAlloc_591_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_590_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_590_, 0, v___x_589_);
                lean_ctor_set(v___x_590_, 1, v_s_567_);
                return v___x_590_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_String_skipString(
    mut v_s_595_: *mut LeanObject,
    mut v_a_596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_601_: u8 = 0;
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_606_: u8 = 0;
    let mut v_unused_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_612_: u8 = 0;
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_616_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_597_ = l_Std_Internal_Parsec_String_pstring(v_s_595_, v_a_596_);
                if lean_obj_tag(v___x_597_) == 0 {
                    v_pos_598_ = lean_ctor_get(v___x_597_, 0);
                    v_isSharedCheck_606_ = (!lean_is_exclusive(v___x_597_)) as u8;
                    if v_isSharedCheck_606_ == 0 {
                        v_unused_607_ = lean_ctor_get(v___x_597_, 1);
                        lean_dec(v_unused_607_);
                        v___x_600_ = v___x_597_;
                        v_isShared_601_ = v_isSharedCheck_606_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_pos_598_);
                        lean_dec(v___x_597_);
                        v___x_600_ = lean_box(0);
                        v_isShared_601_ = v_isSharedCheck_606_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_pos_608_ = lean_ctor_get(v___x_597_, 0);
                    v_err_609_ = lean_ctor_get(v___x_597_, 1);
                    v_isSharedCheck_616_ = (!lean_is_exclusive(v___x_597_)) as u8;
                    if v_isSharedCheck_616_ == 0 {
                        v___x_611_ = v___x_597_;
                        v_isShared_612_ = v_isSharedCheck_616_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_err_609_);
                        lean_inc(v_pos_608_);
                        lean_dec(v___x_597_);
                        v___x_611_ = lean_box(0);
                        v_isShared_612_ = v_isSharedCheck_616_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_602_ = lean_box(0);
                if v_isShared_601_ == 0 {
                    lean_ctor_set(v___x_600_, 1, v___x_602_);
                    v___x_604_ = v___x_600_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_605_, 0, v_pos_598_);
                    lean_ctor_set(v_reuseFailAlloc_605_, 1, v___x_602_);
                    v___x_604_ = v_reuseFailAlloc_605_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_604_;
            }
            3 => {
                if v_isShared_612_ == 0 {
                    v___x_614_ = v___x_611_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_615_, 0, v_pos_608_);
                    lean_ctor_set(v_reuseFailAlloc_615_, 1, v_err_609_);
                    v___x_614_ = v_reuseFailAlloc_615_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_614_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_String_pchar(
    mut v_c_620_: u32,
    mut v_a_621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: u8 = 0;
    let mut v_c_626_: u32 = 0;
    let mut v___x_627_: u8 = 0;
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_638_: u8 = 0;
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_645_: u8 = 0;
    let mut v_unused_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_622_ = lean_ctor_get(v_a_621_, 0);
                v_snd_623_ = lean_ctor_get(v_a_621_, 1);
                v___x_624_ = lean_string_utf8_byte_size(v_fst_622_);
                v___x_625_ = lean_nat_dec_eq(v_snd_623_, v___x_624_);
                if v___x_625_ == 0 {
                    v_c_626_ = lean_string_utf8_get_fast(v_fst_622_, v_snd_623_);
                    v___x_627_ = lean_uint32_dec_eq(v_c_626_, v_c_620_);
                    if v___x_627_ == 0 {
                        v___x_628_ = l_Std_Internal_Parsec_String_pchar___closed__0;
                        v___x_629_ = l_Std_Internal_Parsec_String_pchar___closed__1;
                        v___x_630_ = lean_string_push(v___x_629_, v_c_620_);
                        v___x_631_ = lean_string_append(v___x_628_, v___x_630_);
                        lean_dec_ref(v___x_630_);
                        v___x_632_ = l_Std_Internal_Parsec_String_pchar___closed__2;
                        v___x_633_ = lean_string_append(v___x_631_, v___x_632_);
                        v___x_634_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_634_, 0, v___x_633_);
                        v___x_635_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_635_, 0, v_a_621_);
                        lean_ctor_set(v___x_635_, 1, v___x_634_);
                        return v___x_635_;
                    } else {
                        lean_inc(v_snd_623_);
                        lean_inc(v_fst_622_);
                        v_isSharedCheck_645_ = (!lean_is_exclusive(v_a_621_)) as u8;
                        if v_isSharedCheck_645_ == 0 {
                            v_unused_646_ = lean_ctor_get(v_a_621_, 1);
                            lean_dec(v_unused_646_);
                            v_unused_647_ = lean_ctor_get(v_a_621_, 0);
                            lean_dec(v_unused_647_);
                            v___x_637_ = v_a_621_;
                            v_isShared_638_ = v_isSharedCheck_645_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_621_);
                            v___x_637_ = lean_box(0);
                            v_isShared_638_ = v_isSharedCheck_645_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_648_ = lean_box(0);
                    v___x_649_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_649_, 0, v_a_621_);
                    lean_ctor_set(v___x_649_, 1, v___x_648_);
                    return v___x_649_;
                }
            }
            1 => {
                v___x_639_ = lean_string_utf8_next_fast(v_fst_622_, v_snd_623_);
                lean_dec(v_snd_623_);
                if v_isShared_638_ == 0 {
                    lean_ctor_set(v___x_637_, 1, v___x_639_);
                    v_it_x27_641_ = v___x_637_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_644_, 0, v_fst_622_);
                    lean_ctor_set(v_reuseFailAlloc_644_, 1, v___x_639_);
                    v_it_x27_641_ = v_reuseFailAlloc_644_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_642_ = lean_box_uint32(v_c_620_);
                v___x_643_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_643_, 0, v_it_x27_641_);
                lean_ctor_set(v___x_643_, 1, v___x_642_);
                return v___x_643_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_String_pchar___boxed(
    mut v_c_650_: *mut LeanObject,
    mut v_a_651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_652_: u32 = 0;
    let mut v_res_653_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_652_ = lean_unbox_uint32(v_c_650_);
    lean_dec(v_c_650_);
    v_res_653_ = l_Std_Internal_Parsec_String_pchar(v_c_boxed_652_, v_a_651_);
    return v_res_653_;
}
pub unsafe fn l_Std_Internal_Parsec_String_skipChar(
    mut v_c_654_: u32,
    mut v_a_655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: u8 = 0;
    let mut v_c_660_: u32 = 0;
    let mut v___x_661_: u8 = 0;
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_672_: u8 = 0;
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_679_: u8 = 0;
    let mut v_unused_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_656_ = lean_ctor_get(v_a_655_, 0);
                v_snd_657_ = lean_ctor_get(v_a_655_, 1);
                v___x_658_ = lean_string_utf8_byte_size(v_fst_656_);
                v___x_659_ = lean_nat_dec_eq(v_snd_657_, v___x_658_);
                if v___x_659_ == 0 {
                    v_c_660_ = lean_string_utf8_get_fast(v_fst_656_, v_snd_657_);
                    v___x_661_ = lean_uint32_dec_eq(v_c_660_, v_c_654_);
                    if v___x_661_ == 0 {
                        v___x_662_ = l_Std_Internal_Parsec_String_pchar___closed__0;
                        v___x_663_ = l_Std_Internal_Parsec_String_pchar___closed__1;
                        v___x_664_ = lean_string_push(v___x_663_, v_c_654_);
                        v___x_665_ = lean_string_append(v___x_662_, v___x_664_);
                        lean_dec_ref(v___x_664_);
                        v___x_666_ = l_Std_Internal_Parsec_String_pchar___closed__2;
                        v___x_667_ = lean_string_append(v___x_665_, v___x_666_);
                        v___x_668_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_668_, 0, v___x_667_);
                        v___x_669_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_669_, 0, v_a_655_);
                        lean_ctor_set(v___x_669_, 1, v___x_668_);
                        return v___x_669_;
                    } else {
                        lean_inc(v_snd_657_);
                        lean_inc(v_fst_656_);
                        v_isSharedCheck_679_ = (!lean_is_exclusive(v_a_655_)) as u8;
                        if v_isSharedCheck_679_ == 0 {
                            v_unused_680_ = lean_ctor_get(v_a_655_, 1);
                            lean_dec(v_unused_680_);
                            v_unused_681_ = lean_ctor_get(v_a_655_, 0);
                            lean_dec(v_unused_681_);
                            v___x_671_ = v_a_655_;
                            v_isShared_672_ = v_isSharedCheck_679_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_655_);
                            v___x_671_ = lean_box(0);
                            v_isShared_672_ = v_isSharedCheck_679_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_682_ = lean_box(0);
                    v___x_683_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_683_, 0, v_a_655_);
                    lean_ctor_set(v___x_683_, 1, v___x_682_);
                    return v___x_683_;
                }
            }
            1 => {
                v___x_673_ = lean_string_utf8_next_fast(v_fst_656_, v_snd_657_);
                lean_dec(v_snd_657_);
                if v_isShared_672_ == 0 {
                    lean_ctor_set(v___x_671_, 1, v___x_673_);
                    v_it_x27_675_ = v___x_671_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_678_, 0, v_fst_656_);
                    lean_ctor_set(v_reuseFailAlloc_678_, 1, v___x_673_);
                    v_it_x27_675_ = v_reuseFailAlloc_678_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_676_ = lean_box(0);
                v___x_677_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_677_, 0, v_it_x27_675_);
                lean_ctor_set(v___x_677_, 1, v___x_676_);
                return v___x_677_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_String_skipChar___boxed(
    mut v_c_684_: *mut LeanObject,
    mut v_a_685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_686_: u32 = 0;
    let mut v_res_687_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_686_ = lean_unbox_uint32(v_c_684_);
    lean_dec(v_c_684_);
    v_res_687_ = l_Std_Internal_Parsec_String_skipChar(v_c_boxed_686_, v_a_685_);
    return v_res_687_;
}
pub unsafe fn l_Std_Internal_Parsec_String_digit(mut v_a_691_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: u8 = 0;
    let mut v_c_699_: u32 = 0;
    let mut v___x_700_: u32 = 0;
    let mut v___x_701_: u8 = 0;
    let mut v___x_702_: u32 = 0;
    let mut v___x_703_: u8 = 0;
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_706_: u8 = 0;
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_713_: u8 = 0;
    let mut v_unused_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_695_ = lean_ctor_get(v_a_691_, 0);
                v_snd_696_ = lean_ctor_get(v_a_691_, 1);
                v___x_697_ = lean_string_utf8_byte_size(v_fst_695_);
                v___x_698_ = lean_nat_dec_eq(v_snd_696_, v___x_697_);
                if v___x_698_ == 0 {
                    v_c_699_ = lean_string_utf8_get_fast(v_fst_695_, v_snd_696_);
                    v___x_700_ = 48;
                    v___x_701_ = lean_uint32_dec_le(v___x_700_, v_c_699_);
                    if v___x_701_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_702_ = 57;
                        v___x_703_ = lean_uint32_dec_le(v_c_699_, v___x_702_);
                        if v___x_703_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_snd_696_);
                            lean_inc(v_fst_695_);
                            v_isSharedCheck_713_ = (!lean_is_exclusive(v_a_691_)) as u8;
                            if v_isSharedCheck_713_ == 0 {
                                v_unused_714_ = lean_ctor_get(v_a_691_, 1);
                                lean_dec(v_unused_714_);
                                v_unused_715_ = lean_ctor_get(v_a_691_, 0);
                                lean_dec(v_unused_715_);
                                v___x_705_ = v_a_691_;
                                v_isShared_706_ = v_isSharedCheck_713_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v_a_691_);
                                v___x_705_ = lean_box(0);
                                v_isShared_706_ = v_isSharedCheck_713_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_716_ = lean_box(0);
                    v___x_717_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_717_, 0, v_a_691_);
                    lean_ctor_set(v___x_717_, 1, v___x_716_);
                    return v___x_717_;
                }
            }
            1 => {
                v___x_693_ = l_Std_Internal_Parsec_String_digit___closed__1;
                v___x_694_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_694_, 0, v_a_691_);
                lean_ctor_set(v___x_694_, 1, v___x_693_);
                return v___x_694_;
            }
            2 => {
                v___x_707_ = lean_string_utf8_next_fast(v_fst_695_, v_snd_696_);
                lean_dec(v_snd_696_);
                if v_isShared_706_ == 0 {
                    lean_ctor_set(v___x_705_, 1, v___x_707_);
                    v_it_x27_709_ = v___x_705_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_712_, 0, v_fst_695_);
                    lean_ctor_set(v_reuseFailAlloc_712_, 1, v___x_707_);
                    v_it_x27_709_ = v_reuseFailAlloc_712_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_710_ = lean_box_uint32(v_c_699_);
                v___x_711_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_711_, 0, v_it_x27_709_);
                lean_ctor_set(v___x_711_, 1, v___x_710_);
                return v___x_711_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat(
    mut v_b_718_: u32,
) -> *mut LeanObject {
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    v___x_719_ = lean_uint32_to_nat(v_b_718_);
    v___x_720_ = lean_unsigned_to_nat(48);
    v___x_721_ = lean_nat_sub(v___x_719_, v___x_720_);
    lean_dec(v___x_719_);
    return v___x_721_;
}
pub unsafe fn l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat___boxed(
    mut v_b_722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_boxed_723_: u32 = 0;
    let mut v_res_724_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_723_ = lean_unbox_uint32(v_b_722_);
    lean_dec(v_b_722_);
    v_res_724_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat(
        v_b_boxed_723_,
    );
    return v_res_724_;
}
pub unsafe fn l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(
    mut v_s_725_: *mut LeanObject,
    mut v_it_726_: *mut LeanObject,
    mut v_acc_727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_729_: u8 = 0;
    let mut v_candidate_730_: u32 = 0;
    let mut v___x_731_: u32 = 0;
    let mut v___x_732_: u8 = 0;
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: u32 = 0;
    let mut v___x_735_: u8 = 0;
    let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_digit_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_acc_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_728_ = lean_string_utf8_byte_size(v_s_725_);
                v___x_729_ = lean_nat_dec_eq(v_it_726_, v___x_728_);
                if v___x_729_ == 0 {
                    v_candidate_730_ = lean_string_utf8_get_fast(v_s_725_, v_it_726_);
                    v___x_731_ = 48;
                    v___x_732_ = lean_uint32_dec_le(v___x_731_, v_candidate_730_);
                    if v___x_732_ == 0 {
                        v___x_733_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_733_, 0, v_acc_727_);
                        lean_ctor_set(v___x_733_, 1, v_it_726_);
                        return v___x_733_;
                    } else {
                        v___x_734_ = 57;
                        v___x_735_ = lean_uint32_dec_le(v_candidate_730_, v___x_734_);
                        if v___x_735_ == 0 {
                            v___x_736_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_736_, 0, v_acc_727_);
                            lean_ctor_set(v___x_736_, 1, v_it_726_);
                            return v___x_736_;
                        } else {
                            v___x_737_ = lean_uint32_to_nat(v_candidate_730_);
                            v___x_738_ = lean_unsigned_to_nat(48);
                            v_digit_739_ = lean_nat_sub(v___x_737_, v___x_738_);
                            lean_dec(v___x_737_);
                            v___x_740_ = lean_unsigned_to_nat(10);
                            v___x_741_ = lean_nat_mul(v_acc_727_, v___x_740_);
                            lean_dec(v_acc_727_);
                            v_acc_742_ = lean_nat_add(v___x_741_, v_digit_739_);
                            lean_dec(v_digit_739_);
                            lean_dec(v___x_741_);
                            v___x_743_ = lean_string_utf8_next_fast(v_s_725_, v_it_726_);
                            lean_dec(v_it_726_);
                            v_it_726_ = v___x_743_;
                            v_acc_727_ = v_acc_742_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_745_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_745_, 0, v_acc_727_);
                    lean_ctor_set(v___x_745_, 1, v_it_726_);
                    return v___x_745_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go___boxed(
    mut v_s_746_: *mut LeanObject,
    mut v_it_747_: *mut LeanObject,
    mut v_acc_748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_749_: *mut LeanObject = core::ptr::null_mut();
    v_res_749_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(
        v_s_746_, v_it_747_, v_acc_748_,
    );
    lean_dec_ref(v_s_746_);
    return v_res_749_;
}
pub unsafe fn l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore(
    mut v_acc_750_: *mut LeanObject,
    mut v_it_751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_756_: u8 = 0;
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_762_: u8 = 0;
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_769_: u8 = 0;
    let mut v_isSharedCheck_770_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_752_ = lean_ctor_get(v_it_751_, 0);
                v_snd_753_ = lean_ctor_get(v_it_751_, 1);
                v_isSharedCheck_770_ = (!lean_is_exclusive(v_it_751_)) as u8;
                if v_isSharedCheck_770_ == 0 {
                    v___x_755_ = v_it_751_;
                    v_isShared_756_ = v_isSharedCheck_770_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_753_);
                    lean_inc(v_fst_752_);
                    lean_dec(v_it_751_);
                    v___x_755_ = lean_box(0);
                    v_isShared_756_ = v_isSharedCheck_770_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_757_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_fst_752_, v_snd_753_, v_acc_750_);
                v_fst_758_ = lean_ctor_get(v___x_757_, 0);
                v_snd_759_ = lean_ctor_get(v___x_757_, 1);
                v_isSharedCheck_769_ = (!lean_is_exclusive(v___x_757_)) as u8;
                if v_isSharedCheck_769_ == 0 {
                    v___x_761_ = v___x_757_;
                    v_isShared_762_ = v_isSharedCheck_769_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_759_);
                    lean_inc(v_fst_758_);
                    lean_dec(v___x_757_);
                    v___x_761_ = lean_box(0);
                    v_isShared_762_ = v_isSharedCheck_769_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_756_ == 0 {
                    lean_ctor_set(v___x_755_, 1, v_snd_759_);
                    v___x_764_ = v___x_755_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_768_, 0, v_fst_752_);
                    lean_ctor_set(v_reuseFailAlloc_768_, 1, v_snd_759_);
                    v___x_764_ = v_reuseFailAlloc_768_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_762_ == 0 {
                    lean_ctor_set(v___x_761_, 1, v_fst_758_);
                    lean_ctor_set(v___x_761_, 0, v___x_764_);
                    v___x_766_ = v___x_761_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_764_);
                    lean_ctor_set(v_reuseFailAlloc_767_, 1, v_fst_758_);
                    v___x_766_ = v_reuseFailAlloc_767_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_766_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_String_digits(
    mut v_a_771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_778_: u8 = 0;
    let mut v_c_779_: u32 = 0;
    let mut v___x_780_: u32 = 0;
    let mut v___x_781_: u8 = 0;
    let mut v___x_782_: u32 = 0;
    let mut v___x_783_: u8 = 0;
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_786_: u8 = 0;
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_796_: u8 = 0;
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_803_: u8 = 0;
    let mut v_isSharedCheck_804_: u8 = 0;
    let mut v_unused_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_775_ = lean_ctor_get(v_a_771_, 0);
                v_snd_776_ = lean_ctor_get(v_a_771_, 1);
                v___x_777_ = lean_string_utf8_byte_size(v_fst_775_);
                v___x_778_ = lean_nat_dec_eq(v_snd_776_, v___x_777_);
                if v___x_778_ == 0 {
                    v_c_779_ = lean_string_utf8_get_fast(v_fst_775_, v_snd_776_);
                    v___x_780_ = 48;
                    v___x_781_ = lean_uint32_dec_le(v___x_780_, v_c_779_);
                    if v___x_781_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_782_ = 57;
                        v___x_783_ = lean_uint32_dec_le(v_c_779_, v___x_782_);
                        if v___x_783_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_snd_776_);
                            lean_inc(v_fst_775_);
                            v_isSharedCheck_804_ = (!lean_is_exclusive(v_a_771_)) as u8;
                            if v_isSharedCheck_804_ == 0 {
                                v_unused_805_ = lean_ctor_get(v_a_771_, 1);
                                lean_dec(v_unused_805_);
                                v_unused_806_ = lean_ctor_get(v_a_771_, 0);
                                lean_dec(v_unused_806_);
                                v___x_785_ = v_a_771_;
                                v_isShared_786_ = v_isSharedCheck_804_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v_a_771_);
                                v___x_785_ = lean_box(0);
                                v_isShared_786_ = v_isSharedCheck_804_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_807_ = lean_box(0);
                    v___x_808_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_808_, 0, v_a_771_);
                    lean_ctor_set(v___x_808_, 1, v___x_807_);
                    return v___x_808_;
                }
            }
            1 => {
                v___x_773_ = l_Std_Internal_Parsec_String_digit___closed__1;
                v___x_774_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_774_, 0, v_a_771_);
                lean_ctor_set(v___x_774_, 1, v___x_773_);
                return v___x_774_;
            }
            2 => {
                v___x_787_ = lean_string_utf8_next_fast(v_fst_775_, v_snd_776_);
                lean_dec(v_snd_776_);
                v___x_788_ = lean_uint32_to_nat(v_c_779_);
                v___x_789_ = lean_unsigned_to_nat(48);
                v___x_790_ = lean_nat_sub(v___x_788_, v___x_789_);
                lean_dec(v___x_788_);
                v___x_791_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(v_fst_775_, v___x_787_, v___x_790_);
                v_fst_792_ = lean_ctor_get(v___x_791_, 0);
                v_snd_793_ = lean_ctor_get(v___x_791_, 1);
                v_isSharedCheck_803_ = (!lean_is_exclusive(v___x_791_)) as u8;
                if v_isSharedCheck_803_ == 0 {
                    v___x_795_ = v___x_791_;
                    v_isShared_796_ = v_isSharedCheck_803_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_793_);
                    lean_inc(v_fst_792_);
                    lean_dec(v___x_791_);
                    v___x_795_ = lean_box(0);
                    v_isShared_796_ = v_isSharedCheck_803_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_786_ == 0 {
                    lean_ctor_set(v___x_785_, 1, v_snd_793_);
                    v___x_798_ = v___x_785_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_802_, 0, v_fst_775_);
                    lean_ctor_set(v_reuseFailAlloc_802_, 1, v_snd_793_);
                    v___x_798_ = v_reuseFailAlloc_802_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_796_ == 0 {
                    lean_ctor_set(v___x_795_, 1, v_fst_792_);
                    lean_ctor_set(v___x_795_, 0, v___x_798_);
                    v___x_800_ = v___x_795_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_798_);
                    lean_ctor_set(v_reuseFailAlloc_801_, 1, v_fst_792_);
                    v___x_800_ = v_reuseFailAlloc_801_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_800_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_String_hexDigit(
    mut v_a_812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_819_: u8 = 0;
    let mut v_c_820_: u32 = 0;
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: u32 = 0;
    let mut v___x_827_: u8 = 0;
    let mut v___x_828_: u32 = 0;
    let mut v___x_829_: u8 = 0;
    let mut v___x_831_: u32 = 0;
    let mut v___x_832_: u8 = 0;
    let mut v___x_833_: u32 = 0;
    let mut v___x_834_: u8 = 0;
    let mut v___x_835_: u32 = 0;
    let mut v___x_836_: u8 = 0;
    let mut v___x_837_: u32 = 0;
    let mut v___x_838_: u8 = 0;
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_816_ = lean_ctor_get(v_a_812_, 0);
                v_snd_817_ = lean_ctor_get(v_a_812_, 1);
                v___x_818_ = lean_string_utf8_byte_size(v_fst_816_);
                v___x_819_ = lean_nat_dec_eq(v_snd_817_, v___x_818_);
                if v___x_819_ == 0 {
                    v_c_820_ = lean_string_utf8_get_fast(v_fst_816_, v_snd_817_);
                    v___x_821_ = lean_string_utf8_next_fast(v_fst_816_, v_snd_817_);
                    lean_inc(v_fst_816_);
                    v_it_x27_822_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_it_x27_822_, 0, v_fst_816_);
                    lean_ctor_set(v_it_x27_822_, 1, v___x_821_);
                    v___x_823_ = lean_box_uint32(v_c_820_);
                    v___x_824_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_824_, 0, v_it_x27_822_);
                    lean_ctor_set(v___x_824_, 1, v___x_823_);
                    v___x_835_ = 48;
                    v___x_836_ = lean_uint32_dec_le(v___x_835_, v_c_820_);
                    if v___x_836_ == 0 {
                        state = 3;
                        continue;
                    } else {
                        v___x_837_ = 57;
                        v___x_838_ = lean_uint32_dec_le(v_c_820_, v___x_837_);
                        if v___x_838_ == 0 {
                            state = 3;
                            continue;
                        } else {
                            lean_dec_ref(v_a_812_);
                            return v___x_824_;
                        }
                    }
                } else {
                    v___x_839_ = lean_box(0);
                    v___x_840_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_840_, 0, v_a_812_);
                    lean_ctor_set(v___x_840_, 1, v___x_839_);
                    return v___x_840_;
                }
            }
            1 => {
                v___x_814_ = l_Std_Internal_Parsec_String_hexDigit___closed__1;
                v___x_815_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_815_, 0, v_a_812_);
                lean_ctor_set(v___x_815_, 1, v___x_814_);
                return v___x_815_;
            }
            2 => {
                v___x_826_ = 65;
                v___x_827_ = lean_uint32_dec_le(v___x_826_, v_c_820_);
                if v___x_827_ == 0 {
                    lean_dec_ref_known(v___x_824_, 2);
                    state = 1;
                    continue;
                } else {
                    v___x_828_ = 70;
                    v___x_829_ = lean_uint32_dec_le(v_c_820_, v___x_828_);
                    if v___x_829_ == 0 {
                        lean_dec_ref_known(v___x_824_, 2);
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_a_812_);
                        return v___x_824_;
                    }
                }
            }
            3 => {
                v___x_831_ = 97;
                v___x_832_ = lean_uint32_dec_le(v___x_831_, v_c_820_);
                if v___x_832_ == 0 {
                    state = 2;
                    continue;
                } else {
                    v___x_833_ = 102;
                    v___x_834_ = lean_uint32_dec_le(v_c_820_, v___x_833_);
                    if v___x_834_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        lean_dec_ref(v_a_812_);
                        return v___x_824_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_String_asciiLetter(
    mut v_a_844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_851_: u8 = 0;
    let mut v_c_852_: u32 = 0;
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_x27_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: u32 = 0;
    let mut v___x_859_: u8 = 0;
    let mut v___x_860_: u32 = 0;
    let mut v___x_861_: u8 = 0;
    let mut v___x_862_: u32 = 0;
    let mut v___x_863_: u8 = 0;
    let mut v___x_864_: u32 = 0;
    let mut v___x_865_: u8 = 0;
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_848_ = lean_ctor_get(v_a_844_, 0);
                v_snd_849_ = lean_ctor_get(v_a_844_, 1);
                v___x_850_ = lean_string_utf8_byte_size(v_fst_848_);
                v___x_851_ = lean_nat_dec_eq(v_snd_849_, v___x_850_);
                if v___x_851_ == 0 {
                    v_c_852_ = lean_string_utf8_get_fast(v_fst_848_, v_snd_849_);
                    v___x_853_ = lean_string_utf8_next_fast(v_fst_848_, v_snd_849_);
                    lean_inc(v_fst_848_);
                    v_it_x27_854_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_it_x27_854_, 0, v_fst_848_);
                    lean_ctor_set(v_it_x27_854_, 1, v___x_853_);
                    v___x_855_ = lean_box_uint32(v_c_852_);
                    v___x_856_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_856_, 0, v_it_x27_854_);
                    lean_ctor_set(v___x_856_, 1, v___x_855_);
                    v___x_862_ = 65;
                    v___x_863_ = lean_uint32_dec_le(v___x_862_, v_c_852_);
                    if v___x_863_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        v___x_864_ = 90;
                        v___x_865_ = lean_uint32_dec_le(v_c_852_, v___x_864_);
                        if v___x_865_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            lean_dec_ref(v_a_844_);
                            return v___x_856_;
                        }
                    }
                } else {
                    v___x_866_ = lean_box(0);
                    v___x_867_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_867_, 0, v_a_844_);
                    lean_ctor_set(v___x_867_, 1, v___x_866_);
                    return v___x_867_;
                }
            }
            1 => {
                v___x_846_ = l_Std_Internal_Parsec_String_asciiLetter___closed__1;
                v___x_847_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_847_, 0, v_a_844_);
                lean_ctor_set(v___x_847_, 1, v___x_846_);
                return v___x_847_;
            }
            2 => {
                v___x_858_ = 97;
                v___x_859_ = lean_uint32_dec_le(v___x_858_, v_c_852_);
                if v___x_859_ == 0 {
                    lean_dec_ref_known(v___x_856_, 2);
                    state = 1;
                    continue;
                } else {
                    v___x_860_ = 122;
                    v___x_861_ = lean_uint32_dec_le(v_c_852_, v___x_860_);
                    if v___x_861_ == 0 {
                        lean_dec_ref_known(v___x_856_, 2);
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_a_844_);
                        return v___x_856_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(
    mut v_s_868_: *mut LeanObject,
    mut v_it_869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_874_: u8 = 0;
    let mut v_c_875_: u32 = 0;
    let mut v___x_876_: u32 = 0;
    let mut v___x_877_: u8 = 0;
    let mut v___x_878_: u32 = 0;
    let mut v___x_879_: u8 = 0;
    let mut v___x_880_: u32 = 0;
    let mut v___x_881_: u8 = 0;
    let mut v___x_882_: u32 = 0;
    let mut v___x_883_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_873_ = lean_string_utf8_byte_size(v_s_868_);
                v___x_874_ = lean_nat_dec_eq(v_it_869_, v___x_873_);
                if v___x_874_ == 0 {
                    v_c_875_ = lean_string_utf8_get_fast(v_s_868_, v_it_869_);
                    v___x_876_ = 9;
                    v___x_877_ = lean_uint32_dec_eq(v_c_875_, v___x_876_);
                    if v___x_877_ == 0 {
                        v___x_878_ = 10;
                        v___x_879_ = lean_uint32_dec_eq(v_c_875_, v___x_878_);
                        if v___x_879_ == 0 {
                            v___x_880_ = 13;
                            v___x_881_ = lean_uint32_dec_eq(v_c_875_, v___x_880_);
                            if v___x_881_ == 0 {
                                v___x_882_ = 32;
                                v___x_883_ = lean_uint32_dec_eq(v_c_875_, v___x_882_);
                                if v___x_883_ == 0 {
                                    return v_it_869_;
                                } else {
                                    state = 1;
                                    continue;
                                }
                            } else {
                                state = 1;
                                continue;
                            }
                        } else {
                            state = 1;
                            continue;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    return v_it_869_;
                }
            }
            1 => {
                v___x_871_ = lean_string_utf8_next_fast(v_s_868_, v_it_869_);
                lean_dec(v_it_869_);
                v_it_869_ = v___x_871_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs___boxed(
    mut v_s_884_: *mut LeanObject,
    mut v_it_885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_886_: *mut LeanObject = core::ptr::null_mut();
    v_res_886_ = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(
        v_s_884_, v_it_885_,
    );
    lean_dec_ref(v_s_884_);
    return v_res_886_;
}
pub unsafe fn l_Std_Internal_Parsec_String_ws(mut v_it_887_: *mut LeanObject) -> *mut LeanObject {
    let mut v_fst_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_892_: u8 = 0;
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_899_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_888_ = lean_ctor_get(v_it_887_, 0);
                v_snd_889_ = lean_ctor_get(v_it_887_, 1);
                v_isSharedCheck_899_ = (!lean_is_exclusive(v_it_887_)) as u8;
                if v_isSharedCheck_899_ == 0 {
                    v___x_891_ = v_it_887_;
                    v_isShared_892_ = v_isSharedCheck_899_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_889_);
                    lean_inc(v_fst_888_);
                    lean_dec(v_it_887_);
                    v___x_891_ = lean_box(0);
                    v_isShared_892_ = v_isSharedCheck_899_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_893_ =
                    l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(
                        v_fst_888_, v_snd_889_,
                    );
                if v_isShared_892_ == 0 {
                    lean_ctor_set(v___x_891_, 1, v___x_893_);
                    v___x_895_ = v___x_891_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_898_, 0, v_fst_888_);
                    lean_ctor_set(v_reuseFailAlloc_898_, 1, v___x_893_);
                    v___x_895_ = v_reuseFailAlloc_898_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_896_ = lean_box(0);
                v___x_897_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_897_, 0, v___x_895_);
                lean_ctor_set(v___x_897_, 1, v___x_896_);
                return v___x_897_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Internal_Parsec_String_take(
    mut v_n_900_: *mut LeanObject,
    mut v_it_901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_right_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_substr_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_910_: u8 = 0;
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_915_: u8 = 0;
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_920_: u8 = 0;
    let mut v_unused_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_922_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_902_ = lean_ctor_get(v_it_901_, 0);
                v_snd_903_ = lean_ctor_get(v_it_901_, 1);
                v___x_904_ = lean_unsigned_to_nat(0);
                v___x_905_ = lean_string_utf8_byte_size(v_fst_902_);
                lean_inc(v_fst_902_);
                v___x_906_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_906_, 0, v_fst_902_);
                lean_ctor_set(v___x_906_, 1, v___x_904_);
                lean_ctor_set(v___x_906_, 2, v___x_905_);
                lean_inc(v_n_900_);
                lean_inc(v_snd_903_);
                v_right_907_ = l_String_Slice_Pos_nextn(v___x_906_, v_snd_903_, v_n_900_);
                lean_dec_ref_known(v___x_906_, 3);
                v_substr_908_ = lean_string_utf8_extract(v_fst_902_, v_snd_903_, v_right_907_);
                v___x_909_ = lean_string_length(v_substr_908_);
                v___x_910_ = lean_nat_dec_eq(v___x_909_, v_n_900_);
                lean_dec(v_n_900_);
                if v___x_910_ == 0 {
                    lean_dec_ref(v_substr_908_);
                    lean_dec(v_right_907_);
                    v___x_911_ = lean_box(0);
                    v___x_912_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_912_, 0, v_it_901_);
                    lean_ctor_set(v___x_912_, 1, v___x_911_);
                    return v___x_912_;
                } else {
                    lean_inc(v_fst_902_);
                    v_isSharedCheck_920_ = (!lean_is_exclusive(v_it_901_)) as u8;
                    if v_isSharedCheck_920_ == 0 {
                        v_unused_921_ = lean_ctor_get(v_it_901_, 1);
                        lean_dec(v_unused_921_);
                        v_unused_922_ = lean_ctor_get(v_it_901_, 0);
                        lean_dec(v_unused_922_);
                        v___x_914_ = v_it_901_;
                        v_isShared_915_ = v_isSharedCheck_920_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_it_901_);
                        v___x_914_ = lean_box(0);
                        v_isShared_915_ = v_isSharedCheck_920_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_915_ == 0 {
                    lean_ctor_set(v___x_914_, 1, v_right_907_);
                    v___x_917_ = v___x_914_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_919_, 0, v_fst_902_);
                    lean_ctor_set(v_reuseFailAlloc_919_, 1, v_right_907_);
                    v___x_917_ = v_reuseFailAlloc_919_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_918_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_918_, 0, v___x_917_);
                lean_ctor_set(v___x_918_, 1, v_substr_908_);
                return v___x_918_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_Parsec_String(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Internal_Parsec_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Termination(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Length(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_Parsec_String(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Internal_Parsec_String(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Internal_Parsec_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Termination(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Length(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Parsec_String(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Internal_Parsec_String(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Internal_Parsec_String(builtin);
}

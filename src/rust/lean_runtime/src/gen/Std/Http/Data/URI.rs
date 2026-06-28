// Lean compiler output
// Module: Std.Http.Data.URI
// Imports: Std.Http.Data.URI.Basic Std.Http.Data.URI.Parser
use crate::r#gen::Init::Prelude::l_panic___redArg;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Std::Http::Data::URI::Basic::{
    initialize_Std_Http_Data_URI_Basic, l_Std_Http_instInhabitedRequestTarget_default,
    l_Std_Http_instInhabitedURI_default, runtime_initialize_Std_Http_Data_URI_Basic,
};
use crate::r#gen::Std::Http::Data::URI::Parser::{
    initialize_Std_Http_Data_URI_Parser, l_Std_Http_URI_Parser_parsePath,
    l_Std_Http_URI_Parser_parseRequestTarget, l_Std_Http_URI_Parser_parseURI,
    runtime_initialize_Std_Http_Data_URI_Parser,
};
use crate::r#gen::Std::Internal::Parsec::ByteArray::l_Std_Internal_Parsec_ByteArray_Parser_run___redArg;
use crate::lean_imports_rs::Init::Data::String::Defs::{lean_string_append, lean_string_to_utf8};
use crate::lean_imports_rs::Init::Prelude::{
    lean_byte_array_size, lean_mk_empty_array_with_capacity, lean_nat_dec_lt,
};
pub static l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject {
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
        101, 120, 112, 101, 99, 116, 101, 100, 32, 101, 110, 100, 32, 111, 102, 32, 105, 110, 112,
        117, 116, 0,
    ],
};
static mut l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_RequestTarget_parse_x3f___closed__0_value: crate::leanh::LeanCtorObject<9> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9
                + 0) as u16,
            other: 9,
            tag: 0,
        },
        m_objs: [
            (((13 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((253 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((256 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((8192 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((128 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((8192 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((100 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_RequestTarget_parse_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_RequestTarget_parse_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_RequestTarget_parse_x3f___closed__1_value: crate::leanh::LeanClosureObject<
    1,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_RequestTarget_parse_x3f___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_RequestTarget_parse_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_RequestTarget_parse_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_RequestTarget_parse_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_RequestTarget_parse_x21___closed__0_value: crate::leanh::LeanStringObject<
    18,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 68, 97, 116, 97, 46, 85, 82, 73, 0,
    ],
};
static mut l_Std_Http_RequestTarget_parse_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_RequestTarget_parse_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_RequestTarget_parse_x21___closed__1_value: crate::leanh::LeanStringObject<
    30,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 82, 101, 113, 117, 101, 115, 116, 84, 97, 114,
        103, 101, 116, 46, 112, 97, 114, 115, 101, 33, 0,
    ],
};
static mut l_Std_Http_RequestTarget_parse_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_RequestTarget_parse_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_RequestTarget_parse_x21___closed__2_value: crate::leanh::LeanStringObject<
    23,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 114, 101, 113, 117, 101, 115, 116, 32, 116, 97, 114,
        103, 101, 116, 0,
    ],
};
static mut l_Std_Http_RequestTarget_parse_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_RequestTarget_parse_x21___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_RequestTarget_parse_x21___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_RequestTarget_parse_x21___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_RequestTarget_originForm_x21___closed__0_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        83, 116, 100, 46, 72, 116, 116, 112, 46, 82, 101, 113, 117, 101, 115, 116, 84, 97, 114,
        103, 101, 116, 46, 111, 114, 105, 103, 105, 110, 70, 111, 114, 109, 33, 0,
    ],
};
static mut l_Std_Http_RequestTarget_originForm_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_RequestTarget_originForm_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_RequestTarget_originForm_x21___closed__1_value:
    crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 111, 114, 105, 103, 105, 110, 45, 102, 111, 114, 109,
        32, 114, 101, 113, 117, 101, 115, 116, 32, 116, 97, 114, 103, 101, 116, 58, 32, 0,
    ],
};
static mut l_Std_Http_RequestTarget_originForm_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_RequestTarget_originForm_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_URI_parse_x3f___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_URI_parse_x3f___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_RequestTarget_parse_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_URI_parse_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_parse_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_URI_parse_x21___closed__0_value: crate::leanh::LeanStringObject<20> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 85, 82, 73, 46, 112, 97, 114, 115, 101, 33, 0,
        ],
    };
static mut l_Std_Http_URI_parse_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_parse_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_URI_parse_x21___closed__1_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [105, 110, 118, 97, 108, 105, 100, 32, 85, 82, 73, 0],
    };
static mut l_Std_Http_URI_parse_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_parse_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Http_URI_parse_x21___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_URI_parse_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_URI_Path_parse_x3f___closed__0_value: crate::leanh::LeanClosureObject<2> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_URI_Path_parse_x3f___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_RequestTarget_parse_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_URI_Path_parse_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Path_parse_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_URI_Path_parseOrRoot___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Std_Http_URI_Path_parseOrRoot___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Path_parseOrRoot___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_URI_Path_parseOrRoot___closed__1_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_URI_Path_parseOrRoot___closed__0_value)
                as *mut crate::leanh::LeanObject,
            1 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Http_URI_Path_parseOrRoot___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_URI_Path_parseOrRoot___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Http_RequestTarget_parse_x3f___lam__0(
    mut v___x_197_: *mut crate::leanh::LeanObject,
    mut v___y_198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_204_: u8 = 0;
    let mut v___x_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_207_: u8 = 0;
    let mut v___x_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_212_: u8 = 0;
    let mut v_unused_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_199_ = l_Std_Http_URI_Parser_parseRequestTarget(v___x_197_, v___y_198_);
                if crate::leanh::lean_obj_tag(v___x_199_) == 0 {
                    v_pos_200_ = crate::leanh::lean_ctor_get(v___x_199_, 0);
                    crate::leanh::lean_inc(v_pos_200_);
                    v_array_201_ = crate::leanh::lean_ctor_get(v_pos_200_, 0);
                    v_idx_202_ = crate::leanh::lean_ctor_get(v_pos_200_, 1);
                    v___x_203_ = lean_byte_array_size(v_array_201_);
                    v___x_204_ = lean_nat_dec_lt(v_idx_202_, v___x_203_);
                    if v___x_204_ == 0 {
                        crate::leanh::lean_dec(v_pos_200_);
                        return v___x_199_;
                    } else {
                        v_isSharedCheck_212_ = (!crate::leanh::lean_is_exclusive(v___x_199_)) as u8;
                        if v_isSharedCheck_212_ == 0 {
                            v_unused_213_ = crate::leanh::lean_ctor_get(v___x_199_, 1);
                            crate::leanh::lean_dec(v_unused_213_);
                            v_unused_214_ = crate::leanh::lean_ctor_get(v___x_199_, 0);
                            crate::leanh::lean_dec(v_unused_214_);
                            v___x_206_ = v___x_199_;
                            v_isShared_207_ = v_isSharedCheck_212_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_199_);
                            v___x_206_ = crate::leanh::lean_box(0);
                            v_isShared_207_ = v_isSharedCheck_212_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v___x_199_;
                }
            }
            1 => {
                v___x_208_ = l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__1;
                if v_isShared_207_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_206_, 1);
                    crate::leanh::lean_ctor_set(v___x_206_, 1, v___x_208_);
                    v___x_210_ = v___x_206_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_211_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_211_, 0, v_pos_200_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_211_, 1, v___x_208_);
                    v___x_210_ = v_reuseFailAlloc_211_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_210_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_RequestTarget_parse_x3f(
    mut v_string_225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_233_: u8 = 0;
    let mut v___x_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_237_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_226_ = l_Std_Http_RequestTarget_parse_x3f___closed__1;
                v___x_227_ = lean_string_to_utf8(v_string_225_);
                v___x_228_ =
                    l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_226_, v___x_227_);
                if crate::leanh::lean_obj_tag(v___x_228_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_228_, 1);
                    v___x_229_ = crate::leanh::lean_box(0);
                    return v___x_229_;
                } else {
                    v_a_230_ = crate::leanh::lean_ctor_get(v___x_228_, 0);
                    v_isSharedCheck_237_ = (!crate::leanh::lean_is_exclusive(v___x_228_)) as u8;
                    if v_isSharedCheck_237_ == 0 {
                        v___x_232_ = v___x_228_;
                        v_isShared_233_ = v_isSharedCheck_237_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_230_);
                        crate::leanh::lean_dec(v___x_228_);
                        v___x_232_ = crate::leanh::lean_box(0);
                        v_isShared_233_ = v_isSharedCheck_237_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_233_ == 0 {
                    v___x_235_ = v___x_232_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_236_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_230_);
                    v___x_235_ = v_reuseFailAlloc_236_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_RequestTarget_parse_x3f___boxed(
    mut v_string_238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_239_ = l_Std_Http_RequestTarget_parse_x3f(v_string_238_);
    crate::leanh::lean_dec_ref(v_string_238_);
    return v_res_239_;
}
pub unsafe fn _init_l_Std_Http_RequestTarget_parse_x21___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_243_ = l_Std_Http_RequestTarget_parse_x21___closed__2;
    v___x_244_ = crate::leanh::lean_unsigned_to_nat(12);
    v___x_245_ = crate::leanh::lean_unsigned_to_nat(45);
    v___x_246_ = l_Std_Http_RequestTarget_parse_x21___closed__1;
    v___x_247_ = l_Std_Http_RequestTarget_parse_x21___closed__0;
    v___x_248_ =
        l_mkPanicMessageWithDecl(v___x_247_, v___x_246_, v___x_245_, v___x_244_, v___x_243_);
    return v___x_248_;
}
pub unsafe fn l_Std_Http_RequestTarget_parse_x21(
    mut v_string_249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_250_ = l_Std_Http_RequestTarget_parse_x3f___closed__1;
    v___x_251_ = lean_string_to_utf8(v_string_249_);
    v___x_252_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_250_, v___x_251_);
    if crate::leanh::lean_obj_tag(v___x_252_) == 0 {
        let mut v___x_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_252_, 1);
        v___x_253_ = l_Std_Http_instInhabitedRequestTarget_default;
        v___x_254_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Http_RequestTarget_parse_x21___closed__3),
            core::ptr::addr_of_mut!(l_Std_Http_RequestTarget_parse_x21___closed__3_once),
            _init_l_Std_Http_RequestTarget_parse_x21___closed__3,
        );
        v___x_255_ = l_panic___redArg(v___x_253_, v___x_254_);
        return v___x_255_;
    } else {
        let mut v_a_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_256_ = crate::leanh::lean_ctor_get(v___x_252_, 0);
        crate::leanh::lean_inc(v_a_256_);
        crate::leanh::lean_dec_ref_known(v___x_252_, 1);
        return v_a_256_;
    }
}
pub unsafe fn l_Std_Http_RequestTarget_parse_x21___boxed(
    mut v_string_257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_258_ = l_Std_Http_RequestTarget_parse_x21(v_string_257_);
    crate::leanh::lean_dec_ref(v_string_257_);
    return v_res_258_;
}
pub unsafe fn l_Std_Http_RequestTarget_originForm_x21(
    mut v_path_261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_262_ = l_Std_Http_instInhabitedRequestTarget_default;
                v___f_272_ = l_Std_Http_RequestTarget_parse_x3f___closed__1;
                v___x_273_ = lean_string_to_utf8(v_path_261_);
                v___x_274_ =
                    l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_272_, v___x_273_);
                if crate::leanh::lean_obj_tag(v___x_274_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_274_, 1);
                    state = 1;
                    continue;
                } else {
                    v_a_275_ = crate::leanh::lean_ctor_get(v___x_274_, 0);
                    crate::leanh::lean_inc(v_a_275_);
                    crate::leanh::lean_dec_ref_known(v___x_274_, 1);
                    if crate::leanh::lean_obj_tag(v_a_275_) == 0 {
                        return v_a_275_;
                    } else {
                        crate::leanh::lean_dec(v_a_275_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_264_ = l_Std_Http_RequestTarget_parse_x21___closed__0;
                v___x_265_ = l_Std_Http_RequestTarget_originForm_x21___closed__0;
                v___x_266_ = crate::leanh::lean_unsigned_to_nat(56);
                v___x_267_ = crate::leanh::lean_unsigned_to_nat(9);
                v___x_268_ = l_Std_Http_RequestTarget_originForm_x21___closed__1;
                v___x_269_ = lean_string_append(v___x_268_, v_path_261_);
                v___x_270_ = l_mkPanicMessageWithDecl(
                    v___x_264_, v___x_265_, v___x_266_, v___x_267_, v___x_269_,
                );
                crate::leanh::lean_dec_ref(v___x_269_);
                v___x_271_ = l_panic___redArg(v___x_262_, v___x_270_);
                return v___x_271_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_RequestTarget_originForm_x21___boxed(
    mut v_path_276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_277_ = l_Std_Http_RequestTarget_originForm_x21(v_path_276_);
    crate::leanh::lean_dec_ref(v_path_276_);
    return v_res_277_;
}
pub unsafe fn l_Std_Http_URI_parse_x3f___lam__0(
    mut v___x_278_: *mut crate::leanh::LeanObject,
    mut v___y_279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: u8 = 0;
    let mut v___x_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_288_: u8 = 0;
    let mut v___x_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_293_: u8 = 0;
    let mut v_unused_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_280_ = l_Std_Http_URI_Parser_parseURI(v___x_278_, v___y_279_);
                if crate::leanh::lean_obj_tag(v___x_280_) == 0 {
                    v_pos_281_ = crate::leanh::lean_ctor_get(v___x_280_, 0);
                    crate::leanh::lean_inc(v_pos_281_);
                    v_array_282_ = crate::leanh::lean_ctor_get(v_pos_281_, 0);
                    v_idx_283_ = crate::leanh::lean_ctor_get(v_pos_281_, 1);
                    v___x_284_ = lean_byte_array_size(v_array_282_);
                    v___x_285_ = lean_nat_dec_lt(v_idx_283_, v___x_284_);
                    if v___x_285_ == 0 {
                        crate::leanh::lean_dec(v_pos_281_);
                        return v___x_280_;
                    } else {
                        v_isSharedCheck_293_ = (!crate::leanh::lean_is_exclusive(v___x_280_)) as u8;
                        if v_isSharedCheck_293_ == 0 {
                            v_unused_294_ = crate::leanh::lean_ctor_get(v___x_280_, 1);
                            crate::leanh::lean_dec(v_unused_294_);
                            v_unused_295_ = crate::leanh::lean_ctor_get(v___x_280_, 0);
                            crate::leanh::lean_dec(v_unused_295_);
                            v___x_287_ = v___x_280_;
                            v_isShared_288_ = v_isSharedCheck_293_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_280_);
                            v___x_287_ = crate::leanh::lean_box(0);
                            v_isShared_288_ = v_isSharedCheck_293_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v___x_280_;
                }
            }
            1 => {
                v___x_289_ = l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__1;
                if v_isShared_288_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_287_, 1);
                    crate::leanh::lean_ctor_set(v___x_287_, 1, v___x_289_);
                    v___x_291_ = v___x_287_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_292_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_292_, 0, v_pos_281_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_292_, 1, v___x_289_);
                    v___x_291_ = v_reuseFailAlloc_292_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_291_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_parse_x3f(
    mut v_string_298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_306_: u8 = 0;
    let mut v___x_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_299_ = l_Std_Http_URI_parse_x3f___closed__0;
                v___x_300_ = lean_string_to_utf8(v_string_298_);
                v___x_301_ =
                    l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_299_, v___x_300_);
                if crate::leanh::lean_obj_tag(v___x_301_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_301_, 1);
                    v___x_302_ = crate::leanh::lean_box(0);
                    return v___x_302_;
                } else {
                    v_a_303_ = crate::leanh::lean_ctor_get(v___x_301_, 0);
                    v_isSharedCheck_310_ = (!crate::leanh::lean_is_exclusive(v___x_301_)) as u8;
                    if v_isSharedCheck_310_ == 0 {
                        v___x_305_ = v___x_301_;
                        v_isShared_306_ = v_isSharedCheck_310_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_303_);
                        crate::leanh::lean_dec(v___x_301_);
                        v___x_305_ = crate::leanh::lean_box(0);
                        v_isShared_306_ = v_isSharedCheck_310_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_306_ == 0 {
                    v___x_308_ = v___x_305_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_309_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
                    v___x_308_ = v_reuseFailAlloc_309_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_308_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_parse_x3f___boxed(
    mut v_string_311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_312_ = l_Std_Http_URI_parse_x3f(v_string_311_);
    crate::leanh::lean_dec_ref(v_string_311_);
    return v_res_312_;
}
pub unsafe fn _init_l_Std_Http_URI_parse_x21___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_315_ = l_Std_Http_URI_parse_x21___closed__1;
    v___x_316_ = crate::leanh::lean_unsigned_to_nat(12);
    v___x_317_ = crate::leanh::lean_unsigned_to_nat(77);
    v___x_318_ = l_Std_Http_URI_parse_x21___closed__0;
    v___x_319_ = l_Std_Http_RequestTarget_parse_x21___closed__0;
    v___x_320_ =
        l_mkPanicMessageWithDecl(v___x_319_, v___x_318_, v___x_317_, v___x_316_, v___x_315_);
    return v___x_320_;
}
pub unsafe fn l_Std_Http_URI_parse_x21(
    mut v_string_321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_322_ = l_Std_Http_URI_parse_x3f___closed__0;
    v___x_323_ = lean_string_to_utf8(v_string_321_);
    v___x_324_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_322_, v___x_323_);
    if crate::leanh::lean_obj_tag(v___x_324_) == 0 {
        let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_324_, 1);
        v___x_325_ = l_Std_Http_instInhabitedURI_default;
        v___x_326_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Http_URI_parse_x21___closed__2),
            core::ptr::addr_of_mut!(l_Std_Http_URI_parse_x21___closed__2_once),
            _init_l_Std_Http_URI_parse_x21___closed__2,
        );
        v___x_327_ = l_panic___redArg(v___x_325_, v___x_326_);
        return v___x_327_;
    } else {
        let mut v_a_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_328_ = crate::leanh::lean_ctor_get(v___x_324_, 0);
        crate::leanh::lean_inc(v_a_328_);
        crate::leanh::lean_dec_ref_known(v___x_324_, 1);
        return v_a_328_;
    }
}
pub unsafe fn l_Std_Http_URI_parse_x21___boxed(
    mut v_string_329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_330_ = l_Std_Http_URI_parse_x21(v_string_329_);
    crate::leanh::lean_dec_ref(v_string_329_);
    return v_res_330_;
}
pub unsafe fn l_Std_Http_URI_Path_parse_x3f___lam__0(
    mut v___x_331_: *mut crate::leanh::LeanObject,
    mut v___x_332_: u8,
    mut v___y_333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: u8 = 0;
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_342_: u8 = 0;
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_347_: u8 = 0;
    let mut v_unused_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_334_ =
                    l_Std_Http_URI_Parser_parsePath(v___x_331_, v___x_332_, v___x_332_, v___y_333_);
                if crate::leanh::lean_obj_tag(v___x_334_) == 0 {
                    v_pos_335_ = crate::leanh::lean_ctor_get(v___x_334_, 0);
                    crate::leanh::lean_inc(v_pos_335_);
                    v_array_336_ = crate::leanh::lean_ctor_get(v_pos_335_, 0);
                    v_idx_337_ = crate::leanh::lean_ctor_get(v_pos_335_, 1);
                    v___x_338_ = lean_byte_array_size(v_array_336_);
                    v___x_339_ = lean_nat_dec_lt(v_idx_337_, v___x_338_);
                    if v___x_339_ == 0 {
                        crate::leanh::lean_dec(v_pos_335_);
                        return v___x_334_;
                    } else {
                        v_isSharedCheck_347_ = (!crate::leanh::lean_is_exclusive(v___x_334_)) as u8;
                        if v_isSharedCheck_347_ == 0 {
                            v_unused_348_ = crate::leanh::lean_ctor_get(v___x_334_, 1);
                            crate::leanh::lean_dec(v_unused_348_);
                            v_unused_349_ = crate::leanh::lean_ctor_get(v___x_334_, 0);
                            crate::leanh::lean_dec(v_unused_349_);
                            v___x_341_ = v___x_334_;
                            v_isShared_342_ = v_isSharedCheck_347_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_334_);
                            v___x_341_ = crate::leanh::lean_box(0);
                            v_isShared_342_ = v_isSharedCheck_347_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v___x_334_;
                }
            }
            1 => {
                v___x_343_ = l_Std_Http_RequestTarget_parse_x3f___lam__0___closed__1;
                if v_isShared_342_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_341_, 1);
                    crate::leanh::lean_ctor_set(v___x_341_, 1, v___x_343_);
                    v___x_345_ = v___x_341_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_346_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_346_, 0, v_pos_335_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_346_, 1, v___x_343_);
                    v___x_345_ = v_reuseFailAlloc_346_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_345_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_Path_parse_x3f___lam__0___boxed(
    mut v___x_350_: *mut crate::leanh::LeanObject,
    mut v___x_351_: *mut crate::leanh::LeanObject,
    mut v___y_352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_274__boxed_353_: u8 = 0;
    let mut v_res_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_274__boxed_353_ = (crate::leanh::lean_unbox(v___x_351_) as u8);
    v_res_354_ =
        l_Std_Http_URI_Path_parse_x3f___lam__0(v___x_350_, v___x_274__boxed_353_, v___y_352_);
    return v_res_354_;
}
pub unsafe fn l_Std_Http_URI_Path_parse_x3f(
    mut v_s_359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_367_: u8 = 0;
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_371_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_360_ = l_Std_Http_URI_Path_parse_x3f___closed__0;
                v___x_361_ = lean_string_to_utf8(v_s_359_);
                v___x_362_ =
                    l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_360_, v___x_361_);
                if crate::leanh::lean_obj_tag(v___x_362_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_362_, 1);
                    v___x_363_ = crate::leanh::lean_box(0);
                    return v___x_363_;
                } else {
                    v_a_364_ = crate::leanh::lean_ctor_get(v___x_362_, 0);
                    v_isSharedCheck_371_ = (!crate::leanh::lean_is_exclusive(v___x_362_)) as u8;
                    if v_isSharedCheck_371_ == 0 {
                        v___x_366_ = v___x_362_;
                        v_isShared_367_ = v_isSharedCheck_371_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_364_);
                        crate::leanh::lean_dec(v___x_362_);
                        v___x_366_ = crate::leanh::lean_box(0);
                        v_isShared_367_ = v_isSharedCheck_371_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_367_ == 0 {
                    v___x_369_ = v___x_366_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_370_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
                    v___x_369_ = v_reuseFailAlloc_370_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_369_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_URI_Path_parse_x3f___boxed(
    mut v_s_372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_373_ = l_Std_Http_URI_Path_parse_x3f(v_s_372_);
    crate::leanh::lean_dec_ref(v_s_372_);
    return v_res_373_;
}
pub unsafe fn l_Std_Http_URI_Path_parseOrRoot(
    mut v_s_379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_380_ = l_Std_Http_URI_Path_parse_x3f___closed__0;
    v___x_381_ = lean_string_to_utf8(v_s_379_);
    v___x_382_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_380_, v___x_381_);
    if crate::leanh::lean_obj_tag(v___x_382_) == 0 {
        let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_382_, 1);
        v___x_383_ = l_Std_Http_URI_Path_parseOrRoot___closed__1;
        return v___x_383_;
    } else {
        let mut v_a_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_384_ = crate::leanh::lean_ctor_get(v___x_382_, 0);
        crate::leanh::lean_inc(v_a_384_);
        crate::leanh::lean_dec_ref_known(v___x_382_, 1);
        return v_a_384_;
    }
}
pub unsafe fn l_Std_Http_URI_Path_parseOrRoot___boxed(
    mut v_s_385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_386_ = l_Std_Http_URI_Path_parseOrRoot(v_s_385_);
    crate::leanh::lean_dec_ref(v_s_385_);
    return v_res_386_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Data_URI(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Http_Data_URI_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_URI_Parser(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Data_URI(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Data_URI(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Http_Data_URI_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Data_URI_Parser(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_URI(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Data_URI(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Http_Data_URI(builtin);
}

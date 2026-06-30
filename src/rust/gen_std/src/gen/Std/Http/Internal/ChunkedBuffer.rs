// Lean compiler output
// Module: Std.Http.Internal.ChunkedBuffer
// Imports: Init.Data.ToString Init.Data.Array.Lemmas Init.Data.String.Basic Init.Data.ByteArray
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_byte_array_copy_slice,
    lean_byte_array_mk, lean_byte_array_size, lean_mk_empty_array_with_capacity,
    lean_mk_empty_byte_array, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_string_to_utf8, lean_uint32_to_uint8, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold, l_Array_append___redArg,
};
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::ByteArray::{
    initialize_Init_Data_ByteArray, runtime_initialize_Init_Data_ByteArray,
};
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::r#gen::Init::Data::ToString::{
    initialize_Init_Data_ToString, runtime_initialize_Init_Data_ToString,
};
pub static l_Std_Http_Internal_ChunkedBuffer_empty___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Http_Internal_ChunkedBuffer_empty___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_empty___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_empty___closed__0_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Internal_ChunkedBuffer_empty___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Internal_ChunkedBuffer_empty: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__3_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__4_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__5_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__6_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__7_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__8_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_ofArray___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_ChunkedBuffer_ofArray___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_ofArray___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Internal_ChunkedBuffer_instInhabited: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Internal_ChunkedBuffer_instEmptyCollection:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_instCoeByteArray___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Internal_ChunkedBuffer_ofByteArray as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_ChunkedBuffer_instCoeByteArray___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_instCoeByteArray___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Internal_ChunkedBuffer_instCoeByteArray: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_instCoeByteArray___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_instCoeArrayByteArray___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Internal_ChunkedBuffer_ofArray as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_ChunkedBuffer_instCoeArrayByteArray___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_instCoeArrayByteArray___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Internal_ChunkedBuffer_instCoeArrayByteArray:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_instCoeArrayByteArray___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_push(
    mut v_c_194_: *mut leanh::LeanObject,
    mut v_b_195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_data_196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_200_: u8 = 0;
    let mut v___x_201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_207_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_data_196_ = leanh::lean_ctor_get(v_c_194_, 0);
                v_size_197_ = leanh::lean_ctor_get(v_c_194_, 1);
                v_isSharedCheck_207_ = (!leanh::lean_is_exclusive(v_c_194_)) as u8;
                if v_isSharedCheck_207_ == 0 {
                    v___x_199_ = v_c_194_;
                    v_isShared_200_ = v_isSharedCheck_207_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_size_197_);
                    leanh::lean_inc(v_data_196_);
                    leanh::lean_dec(v_c_194_);
                    v___x_199_ = leanh::lean_box(0);
                    v_isShared_200_ = v_isSharedCheck_207_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_b_195_);
                v___x_201_ = lean_array_push(v_data_196_, v_b_195_);
                v___x_202_ = lean_byte_array_size(v_b_195_);
                leanh::lean_dec_ref(v_b_195_);
                v___x_203_ = lean_nat_add(v_size_197_, v___x_202_);
                leanh::lean_dec(v_size_197_);
                if v_isShared_200_ == 0 {
                    leanh::lean_ctor_set(v___x_199_, 1, v___x_203_);
                    leanh::lean_ctor_set(v___x_199_, 0, v___x_201_);
                    v___x_205_ = v___x_199_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_206_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_201_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_206_, 1, v___x_203_);
                    v___x_205_ = v_reuseFailAlloc_206_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_205_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_write(
    mut v_buffer_208_: *mut leanh::LeanObject,
    mut v_data_209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_data_210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_214_: u8 = 0;
    let mut v___x_215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_221_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_data_210_ = leanh::lean_ctor_get(v_buffer_208_, 0);
                v_size_211_ = leanh::lean_ctor_get(v_buffer_208_, 1);
                v_isSharedCheck_221_ = (!leanh::lean_is_exclusive(v_buffer_208_)) as u8;
                if v_isSharedCheck_221_ == 0 {
                    v___x_213_ = v_buffer_208_;
                    v_isShared_214_ = v_isSharedCheck_221_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_size_211_);
                    leanh::lean_inc(v_data_210_);
                    leanh::lean_dec(v_buffer_208_);
                    v___x_213_ = leanh::lean_box(0);
                    v_isShared_214_ = v_isSharedCheck_221_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_data_209_);
                v___x_215_ = lean_array_push(v_data_210_, v_data_209_);
                v___x_216_ = lean_byte_array_size(v_data_209_);
                leanh::lean_dec_ref(v_data_209_);
                v___x_217_ = lean_nat_add(v_size_211_, v___x_216_);
                leanh::lean_dec(v_size_211_);
                if v_isShared_214_ == 0 {
                    leanh::lean_ctor_set(v___x_213_, 1, v___x_217_);
                    leanh::lean_ctor_set(v___x_213_, 0, v___x_215_);
                    v___x_219_ = v___x_213_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_220_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_215_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_220_, 1, v___x_217_);
                    v___x_219_ = v_reuseFailAlloc_220_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_219_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_append(
    mut v_buffer_222_: *mut leanh::LeanObject,
    mut v_data_223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_data_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_230_: u8 = 0;
    let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_236_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_data_224_ = leanh::lean_ctor_get(v_buffer_222_, 0);
                leanh::lean_inc_ref(v_data_224_);
                v_size_225_ = leanh::lean_ctor_get(v_buffer_222_, 1);
                leanh::lean_inc(v_size_225_);
                leanh::lean_dec_ref(v_buffer_222_);
                v_data_226_ = leanh::lean_ctor_get(v_data_223_, 0);
                v_size_227_ = leanh::lean_ctor_get(v_data_223_, 1);
                v_isSharedCheck_236_ = (!leanh::lean_is_exclusive(v_data_223_)) as u8;
                if v_isSharedCheck_236_ == 0 {
                    v___x_229_ = v_data_223_;
                    v_isShared_230_ = v_isSharedCheck_236_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_size_227_);
                    leanh::lean_inc(v_data_226_);
                    leanh::lean_dec(v_data_223_);
                    v___x_229_ = leanh::lean_box(0);
                    v_isShared_230_ = v_isSharedCheck_236_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_231_ = l_Array_append___redArg(v_data_224_, v_data_226_);
                leanh::lean_dec_ref(v_data_226_);
                v___x_232_ = lean_nat_add(v_size_225_, v_size_227_);
                leanh::lean_dec(v_size_227_);
                leanh::lean_dec(v_size_225_);
                if v_isShared_230_ == 0 {
                    leanh::lean_ctor_set(v___x_229_, 1, v___x_232_);
                    leanh::lean_ctor_set(v___x_229_, 0, v___x_231_);
                    v___x_234_ = v___x_229_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_235_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_231_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_235_, 1, v___x_232_);
                    v___x_234_ = v_reuseFailAlloc_235_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_234_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_writeChar(
    mut v_buffer_237_: *mut leanh::LeanObject,
    mut v_data_238_: u32,
) -> *mut leanh::LeanObject {
    let mut v_data_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_243_: u8 = 0;
    let mut v___x_244_: u8 = 0;
    let mut v___x_245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_256_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_data_239_ = leanh::lean_ctor_get(v_buffer_237_, 0);
                v_size_240_ = leanh::lean_ctor_get(v_buffer_237_, 1);
                v_isSharedCheck_256_ = (!leanh::lean_is_exclusive(v_buffer_237_)) as u8;
                if v_isSharedCheck_256_ == 0 {
                    v___x_242_ = v_buffer_237_;
                    v_isShared_243_ = v_isSharedCheck_256_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_size_240_);
                    leanh::lean_inc(v_data_239_);
                    leanh::lean_dec(v_buffer_237_);
                    v___x_242_ = leanh::lean_box(0);
                    v_isShared_243_ = v_isSharedCheck_256_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_244_ = lean_uint32_to_uint8(v_data_238_);
                v___x_245_ = leanh::lean_unsigned_to_nat(1);
                v___x_246_ = lean_mk_empty_array_with_capacity(v___x_245_);
                v___x_247_ = leanh::lean_box((v___x_244_) as usize);
                v___x_248_ = lean_array_push(v___x_246_, v___x_247_);
                v___x_249_ = lean_byte_array_mk(v___x_248_);
                leanh::lean_inc_ref(v___x_249_);
                v___x_250_ = lean_array_push(v_data_239_, v___x_249_);
                v___x_251_ = lean_byte_array_size(v___x_249_);
                leanh::lean_dec_ref(v___x_249_);
                v___x_252_ = lean_nat_add(v_size_240_, v___x_251_);
                leanh::lean_dec(v_size_240_);
                if v_isShared_243_ == 0 {
                    leanh::lean_ctor_set(v___x_242_, 1, v___x_252_);
                    leanh::lean_ctor_set(v___x_242_, 0, v___x_250_);
                    v___x_254_ = v___x_242_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_255_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_250_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_255_, 1, v___x_252_);
                    v___x_254_ = v_reuseFailAlloc_255_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_254_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_writeChar___boxed(
    mut v_buffer_257_: *mut leanh::LeanObject,
    mut v_data_258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_data_boxed_259_: u32 = 0;
    let mut v_res_260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_data_boxed_259_ = leanh::lean_unbox_uint32(v_data_258_);
    leanh::lean_dec(v_data_258_);
    v_res_260_ = l_Std_Http_Internal_ChunkedBuffer_writeChar(v_buffer_257_, v_data_boxed_259_);
    return v_res_260_;
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_writeString(
    mut v_buffer_261_: *mut leanh::LeanObject,
    mut v_data_262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_data_263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_267_: u8 = 0;
    let mut v___x_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_data_263_ = leanh::lean_ctor_get(v_buffer_261_, 0);
                v_size_264_ = leanh::lean_ctor_get(v_buffer_261_, 1);
                v_isSharedCheck_275_ = (!leanh::lean_is_exclusive(v_buffer_261_)) as u8;
                if v_isSharedCheck_275_ == 0 {
                    v___x_266_ = v_buffer_261_;
                    v_isShared_267_ = v_isSharedCheck_275_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_size_264_);
                    leanh::lean_inc(v_data_263_);
                    leanh::lean_dec(v_buffer_261_);
                    v___x_266_ = leanh::lean_box(0);
                    v_isShared_267_ = v_isSharedCheck_275_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_268_ = lean_string_to_utf8(v_data_262_);
                leanh::lean_inc_ref(v___x_268_);
                v___x_269_ = lean_array_push(v_data_263_, v___x_268_);
                v___x_270_ = lean_byte_array_size(v___x_268_);
                leanh::lean_dec_ref(v___x_268_);
                v___x_271_ = lean_nat_add(v_size_264_, v___x_270_);
                leanh::lean_dec(v_size_264_);
                if v_isShared_267_ == 0 {
                    leanh::lean_ctor_set(v___x_266_, 1, v___x_271_);
                    leanh::lean_ctor_set(v___x_266_, 0, v___x_269_);
                    v___x_273_ = v___x_266_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_274_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_269_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_271_);
                    v___x_273_ = v_reuseFailAlloc_274_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_273_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_writeString___boxed(
    mut v_buffer_276_: *mut leanh::LeanObject,
    mut v_data_277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_278_ = l_Std_Http_Internal_ChunkedBuffer_writeString(v_buffer_276_, v_data_277_);
    leanh::lean_dec_ref(v_data_277_);
    return v_res_278_;
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0(
    mut v___x_279_: u8,
    mut v_x1_280_: *mut leanh::LeanObject,
    mut v_x2_281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_282_ = leanh::lean_unsigned_to_nat(0);
    v___x_283_ = lean_byte_array_size(v_x1_280_);
    v___x_284_ = lean_byte_array_size(v_x2_281_);
    v___x_285_ = lean_byte_array_copy_slice(
        v_x2_281_, v___x_282_, v_x1_280_, v___x_283_, v___x_284_, v___x_279_,
    );
    return v___x_285_;
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0___boxed(
    mut v___x_286_: *mut leanh::LeanObject,
    mut v_x1_287_: *mut leanh::LeanObject,
    mut v_x2_288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_92__boxed_289_: u8 = 0;
    let mut v_res_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_92__boxed_289_ = (leanh::lean_unbox(v___x_286_) as u8);
    v_res_290_ = l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0(
        v___x_92__boxed_289_,
        v_x1_287_,
        v_x2_288_,
    );
    leanh::lean_dec_ref(v_x2_288_);
    return v_res_290_;
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_toByteArray(
    mut v_cb_310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_data_311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: u8 = 0;
    v_data_311_ = leanh::lean_ctor_get(v_cb_310_, 0);
    leanh::lean_inc_ref(v_data_311_);
    v_size_312_ = leanh::lean_ctor_get(v_cb_310_, 1);
    leanh::lean_inc(v_size_312_);
    leanh::lean_dec_ref(v_cb_310_);
    v___x_313_ = leanh::lean_unsigned_to_nat(1);
    v___x_314_ = lean_array_get_size(v_data_311_);
    v___x_315_ = lean_nat_dec_eq(v___x_313_, v___x_314_);
    if v___x_315_ == 0 {
        let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_319_: u8 = 0;
        v___x_316_ = lean_mk_empty_byte_array(v_size_312_);
        leanh::lean_dec(v_size_312_);
        v___x_317_ = leanh::lean_unsigned_to_nat(0);
        v___x_318_ = l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9;
        v___x_319_ = lean_nat_dec_lt(v___x_317_, v___x_314_);
        if v___x_319_ == 0 {
            leanh::lean_dec_ref(v_data_311_);
            return v___x_316_;
        } else {
            let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_321_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_322_: u8 = 0;
            v___x_320_ = leanh::lean_box((v___x_315_) as usize);
            v___f_321_ = leanh::lean_alloc_closure(
                l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0___boxed
                    as *mut core::ffi::c_void,
                3,
                1,
            );
            leanh::lean_closure_set(v___f_321_, 0, v___x_320_);
            v___x_322_ = lean_nat_dec_le(v___x_314_, v___x_314_);
            if v___x_322_ == 0 {
                if v___x_319_ == 0 {
                    leanh::lean_dec_ref(v___f_321_);
                    leanh::lean_dec_ref(v_data_311_);
                    return v___x_316_;
                } else {
                    let mut v___x_323_: usize = 0;
                    let mut v___x_324_: usize = 0;
                    let mut v___x_325_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_323_ = 0usize;
                    v___x_324_ = lean_usize_of_nat(v___x_314_);
                    v___x_325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_318_,
                        v___f_321_,
                        v_data_311_,
                        v___x_323_,
                        v___x_324_,
                        v___x_316_,
                    );
                    return v___x_325_;
                }
            } else {
                let mut v___x_326_: usize = 0;
                let mut v___x_327_: usize = 0;
                let mut v___x_328_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_326_ = 0usize;
                v___x_327_ = lean_usize_of_nat(v___x_314_);
                v___x_328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_318_,
                    v___f_321_,
                    v_data_311_,
                    v___x_326_,
                    v___x_327_,
                    v___x_316_,
                );
                return v___x_328_;
            }
        }
    } else {
        let mut v___x_329_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_330_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_size_312_);
        v___x_329_ = leanh::lean_unsigned_to_nat(0);
        v___x_330_ = lean_array_fget(v_data_311_, v___x_329_);
        leanh::lean_dec_ref(v_data_311_);
        return v___x_330_;
    }
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_ofByteArray(
    mut v_bs_331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_332_ = leanh::lean_unsigned_to_nat(1);
    v___x_333_ = lean_mk_empty_array_with_capacity(v___x_332_);
    leanh::lean_inc_ref(v_bs_331_);
    v___x_334_ = lean_array_push(v___x_333_, v_bs_331_);
    v___x_335_ = lean_byte_array_size(v_bs_331_);
    leanh::lean_dec_ref(v_bs_331_);
    v___x_336_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_336_, 0, v___x_334_);
    leanh::lean_ctor_set(v___x_336_, 1, v___x_335_);
    return v___x_336_;
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0(
    mut v_x1_337_: *mut leanh::LeanObject,
    mut v_x2_338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_339_ = lean_byte_array_size(v_x2_338_);
    v___x_340_ = lean_nat_add(v_x1_337_, v___x_339_);
    return v___x_340_;
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0___boxed(
    mut v_x1_341_: *mut leanh::LeanObject,
    mut v_x2_342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_343_ = l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0(v_x1_341_, v_x2_342_);
    leanh::lean_dec_ref(v_x2_342_);
    leanh::lean_dec(v_x1_341_);
    return v_res_343_;
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_ofArray(
    mut v_bs_345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: u8 = 0;
    v___x_346_ = leanh::lean_unsigned_to_nat(0);
    v___x_347_ = lean_array_get_size(v_bs_345_);
    v___x_348_ = l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9;
    v___x_349_ = lean_nat_dec_lt(v___x_346_, v___x_347_);
    if v___x_349_ == 0 {
        let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_350_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_350_, 0, v_bs_345_);
        leanh::lean_ctor_set(v___x_350_, 1, v___x_346_);
        return v___x_350_;
    } else {
        let mut v___f_351_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_352_: u8 = 0;
        v___f_351_ = l_Std_Http_Internal_ChunkedBuffer_ofArray___closed__0;
        v___x_352_ = lean_nat_dec_le(v___x_347_, v___x_347_);
        if v___x_352_ == 0 {
            if v___x_349_ == 0 {
                let mut v___x_353_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_353_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_353_, 0, v_bs_345_);
                leanh::lean_ctor_set(v___x_353_, 1, v___x_346_);
                return v___x_353_;
            } else {
                let mut v___x_354_: usize = 0;
                let mut v___x_355_: usize = 0;
                let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_354_ = 0usize;
                v___x_355_ = lean_usize_of_nat(v___x_347_);
                leanh::lean_inc_ref(v_bs_345_);
                v___x_356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_348_,
                    v___f_351_,
                    v_bs_345_,
                    v___x_354_,
                    v___x_355_,
                    v___x_346_,
                );
                v___x_357_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_357_, 0, v_bs_345_);
                leanh::lean_ctor_set(v___x_357_, 1, v___x_356_);
                return v___x_357_;
            }
        } else {
            let mut v___x_358_: usize = 0;
            let mut v___x_359_: usize = 0;
            let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_361_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_358_ = 0usize;
            v___x_359_ = lean_usize_of_nat(v___x_347_);
            leanh::lean_inc_ref(v_bs_345_);
            v___x_360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_348_,
                v___f_351_,
                v_bs_345_,
                v___x_358_,
                v___x_359_,
                v___x_346_,
            );
            v___x_361_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_361_, 0, v_bs_345_);
            leanh::lean_ctor_set(v___x_361_, 1, v___x_360_);
            return v___x_361_;
        }
    }
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_isEmpty(
    mut v_bb_362_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_size_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: u8 = 0;
    v_size_363_ = leanh::lean_ctor_get(v_bb_362_, 1);
    v___x_364_ = leanh::lean_unsigned_to_nat(0);
    v___x_365_ = lean_nat_dec_eq(v_size_363_, v___x_364_);
    return v___x_365_;
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_isEmpty___boxed(
    mut v_bb_366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_367_: u8 = 0;
    let mut v_r_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_367_ = l_Std_Http_Internal_ChunkedBuffer_isEmpty(v_bb_366_);
    leanh::lean_dec_ref(v_bb_366_);
    v_r_368_ = leanh::lean_box((v_res_367_) as usize);
    return v_r_368_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Internal_ChunkedBuffer(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ByteArray(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Internal_ChunkedBuffer(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Internal_ChunkedBuffer(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ByteArray(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Internal_ChunkedBuffer(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Internal_ChunkedBuffer(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Http_Internal_ChunkedBuffer(builtin);
}
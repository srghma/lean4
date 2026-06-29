// Lean compiler output
// Module: Std.Http.Internal.ChunkedBuffer
// Imports: Init.Data.ToString Init.Data.Array.Lemmas Init.Data.String.Basic Init.Data.ByteArray
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
use crate::ffi::lean_byte_array_copy_slice;
use crate::ffi::lean_string_to_utf8;
use crate::ffi::{lean_uint32_to_uint8, lean_usize_of_nat};
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_byte_array_mk,
    lean_byte_array_size, lean_mk_empty_array_with_capacity, lean_mk_empty_byte_array,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
};
pub static l_Std_Http_Internal_ChunkedBuffer_empty___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Http_Internal_ChunkedBuffer_empty___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_empty___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_empty___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Internal_ChunkedBuffer_empty___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Internal_ChunkedBuffer_empty: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__3_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__4_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__5_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__6_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__7_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__8_value:
    crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__8_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_ofArray___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_ChunkedBuffer_ofArray___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_ofArray___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Internal_ChunkedBuffer_instInhabited: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Internal_ChunkedBuffer_instEmptyCollection:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_instCoeByteArray___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Internal_ChunkedBuffer_ofByteArray as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_ChunkedBuffer_instCoeByteArray___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_instCoeByteArray___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Internal_ChunkedBuffer_instCoeByteArray: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_instCoeByteArray___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_instCoeArrayByteArray___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Internal_ChunkedBuffer_ofArray as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_ChunkedBuffer_instCoeArrayByteArray___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_instCoeArrayByteArray___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Http_Internal_ChunkedBuffer_instCoeArrayByteArray:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_instCoeArrayByteArray___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_push(
    mut v_c_194_: *mut crate::leanh::LeanObject,
    mut v_b_195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_data_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_200_: u8 = 0;
    let mut v___x_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_207_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_data_196_ = crate::leanh::lean_ctor_get(v_c_194_, 0);
                v_size_197_ = crate::leanh::lean_ctor_get(v_c_194_, 1);
                v_isSharedCheck_207_ = (!crate::leanh::lean_is_exclusive(v_c_194_)) as u8;
                if v_isSharedCheck_207_ == 0 {
                    v___x_199_ = v_c_194_;
                    v_isShared_200_ = v_isSharedCheck_207_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_size_197_);
                    crate::leanh::lean_inc(v_data_196_);
                    crate::leanh::lean_dec(v_c_194_);
                    v___x_199_ = crate::leanh::lean_box(0);
                    v_isShared_200_ = v_isSharedCheck_207_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_b_195_);
                v___x_201_ = lean_array_push(v_data_196_, v_b_195_);
                v___x_202_ = lean_byte_array_size(v_b_195_);
                crate::leanh::lean_dec_ref(v_b_195_);
                v___x_203_ = lean_nat_add(v_size_197_, v___x_202_);
                crate::leanh::lean_dec(v_size_197_);
                if v_isShared_200_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_199_, 1, v___x_203_);
                    crate::leanh::lean_ctor_set(v___x_199_, 0, v___x_201_);
                    v___x_205_ = v___x_199_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_206_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_201_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_206_, 1, v___x_203_);
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
    mut v_buffer_208_: *mut crate::leanh::LeanObject,
    mut v_data_209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_data_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_214_: u8 = 0;
    let mut v___x_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_221_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_data_210_ = crate::leanh::lean_ctor_get(v_buffer_208_, 0);
                v_size_211_ = crate::leanh::lean_ctor_get(v_buffer_208_, 1);
                v_isSharedCheck_221_ = (!crate::leanh::lean_is_exclusive(v_buffer_208_)) as u8;
                if v_isSharedCheck_221_ == 0 {
                    v___x_213_ = v_buffer_208_;
                    v_isShared_214_ = v_isSharedCheck_221_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_size_211_);
                    crate::leanh::lean_inc(v_data_210_);
                    crate::leanh::lean_dec(v_buffer_208_);
                    v___x_213_ = crate::leanh::lean_box(0);
                    v_isShared_214_ = v_isSharedCheck_221_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_data_209_);
                v___x_215_ = lean_array_push(v_data_210_, v_data_209_);
                v___x_216_ = lean_byte_array_size(v_data_209_);
                crate::leanh::lean_dec_ref(v_data_209_);
                v___x_217_ = lean_nat_add(v_size_211_, v___x_216_);
                crate::leanh::lean_dec(v_size_211_);
                if v_isShared_214_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_213_, 1, v___x_217_);
                    crate::leanh::lean_ctor_set(v___x_213_, 0, v___x_215_);
                    v___x_219_ = v___x_213_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_220_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_215_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_220_, 1, v___x_217_);
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
    mut v_buffer_222_: *mut crate::leanh::LeanObject,
    mut v_data_223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_data_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_230_: u8 = 0;
    let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_236_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_data_224_ = crate::leanh::lean_ctor_get(v_buffer_222_, 0);
                crate::leanh::lean_inc_ref(v_data_224_);
                v_size_225_ = crate::leanh::lean_ctor_get(v_buffer_222_, 1);
                crate::leanh::lean_inc(v_size_225_);
                crate::leanh::lean_dec_ref(v_buffer_222_);
                v_data_226_ = crate::leanh::lean_ctor_get(v_data_223_, 0);
                v_size_227_ = crate::leanh::lean_ctor_get(v_data_223_, 1);
                v_isSharedCheck_236_ = (!crate::leanh::lean_is_exclusive(v_data_223_)) as u8;
                if v_isSharedCheck_236_ == 0 {
                    v___x_229_ = v_data_223_;
                    v_isShared_230_ = v_isSharedCheck_236_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_size_227_);
                    crate::leanh::lean_inc(v_data_226_);
                    crate::leanh::lean_dec(v_data_223_);
                    v___x_229_ = crate::leanh::lean_box(0);
                    v_isShared_230_ = v_isSharedCheck_236_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_231_ = l_Array_append___redArg(v_data_224_, v_data_226_);
                crate::leanh::lean_dec_ref(v_data_226_);
                v___x_232_ = lean_nat_add(v_size_225_, v_size_227_);
                crate::leanh::lean_dec(v_size_227_);
                crate::leanh::lean_dec(v_size_225_);
                if v_isShared_230_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_229_, 1, v___x_232_);
                    crate::leanh::lean_ctor_set(v___x_229_, 0, v___x_231_);
                    v___x_234_ = v___x_229_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_235_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_231_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_235_, 1, v___x_232_);
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
    mut v_buffer_237_: *mut crate::leanh::LeanObject,
    mut v_data_238_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v_data_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_243_: u8 = 0;
    let mut v___x_244_: u8 = 0;
    let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_256_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_data_239_ = crate::leanh::lean_ctor_get(v_buffer_237_, 0);
                v_size_240_ = crate::leanh::lean_ctor_get(v_buffer_237_, 1);
                v_isSharedCheck_256_ = (!crate::leanh::lean_is_exclusive(v_buffer_237_)) as u8;
                if v_isSharedCheck_256_ == 0 {
                    v___x_242_ = v_buffer_237_;
                    v_isShared_243_ = v_isSharedCheck_256_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_size_240_);
                    crate::leanh::lean_inc(v_data_239_);
                    crate::leanh::lean_dec(v_buffer_237_);
                    v___x_242_ = crate::leanh::lean_box(0);
                    v_isShared_243_ = v_isSharedCheck_256_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_244_ = lean_uint32_to_uint8(v_data_238_);
                v___x_245_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_246_ = lean_mk_empty_array_with_capacity(v___x_245_);
                v___x_247_ = crate::leanh::lean_box((v___x_244_) as usize);
                v___x_248_ = lean_array_push(v___x_246_, v___x_247_);
                v___x_249_ = lean_byte_array_mk(v___x_248_);
                crate::leanh::lean_inc_ref(v___x_249_);
                v___x_250_ = lean_array_push(v_data_239_, v___x_249_);
                v___x_251_ = lean_byte_array_size(v___x_249_);
                crate::leanh::lean_dec_ref(v___x_249_);
                v___x_252_ = lean_nat_add(v_size_240_, v___x_251_);
                crate::leanh::lean_dec(v_size_240_);
                if v_isShared_243_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_242_, 1, v___x_252_);
                    crate::leanh::lean_ctor_set(v___x_242_, 0, v___x_250_);
                    v___x_254_ = v___x_242_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_255_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_250_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_255_, 1, v___x_252_);
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
    mut v_buffer_257_: *mut crate::leanh::LeanObject,
    mut v_data_258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_data_boxed_259_: u32 = 0;
    let mut v_res_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_data_boxed_259_ = crate::leanh::lean_unbox_uint32(v_data_258_);
    crate::leanh::lean_dec(v_data_258_);
    v_res_260_ = l_Std_Http_Internal_ChunkedBuffer_writeChar(v_buffer_257_, v_data_boxed_259_);
    return v_res_260_;
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_writeString(
    mut v_buffer_261_: *mut crate::leanh::LeanObject,
    mut v_data_262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_data_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_267_: u8 = 0;
    let mut v___x_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_data_263_ = crate::leanh::lean_ctor_get(v_buffer_261_, 0);
                v_size_264_ = crate::leanh::lean_ctor_get(v_buffer_261_, 1);
                v_isSharedCheck_275_ = (!crate::leanh::lean_is_exclusive(v_buffer_261_)) as u8;
                if v_isSharedCheck_275_ == 0 {
                    v___x_266_ = v_buffer_261_;
                    v_isShared_267_ = v_isSharedCheck_275_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_size_264_);
                    crate::leanh::lean_inc(v_data_263_);
                    crate::leanh::lean_dec(v_buffer_261_);
                    v___x_266_ = crate::leanh::lean_box(0);
                    v_isShared_267_ = v_isSharedCheck_275_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_268_ = lean_string_to_utf8(v_data_262_);
                crate::leanh::lean_inc_ref(v___x_268_);
                v___x_269_ = lean_array_push(v_data_263_, v___x_268_);
                v___x_270_ = lean_byte_array_size(v___x_268_);
                crate::leanh::lean_dec_ref(v___x_268_);
                v___x_271_ = lean_nat_add(v_size_264_, v___x_270_);
                crate::leanh::lean_dec(v_size_264_);
                if v_isShared_267_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_266_, 1, v___x_271_);
                    crate::leanh::lean_ctor_set(v___x_266_, 0, v___x_269_);
                    v___x_273_ = v___x_266_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_274_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_269_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_271_);
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
    mut v_buffer_276_: *mut crate::leanh::LeanObject,
    mut v_data_277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_278_ = l_Std_Http_Internal_ChunkedBuffer_writeString(v_buffer_276_, v_data_277_);
    crate::leanh::lean_dec_ref(v_data_277_);
    return v_res_278_;
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0(
    mut v___x_279_: u8,
    mut v_x1_280_: *mut crate::leanh::LeanObject,
    mut v_x2_281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_282_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_283_ = lean_byte_array_size(v_x1_280_);
    v___x_284_ = lean_byte_array_size(v_x2_281_);
    v___x_285_ = lean_byte_array_copy_slice(
        v_x2_281_, v___x_282_, v_x1_280_, v___x_283_, v___x_284_, v___x_279_,
    );
    return v___x_285_;
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0___boxed(
    mut v___x_286_: *mut crate::leanh::LeanObject,
    mut v_x1_287_: *mut crate::leanh::LeanObject,
    mut v_x2_288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_92__boxed_289_: u8 = 0;
    let mut v_res_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_92__boxed_289_ = (crate::leanh::lean_unbox(v___x_286_) as u8);
    v_res_290_ = l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0(
        v___x_92__boxed_289_,
        v_x1_287_,
        v_x2_288_,
    );
    crate::leanh::lean_dec_ref(v_x2_288_);
    return v_res_290_;
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_toByteArray(
    mut v_cb_310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_data_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: u8 = 0;
    v_data_311_ = crate::leanh::lean_ctor_get(v_cb_310_, 0);
    crate::leanh::lean_inc_ref(v_data_311_);
    v_size_312_ = crate::leanh::lean_ctor_get(v_cb_310_, 1);
    crate::leanh::lean_inc(v_size_312_);
    crate::leanh::lean_dec_ref(v_cb_310_);
    v___x_313_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_314_ = lean_array_get_size(v_data_311_);
    v___x_315_ = lean_nat_dec_eq(v___x_313_, v___x_314_);
    if v___x_315_ == 0 {
        let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_319_: u8 = 0;
        v___x_316_ = lean_mk_empty_byte_array(v_size_312_);
        crate::leanh::lean_dec(v_size_312_);
        v___x_317_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_318_ = l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9;
        v___x_319_ = lean_nat_dec_lt(v___x_317_, v___x_314_);
        if v___x_319_ == 0 {
            crate::leanh::lean_dec_ref(v_data_311_);
            return v___x_316_;
        } else {
            let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_322_: u8 = 0;
            v___x_320_ = crate::leanh::lean_box((v___x_315_) as usize);
            v___f_321_ = crate::leanh::lean_alloc_closure(
                l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0___boxed
                    as *mut core::ffi::c_void,
                3,
                1,
            );
            crate::leanh::lean_closure_set(v___f_321_, 0, v___x_320_);
            v___x_322_ = lean_nat_dec_le(v___x_314_, v___x_314_);
            if v___x_322_ == 0 {
                if v___x_319_ == 0 {
                    crate::leanh::lean_dec_ref(v___f_321_);
                    crate::leanh::lean_dec_ref(v_data_311_);
                    return v___x_316_;
                } else {
                    let mut v___x_323_: usize = 0;
                    let mut v___x_324_: usize = 0;
                    let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_323_ = 0usize;
                    v___x_324_ = lean_usize_of_nat(v___x_314_);
                    v___x_325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
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
                let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_326_ = 0usize;
                v___x_327_ = lean_usize_of_nat(v___x_314_);
                v___x_328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
        let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_size_312_);
        v___x_329_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_330_ = lean_array_fget(v_data_311_, v___x_329_);
        crate::leanh::lean_dec_ref(v_data_311_);
        return v___x_330_;
    }
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_ofByteArray(
    mut v_bs_331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_332_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_333_ = lean_mk_empty_array_with_capacity(v___x_332_);
    crate::leanh::lean_inc_ref(v_bs_331_);
    v___x_334_ = lean_array_push(v___x_333_, v_bs_331_);
    v___x_335_ = lean_byte_array_size(v_bs_331_);
    crate::leanh::lean_dec_ref(v_bs_331_);
    v___x_336_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_336_, 0, v___x_334_);
    crate::leanh::lean_ctor_set(v___x_336_, 1, v___x_335_);
    return v___x_336_;
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0(
    mut v_x1_337_: *mut crate::leanh::LeanObject,
    mut v_x2_338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_339_ = lean_byte_array_size(v_x2_338_);
    v___x_340_ = lean_nat_add(v_x1_337_, v___x_339_);
    return v___x_340_;
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0___boxed(
    mut v_x1_341_: *mut crate::leanh::LeanObject,
    mut v_x2_342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_343_ = l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0(v_x1_341_, v_x2_342_);
    crate::leanh::lean_dec_ref(v_x2_342_);
    crate::leanh::lean_dec(v_x1_341_);
    return v_res_343_;
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_ofArray(
    mut v_bs_345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: u8 = 0;
    v___x_346_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_347_ = lean_array_get_size(v_bs_345_);
    v___x_348_ = l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9;
    v___x_349_ = lean_nat_dec_lt(v___x_346_, v___x_347_);
    if v___x_349_ == 0 {
        let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_350_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_350_, 0, v_bs_345_);
        crate::leanh::lean_ctor_set(v___x_350_, 1, v___x_346_);
        return v___x_350_;
    } else {
        let mut v___f_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_352_: u8 = 0;
        v___f_351_ = l_Std_Http_Internal_ChunkedBuffer_ofArray___closed__0;
        v___x_352_ = lean_nat_dec_le(v___x_347_, v___x_347_);
        if v___x_352_ == 0 {
            if v___x_349_ == 0 {
                let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_353_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_353_, 0, v_bs_345_);
                crate::leanh::lean_ctor_set(v___x_353_, 1, v___x_346_);
                return v___x_353_;
            } else {
                let mut v___x_354_: usize = 0;
                let mut v___x_355_: usize = 0;
                let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_354_ = 0usize;
                v___x_355_ = lean_usize_of_nat(v___x_347_);
                crate::leanh::lean_inc_ref(v_bs_345_);
                v___x_356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_348_,
                    v___f_351_,
                    v_bs_345_,
                    v___x_354_,
                    v___x_355_,
                    v___x_346_,
                );
                v___x_357_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_357_, 0, v_bs_345_);
                crate::leanh::lean_ctor_set(v___x_357_, 1, v___x_356_);
                return v___x_357_;
            }
        } else {
            let mut v___x_358_: usize = 0;
            let mut v___x_359_: usize = 0;
            let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_358_ = 0usize;
            v___x_359_ = lean_usize_of_nat(v___x_347_);
            crate::leanh::lean_inc_ref(v_bs_345_);
            v___x_360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_348_,
                v___f_351_,
                v_bs_345_,
                v___x_358_,
                v___x_359_,
                v___x_346_,
            );
            v___x_361_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_361_, 0, v_bs_345_);
            crate::leanh::lean_ctor_set(v___x_361_, 1, v___x_360_);
            return v___x_361_;
        }
    }
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_isEmpty(
    mut v_bb_362_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_size_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: u8 = 0;
    v_size_363_ = crate::leanh::lean_ctor_get(v_bb_362_, 1);
    v___x_364_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_365_ = lean_nat_dec_eq(v_size_363_, v___x_364_);
    return v___x_365_;
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_isEmpty___boxed(
    mut v_bb_366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_367_: u8 = 0;
    let mut v_r_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_367_ = l_Std_Http_Internal_ChunkedBuffer_isEmpty(v_bb_366_);
    crate::leanh::lean_dec_ref(v_bb_366_);
    v_r_368_ = crate::leanh::lean_box((v_res_367_) as usize);
    return v_r_368_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Internal_ChunkedBuffer(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ByteArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Internal_ChunkedBuffer(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Internal_ChunkedBuffer(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ByteArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Internal_ChunkedBuffer(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Internal_ChunkedBuffer(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Http_Internal_ChunkedBuffer(builtin);
}

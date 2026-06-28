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
use crate::lean_imports_rs::Init::Data::ByteArray::Basic::lean_byte_array_copy_slice;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_to_utf8;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_uint32_to_uint8, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_byte_array_mk,
    lean_byte_array_size, lean_mk_empty_array_with_capacity, lean_mk_empty_byte_array,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_unbox,
    lean_unbox_uint32, lean_unsigned_to_nat,
};
pub static l_Std_Http_Internal_ChunkedBuffer_empty___closed__0_value: LeanArrayObject<0> =
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
static mut l_Std_Http_Internal_ChunkedBuffer_empty___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_empty___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_empty___closed__0_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Internal_ChunkedBuffer_empty___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Internal_ChunkedBuffer_empty: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__3_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__4_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__5_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__6_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__6_value)
        as *mut LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__7_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__7_value)
        as *mut LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__8_value: LeanCtorObject<5> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__7_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__8_value)
        as *mut LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__8_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9_value)
        as *mut LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_ofArray___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Internal_ChunkedBuffer_ofArray___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_ofArray___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Internal_ChunkedBuffer_instInhabited: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Internal_ChunkedBuffer_instEmptyCollection: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_empty___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_instCoeByteArray___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Internal_ChunkedBuffer_ofByteArray as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_ChunkedBuffer_instCoeByteArray___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_instCoeByteArray___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Internal_ChunkedBuffer_instCoeByteArray: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_instCoeByteArray___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Internal_ChunkedBuffer_instCoeArrayByteArray___closed__0_value:
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
    m_fun: l_Std_Http_Internal_ChunkedBuffer_ofArray as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Internal_ChunkedBuffer_instCoeArrayByteArray___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_instCoeArrayByteArray___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Internal_ChunkedBuffer_instCoeArrayByteArray: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Internal_ChunkedBuffer_instCoeArrayByteArray___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_push(
    mut v_c_194_: *mut LeanObject,
    mut v_b_195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_data_196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_200_: u8 = 0;
    let mut v___x_201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_207_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_data_196_ = lean_ctor_get(v_c_194_, 0);
                v_size_197_ = lean_ctor_get(v_c_194_, 1);
                v_isSharedCheck_207_ = (!lean_is_exclusive(v_c_194_)) as u8;
                if v_isSharedCheck_207_ == 0 {
                    v___x_199_ = v_c_194_;
                    v_isShared_200_ = v_isSharedCheck_207_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_size_197_);
                    lean_inc(v_data_196_);
                    lean_dec(v_c_194_);
                    v___x_199_ = lean_box(0);
                    v_isShared_200_ = v_isSharedCheck_207_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_b_195_);
                v___x_201_ = lean_array_push(v_data_196_, v_b_195_);
                v___x_202_ = lean_byte_array_size(v_b_195_);
                lean_dec_ref(v_b_195_);
                v___x_203_ = lean_nat_add(v_size_197_, v___x_202_);
                lean_dec(v_size_197_);
                if v_isShared_200_ == 0 {
                    lean_ctor_set(v___x_199_, 1, v___x_203_);
                    lean_ctor_set(v___x_199_, 0, v___x_201_);
                    v___x_205_ = v___x_199_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_201_);
                    lean_ctor_set(v_reuseFailAlloc_206_, 1, v___x_203_);
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
    mut v_buffer_208_: *mut LeanObject,
    mut v_data_209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_data_210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_214_: u8 = 0;
    let mut v___x_215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_221_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_data_210_ = lean_ctor_get(v_buffer_208_, 0);
                v_size_211_ = lean_ctor_get(v_buffer_208_, 1);
                v_isSharedCheck_221_ = (!lean_is_exclusive(v_buffer_208_)) as u8;
                if v_isSharedCheck_221_ == 0 {
                    v___x_213_ = v_buffer_208_;
                    v_isShared_214_ = v_isSharedCheck_221_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_size_211_);
                    lean_inc(v_data_210_);
                    lean_dec(v_buffer_208_);
                    v___x_213_ = lean_box(0);
                    v_isShared_214_ = v_isSharedCheck_221_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_data_209_);
                v___x_215_ = lean_array_push(v_data_210_, v_data_209_);
                v___x_216_ = lean_byte_array_size(v_data_209_);
                lean_dec_ref(v_data_209_);
                v___x_217_ = lean_nat_add(v_size_211_, v___x_216_);
                lean_dec(v_size_211_);
                if v_isShared_214_ == 0 {
                    lean_ctor_set(v___x_213_, 1, v___x_217_);
                    lean_ctor_set(v___x_213_, 0, v___x_215_);
                    v___x_219_ = v___x_213_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_215_);
                    lean_ctor_set(v_reuseFailAlloc_220_, 1, v___x_217_);
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
    mut v_buffer_222_: *mut LeanObject,
    mut v_data_223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_data_224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_230_: u8 = 0;
    let mut v___x_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_236_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_data_224_ = lean_ctor_get(v_buffer_222_, 0);
                lean_inc_ref(v_data_224_);
                v_size_225_ = lean_ctor_get(v_buffer_222_, 1);
                lean_inc(v_size_225_);
                lean_dec_ref(v_buffer_222_);
                v_data_226_ = lean_ctor_get(v_data_223_, 0);
                v_size_227_ = lean_ctor_get(v_data_223_, 1);
                v_isSharedCheck_236_ = (!lean_is_exclusive(v_data_223_)) as u8;
                if v_isSharedCheck_236_ == 0 {
                    v___x_229_ = v_data_223_;
                    v_isShared_230_ = v_isSharedCheck_236_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_size_227_);
                    lean_inc(v_data_226_);
                    lean_dec(v_data_223_);
                    v___x_229_ = lean_box(0);
                    v_isShared_230_ = v_isSharedCheck_236_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_231_ = l_Array_append___redArg(v_data_224_, v_data_226_);
                lean_dec_ref(v_data_226_);
                v___x_232_ = lean_nat_add(v_size_225_, v_size_227_);
                lean_dec(v_size_227_);
                lean_dec(v_size_225_);
                if v_isShared_230_ == 0 {
                    lean_ctor_set(v___x_229_, 1, v___x_232_);
                    lean_ctor_set(v___x_229_, 0, v___x_231_);
                    v___x_234_ = v___x_229_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_231_);
                    lean_ctor_set(v_reuseFailAlloc_235_, 1, v___x_232_);
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
    mut v_buffer_237_: *mut LeanObject,
    mut v_data_238_: u32,
) -> *mut LeanObject {
    let mut v_data_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_243_: u8 = 0;
    let mut v___x_244_: u8 = 0;
    let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_256_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_data_239_ = lean_ctor_get(v_buffer_237_, 0);
                v_size_240_ = lean_ctor_get(v_buffer_237_, 1);
                v_isSharedCheck_256_ = (!lean_is_exclusive(v_buffer_237_)) as u8;
                if v_isSharedCheck_256_ == 0 {
                    v___x_242_ = v_buffer_237_;
                    v_isShared_243_ = v_isSharedCheck_256_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_size_240_);
                    lean_inc(v_data_239_);
                    lean_dec(v_buffer_237_);
                    v___x_242_ = lean_box(0);
                    v_isShared_243_ = v_isSharedCheck_256_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_244_ = lean_uint32_to_uint8(v_data_238_);
                v___x_245_ = lean_unsigned_to_nat(1);
                v___x_246_ = lean_mk_empty_array_with_capacity(v___x_245_);
                v___x_247_ = lean_box((v___x_244_) as usize);
                v___x_248_ = lean_array_push(v___x_246_, v___x_247_);
                v___x_249_ = lean_byte_array_mk(v___x_248_);
                lean_inc_ref(v___x_249_);
                v___x_250_ = lean_array_push(v_data_239_, v___x_249_);
                v___x_251_ = lean_byte_array_size(v___x_249_);
                lean_dec_ref(v___x_249_);
                v___x_252_ = lean_nat_add(v_size_240_, v___x_251_);
                lean_dec(v_size_240_);
                if v_isShared_243_ == 0 {
                    lean_ctor_set(v___x_242_, 1, v___x_252_);
                    lean_ctor_set(v___x_242_, 0, v___x_250_);
                    v___x_254_ = v___x_242_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_250_);
                    lean_ctor_set(v_reuseFailAlloc_255_, 1, v___x_252_);
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
    mut v_buffer_257_: *mut LeanObject,
    mut v_data_258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_data_boxed_259_: u32 = 0;
    let mut v_res_260_: *mut LeanObject = core::ptr::null_mut();
    v_data_boxed_259_ = lean_unbox_uint32(v_data_258_);
    lean_dec(v_data_258_);
    v_res_260_ = l_Std_Http_Internal_ChunkedBuffer_writeChar(v_buffer_257_, v_data_boxed_259_);
    return v_res_260_;
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_writeString(
    mut v_buffer_261_: *mut LeanObject,
    mut v_data_262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_data_263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_267_: u8 = 0;
    let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_data_263_ = lean_ctor_get(v_buffer_261_, 0);
                v_size_264_ = lean_ctor_get(v_buffer_261_, 1);
                v_isSharedCheck_275_ = (!lean_is_exclusive(v_buffer_261_)) as u8;
                if v_isSharedCheck_275_ == 0 {
                    v___x_266_ = v_buffer_261_;
                    v_isShared_267_ = v_isSharedCheck_275_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_size_264_);
                    lean_inc(v_data_263_);
                    lean_dec(v_buffer_261_);
                    v___x_266_ = lean_box(0);
                    v_isShared_267_ = v_isSharedCheck_275_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_268_ = lean_string_to_utf8(v_data_262_);
                lean_inc_ref(v___x_268_);
                v___x_269_ = lean_array_push(v_data_263_, v___x_268_);
                v___x_270_ = lean_byte_array_size(v___x_268_);
                lean_dec_ref(v___x_268_);
                v___x_271_ = lean_nat_add(v_size_264_, v___x_270_);
                lean_dec(v_size_264_);
                if v_isShared_267_ == 0 {
                    lean_ctor_set(v___x_266_, 1, v___x_271_);
                    lean_ctor_set(v___x_266_, 0, v___x_269_);
                    v___x_273_ = v___x_266_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_269_);
                    lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_271_);
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
    mut v_buffer_276_: *mut LeanObject,
    mut v_data_277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_278_: *mut LeanObject = core::ptr::null_mut();
    v_res_278_ = l_Std_Http_Internal_ChunkedBuffer_writeString(v_buffer_276_, v_data_277_);
    lean_dec_ref(v_data_277_);
    return v_res_278_;
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0(
    mut v___x_279_: u8,
    mut v_x1_280_: *mut LeanObject,
    mut v_x2_281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut LeanObject = core::ptr::null_mut();
    v___x_282_ = lean_unsigned_to_nat(0);
    v___x_283_ = lean_byte_array_size(v_x1_280_);
    v___x_284_ = lean_byte_array_size(v_x2_281_);
    v___x_285_ = lean_byte_array_copy_slice(
        v_x2_281_, v___x_282_, v_x1_280_, v___x_283_, v___x_284_, v___x_279_,
    );
    return v___x_285_;
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0___boxed(
    mut v___x_286_: *mut LeanObject,
    mut v_x1_287_: *mut LeanObject,
    mut v_x2_288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_92__boxed_289_: u8 = 0;
    let mut v_res_290_: *mut LeanObject = core::ptr::null_mut();
    v___x_92__boxed_289_ = (lean_unbox(v___x_286_) as u8);
    v_res_290_ = l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0(
        v___x_92__boxed_289_,
        v_x1_287_,
        v_x2_288_,
    );
    lean_dec_ref(v_x2_288_);
    return v_res_290_;
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_toByteArray(
    mut v_cb_310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_data_311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_315_: u8 = 0;
    v_data_311_ = lean_ctor_get(v_cb_310_, 0);
    lean_inc_ref(v_data_311_);
    v_size_312_ = lean_ctor_get(v_cb_310_, 1);
    lean_inc(v_size_312_);
    lean_dec_ref(v_cb_310_);
    v___x_313_ = lean_unsigned_to_nat(1);
    v___x_314_ = lean_array_get_size(v_data_311_);
    v___x_315_ = lean_nat_dec_eq(v___x_313_, v___x_314_);
    if v___x_315_ == 0 {
        let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_319_: u8 = 0;
        v___x_316_ = lean_mk_empty_byte_array(v_size_312_);
        lean_dec(v_size_312_);
        v___x_317_ = lean_unsigned_to_nat(0);
        v___x_318_ = l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9;
        v___x_319_ = lean_nat_dec_lt(v___x_317_, v___x_314_);
        if v___x_319_ == 0 {
            lean_dec_ref(v_data_311_);
            return v___x_316_;
        } else {
            let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_321_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_322_: u8 = 0;
            v___x_320_ = lean_box((v___x_315_) as usize);
            v___f_321_ = lean_alloc_closure(
                l_Std_Http_Internal_ChunkedBuffer_toByteArray___lam__0___boxed
                    as *mut core::ffi::c_void,
                3,
                1,
            );
            lean_closure_set(v___f_321_, 0, v___x_320_);
            v___x_322_ = lean_nat_dec_le(v___x_314_, v___x_314_);
            if v___x_322_ == 0 {
                if v___x_319_ == 0 {
                    lean_dec_ref(v___f_321_);
                    lean_dec_ref(v_data_311_);
                    return v___x_316_;
                } else {
                    let mut v___x_323_: usize = 0;
                    let mut v___x_324_: usize = 0;
                    let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
                    v___x_323_ = 0usize;
                    v___x_324_ = lean_usize_of_nat(v___x_314_);
                    v___x_325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
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
                let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
                v___x_326_ = 0usize;
                v___x_327_ = lean_usize_of_nat(v___x_314_);
                v___x_328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
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
        let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_size_312_);
        v___x_329_ = lean_unsigned_to_nat(0);
        v___x_330_ = lean_array_fget(v_data_311_, v___x_329_);
        lean_dec_ref(v_data_311_);
        return v___x_330_;
    }
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_ofByteArray(
    mut v_bs_331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
    v___x_332_ = lean_unsigned_to_nat(1);
    v___x_333_ = lean_mk_empty_array_with_capacity(v___x_332_);
    lean_inc_ref(v_bs_331_);
    v___x_334_ = lean_array_push(v___x_333_, v_bs_331_);
    v___x_335_ = lean_byte_array_size(v_bs_331_);
    lean_dec_ref(v_bs_331_);
    v___x_336_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_336_, 0, v___x_334_);
    lean_ctor_set(v___x_336_, 1, v___x_335_);
    return v___x_336_;
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0(
    mut v_x1_337_: *mut LeanObject,
    mut v_x2_338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
    v___x_339_ = lean_byte_array_size(v_x2_338_);
    v___x_340_ = lean_nat_add(v_x1_337_, v___x_339_);
    return v___x_340_;
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0___boxed(
    mut v_x1_341_: *mut LeanObject,
    mut v_x2_342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_343_: *mut LeanObject = core::ptr::null_mut();
    v_res_343_ = l_Std_Http_Internal_ChunkedBuffer_ofArray___lam__0(v_x1_341_, v_x2_342_);
    lean_dec_ref(v_x2_342_);
    lean_dec(v_x1_341_);
    return v_res_343_;
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_ofArray(
    mut v_bs_345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_349_: u8 = 0;
    v___x_346_ = lean_unsigned_to_nat(0);
    v___x_347_ = lean_array_get_size(v_bs_345_);
    v___x_348_ = l_Std_Http_Internal_ChunkedBuffer_toByteArray___closed__9;
    v___x_349_ = lean_nat_dec_lt(v___x_346_, v___x_347_);
    if v___x_349_ == 0 {
        let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
        v___x_350_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_350_, 0, v_bs_345_);
        lean_ctor_set(v___x_350_, 1, v___x_346_);
        return v___x_350_;
    } else {
        let mut v___f_351_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_352_: u8 = 0;
        v___f_351_ = l_Std_Http_Internal_ChunkedBuffer_ofArray___closed__0;
        v___x_352_ = lean_nat_dec_le(v___x_347_, v___x_347_);
        if v___x_352_ == 0 {
            if v___x_349_ == 0 {
                let mut v___x_353_: *mut LeanObject = core::ptr::null_mut();
                v___x_353_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_353_, 0, v_bs_345_);
                lean_ctor_set(v___x_353_, 1, v___x_346_);
                return v___x_353_;
            } else {
                let mut v___x_354_: usize = 0;
                let mut v___x_355_: usize = 0;
                let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
                v___x_354_ = 0usize;
                v___x_355_ = lean_usize_of_nat(v___x_347_);
                lean_inc_ref(v_bs_345_);
                v___x_356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_348_,
                    v___f_351_,
                    v_bs_345_,
                    v___x_354_,
                    v___x_355_,
                    v___x_346_,
                );
                v___x_357_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_357_, 0, v_bs_345_);
                lean_ctor_set(v___x_357_, 1, v___x_356_);
                return v___x_357_;
            }
        } else {
            let mut v___x_358_: usize = 0;
            let mut v___x_359_: usize = 0;
            let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
            v___x_358_ = 0usize;
            v___x_359_ = lean_usize_of_nat(v___x_347_);
            lean_inc_ref(v_bs_345_);
            v___x_360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v___x_348_,
                v___f_351_,
                v_bs_345_,
                v___x_358_,
                v___x_359_,
                v___x_346_,
            );
            v___x_361_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_361_, 0, v_bs_345_);
            lean_ctor_set(v___x_361_, 1, v___x_360_);
            return v___x_361_;
        }
    }
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_isEmpty(mut v_bb_362_: *mut LeanObject) -> u8 {
    let mut v_size_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_365_: u8 = 0;
    v_size_363_ = lean_ctor_get(v_bb_362_, 1);
    v___x_364_ = lean_unsigned_to_nat(0);
    v___x_365_ = lean_nat_dec_eq(v_size_363_, v___x_364_);
    return v___x_365_;
}
pub unsafe fn l_Std_Http_Internal_ChunkedBuffer_isEmpty___boxed(
    mut v_bb_366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_367_: u8 = 0;
    let mut v_r_368_: *mut LeanObject = core::ptr::null_mut();
    v_res_367_ = l_Std_Http_Internal_ChunkedBuffer_isEmpty(v_bb_366_);
    lean_dec_ref(v_bb_366_);
    v_r_368_ = lean_box((v_res_367_) as usize);
    return v_r_368_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Internal_ChunkedBuffer(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ByteArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Internal_ChunkedBuffer(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Internal_ChunkedBuffer(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ByteArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Internal_ChunkedBuffer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Http_Internal_ChunkedBuffer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Http_Internal_ChunkedBuffer(builtin);
}

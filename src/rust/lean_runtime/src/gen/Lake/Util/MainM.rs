// Lean compiler output
// Module: Lake.Util.MainM
// Imports: Lake.Util.Log Lake.Util.Exit
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::System::IO::l_instMonadBaseIO;
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lake::Util::Exit::{
    initialize_Lake_Util_Exit, runtime_initialize_Lake_Util_Exit,
};
use crate::r#gen::Lake::Util::Log::{
    initialize_Lake_Util_Log, l_Lake_AnsiMode_isEnabled, l_Lake_Log_maxLv, l_Lake_OutStream_get,
    l_Lake_OutStream_logEntry, l_Lake_instOrdLogLevel_ord, l_Lake_logToStream,
    runtime_initialize_Lake_Util_Log,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_mk_empty_array_with_capacity, lean_nat_dec_le, lean_nat_dec_lt,
    lean_uint32_dec_eq, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_box_uint32, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_tag, lean_unbox,
    lean_unbox_uint32, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lake_instMonadMainM___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instMonadMainM___aux__1___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instMonadMainM___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadMainM___closed__0_value) as *mut LeanObject;
pub static l_Lake_instMonadMainM___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instMonadMainM___aux__3___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instMonadMainM___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadMainM___closed__1_value) as *mut LeanObject;
pub static l_Lake_instMonadMainM___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instMonadMainM___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_instMonadMainM___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instMonadMainM___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadMainM___closed__2_value) as *mut LeanObject;
pub static l_Lake_instMonadMainM___closed__3_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instMonadMainM___aux__5___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instMonadMainM___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadMainM___closed__3_value) as *mut LeanObject;
pub static l_Lake_instMonadMainM___closed__4_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instMonadMainM___aux__7___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instMonadMainM___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadMainM___closed__4_value) as *mut LeanObject;
pub static l_Lake_instMonadMainM___closed__5_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instMonadMainM___aux__9___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instMonadMainM___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadMainM___closed__5_value) as *mut LeanObject;
pub static l_Lake_instMonadMainM___closed__6_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instMonadMainM___aux__11___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instMonadMainM___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadMainM___closed__6_value) as *mut LeanObject;
pub static l_Lake_instMonadMainM___closed__7_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instMonadMainM___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_instMonadMainM___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_instMonadMainM___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_instMonadMainM___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_instMonadMainM___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instMonadMainM___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadMainM___closed__7_value) as *mut LeanObject;
pub static l_Lake_instMonadMainM___closed__8_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instMonadMainM___aux__13___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instMonadMainM___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadMainM___closed__8_value) as *mut LeanObject;
pub static l_Lake_instMonadMainM___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instMonadMainM___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_instMonadMainM___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instMonadMainM___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadMainM___closed__9_value) as *mut LeanObject;
pub static mut l_Lake_instMonadMainM: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadMainM___closed__9_value) as *mut LeanObject;
pub static l_Lake_instMonadFinallyMainM___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadFinallyMainM___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadFinallyMainM___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadFinallyMainM___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instMonadFinallyMainM: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadFinallyMainM___closed__0_value) as *mut LeanObject;
pub static l_Lake_instMonadLiftBaseIOMainM___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadLiftBaseIOMainM___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadLiftBaseIOMainM___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadLiftBaseIOMainM___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instMonadLiftBaseIOMainM: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadLiftBaseIOMainM___closed__0_value) as *mut LeanObject;
pub static l_Lake_MainM_instMonadExit___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_MainM_exit___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_MainM_instMonadExit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_instMonadExit___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_MainM_instMonadExit: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_instMonadExit___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_MainM_tryCatchError___redArg___boxed__const__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_MainM_failure___redArg___boxed__const__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__0_value:
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
    m_fun: l_Lake_MainM_failure___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__1_value:
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
    m_fun: l_Lake_MainM_orElse___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__1_value)
        as *mut LeanObject;
pub static mut l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_MainM_instMonadLog___closed__0_value: LeanClosureObject<3> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_MainM_instMonadLog___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 3,
    m_objs: [
        (((1 as usize) << 1) | 1) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_MainM_instMonadLog___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_instMonadLog___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_MainM_instMonadLog: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_instMonadLog___closed__0_value) as *mut LeanObject;
pub static l_Lake_MainM_instMonadError___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_MainM_instMonadError___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_MainM_instMonadError___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_instMonadError___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_MainM_instMonadError: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_instMonadError___closed__0_value) as *mut LeanObject;
pub static l_Lake_MainM_instMonadLiftIO___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_MainM_instMonadLiftIO___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_MainM_instMonadLiftIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_instMonadLiftIO___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_MainM_instMonadLiftIO: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_instMonadLiftIO___closed__0_value) as *mut LeanObject;
pub static l_Lake_MainM_runLogIO___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lake_MainM_runLogIO___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_runLogIO___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_MainM_instMonadLiftLogIO___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_MainM_liftLogIO___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_MainM_instMonadLiftLogIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_instMonadLiftLogIO___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_MainM_instMonadLiftLogIO: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_instMonadLiftLogIO___closed__0_value) as *mut LeanObject;
pub static l_Lake_MainM_instMonadLiftLoggerIO___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_MainM_liftLoggerIO___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_MainM_instMonadLiftLoggerIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_instMonadLiftLoggerIO___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_MainM_instMonadLiftLoggerIO: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_instMonadLiftLoggerIO___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lake_instMonadMainM___aux__1___redArg(
    mut v_a_1239_: *mut LeanObject,
    mut v_a_1240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1246_: u8 = 0;
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1251_: u8 = 0;
    let mut v_a_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1255_: u8 = 0;
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1259_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1242_ = lean_apply_1(v_a_1240_, lean_box(0));
                if lean_obj_tag(v___x_1242_) == 0 {
                    v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
                    v_isSharedCheck_1251_ = (!lean_is_exclusive(v___x_1242_)) as u8;
                    if v_isSharedCheck_1251_ == 0 {
                        v___x_1245_ = v___x_1242_;
                        v_isShared_1246_ = v_isSharedCheck_1251_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1243_);
                        lean_dec(v___x_1242_);
                        v___x_1245_ = lean_box(0);
                        v_isShared_1246_ = v_isSharedCheck_1251_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1239_);
                    v_a_1252_ = lean_ctor_get(v___x_1242_, 0);
                    v_isSharedCheck_1259_ = (!lean_is_exclusive(v___x_1242_)) as u8;
                    if v_isSharedCheck_1259_ == 0 {
                        v___x_1254_ = v___x_1242_;
                        v_isShared_1255_ = v_isSharedCheck_1259_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1252_);
                        lean_dec(v___x_1242_);
                        v___x_1254_ = lean_box(0);
                        v_isShared_1255_ = v_isSharedCheck_1259_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1247_ = lean_apply_1(v_a_1239_, v_a_1243_);
                if v_isShared_1246_ == 0 {
                    lean_ctor_set(v___x_1245_, 0, v___x_1247_);
                    v___x_1249_ = v___x_1245_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1247_);
                    v___x_1249_ = v_reuseFailAlloc_1250_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1249_;
            }
            3 => {
                if v_isShared_1255_ == 0 {
                    v___x_1257_ = v___x_1254_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
                    v___x_1257_ = v_reuseFailAlloc_1258_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1257_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadMainM___aux__1___redArg___boxed(
    mut v_a_1260_: *mut LeanObject,
    mut v_a_1261_: *mut LeanObject,
    mut v_a_1262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1263_: *mut LeanObject = core::ptr::null_mut();
    v_res_1263_ = l_Lake_instMonadMainM___aux__1___redArg(v_a_1260_, v_a_1261_);
    return v_res_1263_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__1(
    mut v_00_u03b1_1264_: *mut LeanObject,
    mut v_00_u03b2_1265_: *mut LeanObject,
    mut v_a_1266_: *mut LeanObject,
    mut v_a_1267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1273_: u8 = 0;
    let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1278_: u8 = 0;
    let mut v_a_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1282_: u8 = 0;
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1286_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1269_ = lean_apply_1(v_a_1267_, lean_box(0));
                if lean_obj_tag(v___x_1269_) == 0 {
                    v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
                    v_isSharedCheck_1278_ = (!lean_is_exclusive(v___x_1269_)) as u8;
                    if v_isSharedCheck_1278_ == 0 {
                        v___x_1272_ = v___x_1269_;
                        v_isShared_1273_ = v_isSharedCheck_1278_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1270_);
                        lean_dec(v___x_1269_);
                        v___x_1272_ = lean_box(0);
                        v_isShared_1273_ = v_isSharedCheck_1278_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1266_);
                    v_a_1279_ = lean_ctor_get(v___x_1269_, 0);
                    v_isSharedCheck_1286_ = (!lean_is_exclusive(v___x_1269_)) as u8;
                    if v_isSharedCheck_1286_ == 0 {
                        v___x_1281_ = v___x_1269_;
                        v_isShared_1282_ = v_isSharedCheck_1286_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1279_);
                        lean_dec(v___x_1269_);
                        v___x_1281_ = lean_box(0);
                        v_isShared_1282_ = v_isSharedCheck_1286_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1274_ = lean_apply_1(v_a_1266_, v_a_1270_);
                if v_isShared_1273_ == 0 {
                    lean_ctor_set(v___x_1272_, 0, v___x_1274_);
                    v___x_1276_ = v___x_1272_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1274_);
                    v___x_1276_ = v_reuseFailAlloc_1277_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1276_;
            }
            3 => {
                if v_isShared_1282_ == 0 {
                    v___x_1284_ = v___x_1281_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
                    v___x_1284_ = v_reuseFailAlloc_1285_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1284_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadMainM___aux__1___boxed(
    mut v_00_u03b1_1287_: *mut LeanObject,
    mut v_00_u03b2_1288_: *mut LeanObject,
    mut v_a_1289_: *mut LeanObject,
    mut v_a_1290_: *mut LeanObject,
    mut v_a_1291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1292_: *mut LeanObject = core::ptr::null_mut();
    v_res_1292_ =
        l_Lake_instMonadMainM___aux__1(v_00_u03b1_1287_, v_00_u03b2_1288_, v_a_1289_, v_a_1290_);
    return v_res_1292_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__3___redArg(
    mut v_a_1293_: *mut LeanObject,
    mut v_a_1294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1299_: u8 = 0;
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1303_: u8 = 0;
    let mut v_unused_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1308_: u8 = 0;
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1312_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1296_ = lean_apply_1(v_a_1294_, lean_box(0));
                if lean_obj_tag(v___x_1296_) == 0 {
                    v_isSharedCheck_1303_ = (!lean_is_exclusive(v___x_1296_)) as u8;
                    if v_isSharedCheck_1303_ == 0 {
                        v_unused_1304_ = lean_ctor_get(v___x_1296_, 0);
                        lean_dec(v_unused_1304_);
                        v___x_1298_ = v___x_1296_;
                        v_isShared_1299_ = v_isSharedCheck_1303_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1296_);
                        v___x_1298_ = lean_box(0);
                        v_isShared_1299_ = v_isSharedCheck_1303_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1293_);
                    v_a_1305_ = lean_ctor_get(v___x_1296_, 0);
                    v_isSharedCheck_1312_ = (!lean_is_exclusive(v___x_1296_)) as u8;
                    if v_isSharedCheck_1312_ == 0 {
                        v___x_1307_ = v___x_1296_;
                        v_isShared_1308_ = v_isSharedCheck_1312_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1305_);
                        lean_dec(v___x_1296_);
                        v___x_1307_ = lean_box(0);
                        v_isShared_1308_ = v_isSharedCheck_1312_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1299_ == 0 {
                    lean_ctor_set(v___x_1298_, 0, v_a_1293_);
                    v___x_1301_ = v___x_1298_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1293_);
                    v___x_1301_ = v_reuseFailAlloc_1302_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1301_;
            }
            3 => {
                if v_isShared_1308_ == 0 {
                    v___x_1310_ = v___x_1307_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
                    v___x_1310_ = v_reuseFailAlloc_1311_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1310_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadMainM___aux__3___redArg___boxed(
    mut v_a_1313_: *mut LeanObject,
    mut v_a_1314_: *mut LeanObject,
    mut v_a_1315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1316_: *mut LeanObject = core::ptr::null_mut();
    v_res_1316_ = l_Lake_instMonadMainM___aux__3___redArg(v_a_1313_, v_a_1314_);
    return v_res_1316_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__3(
    mut v_00_u03b1_1317_: *mut LeanObject,
    mut v_00_u03b2_1318_: *mut LeanObject,
    mut v_a_1319_: *mut LeanObject,
    mut v_a_1320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1325_: u8 = 0;
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1329_: u8 = 0;
    let mut v_unused_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1334_: u8 = 0;
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1338_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1322_ = lean_apply_1(v_a_1320_, lean_box(0));
                if lean_obj_tag(v___x_1322_) == 0 {
                    v_isSharedCheck_1329_ = (!lean_is_exclusive(v___x_1322_)) as u8;
                    if v_isSharedCheck_1329_ == 0 {
                        v_unused_1330_ = lean_ctor_get(v___x_1322_, 0);
                        lean_dec(v_unused_1330_);
                        v___x_1324_ = v___x_1322_;
                        v_isShared_1325_ = v_isSharedCheck_1329_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1322_);
                        v___x_1324_ = lean_box(0);
                        v_isShared_1325_ = v_isSharedCheck_1329_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1319_);
                    v_a_1331_ = lean_ctor_get(v___x_1322_, 0);
                    v_isSharedCheck_1338_ = (!lean_is_exclusive(v___x_1322_)) as u8;
                    if v_isSharedCheck_1338_ == 0 {
                        v___x_1333_ = v___x_1322_;
                        v_isShared_1334_ = v_isSharedCheck_1338_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1331_);
                        lean_dec(v___x_1322_);
                        v___x_1333_ = lean_box(0);
                        v_isShared_1334_ = v_isSharedCheck_1338_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1325_ == 0 {
                    lean_ctor_set(v___x_1324_, 0, v_a_1319_);
                    v___x_1327_ = v___x_1324_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1319_);
                    v___x_1327_ = v_reuseFailAlloc_1328_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1327_;
            }
            3 => {
                if v_isShared_1334_ == 0 {
                    v___x_1336_ = v___x_1333_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
                    v___x_1336_ = v_reuseFailAlloc_1337_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1336_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadMainM___aux__3___boxed(
    mut v_00_u03b1_1339_: *mut LeanObject,
    mut v_00_u03b2_1340_: *mut LeanObject,
    mut v_a_1341_: *mut LeanObject,
    mut v_a_1342_: *mut LeanObject,
    mut v_a_1343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1344_: *mut LeanObject = core::ptr::null_mut();
    v_res_1344_ =
        l_Lake_instMonadMainM___aux__3(v_00_u03b1_1339_, v_00_u03b2_1340_, v_a_1341_, v_a_1342_);
    return v_res_1344_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__5___redArg(
    mut v_a_1345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    v___x_1347_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1347_, 0, v_a_1345_);
    return v___x_1347_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__5___redArg___boxed(
    mut v_a_1348_: *mut LeanObject,
    mut v_a_1349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1350_: *mut LeanObject = core::ptr::null_mut();
    v_res_1350_ = l_Lake_instMonadMainM___aux__5___redArg(v_a_1348_);
    return v_res_1350_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__5(
    mut v_00_u03b1_1351_: *mut LeanObject,
    mut v_a_1352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    v___x_1354_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1354_, 0, v_a_1352_);
    return v___x_1354_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__5___boxed(
    mut v_00_u03b1_1355_: *mut LeanObject,
    mut v_a_1356_: *mut LeanObject,
    mut v_a_1357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1358_: *mut LeanObject = core::ptr::null_mut();
    v_res_1358_ = l_Lake_instMonadMainM___aux__5(v_00_u03b1_1355_, v_a_1356_);
    return v_res_1358_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__7___redArg(
    mut v_a_1359_: *mut LeanObject,
    mut v_a_1360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1369_: u8 = 0;
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1374_: u8 = 0;
    let mut v_a_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1378_: u8 = 0;
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1382_: u8 = 0;
    let mut v_a_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1386_: u8 = 0;
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1390_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1362_ = lean_apply_1(v_a_1359_, lean_box(0));
                if lean_obj_tag(v___x_1362_) == 0 {
                    v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
                    lean_inc(v_a_1363_);
                    lean_dec_ref_known(v___x_1362_, 1);
                    v___x_1364_ = lean_box(0);
                    v___x_1365_ = lean_apply_2(v_a_1360_, v___x_1364_, lean_box(0));
                    if lean_obj_tag(v___x_1365_) == 0 {
                        v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
                        v_isSharedCheck_1374_ = (!lean_is_exclusive(v___x_1365_)) as u8;
                        if v_isSharedCheck_1374_ == 0 {
                            v___x_1368_ = v___x_1365_;
                            v_isShared_1369_ = v_isSharedCheck_1374_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1366_);
                            lean_dec(v___x_1365_);
                            v___x_1368_ = lean_box(0);
                            v_isShared_1369_ = v_isSharedCheck_1374_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1363_);
                        v_a_1375_ = lean_ctor_get(v___x_1365_, 0);
                        v_isSharedCheck_1382_ = (!lean_is_exclusive(v___x_1365_)) as u8;
                        if v_isSharedCheck_1382_ == 0 {
                            v___x_1377_ = v___x_1365_;
                            v_isShared_1378_ = v_isSharedCheck_1382_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1375_);
                            lean_dec(v___x_1365_);
                            v___x_1377_ = lean_box(0);
                            v_isShared_1378_ = v_isSharedCheck_1382_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_a_1360_);
                    v_a_1383_ = lean_ctor_get(v___x_1362_, 0);
                    v_isSharedCheck_1390_ = (!lean_is_exclusive(v___x_1362_)) as u8;
                    if v_isSharedCheck_1390_ == 0 {
                        v___x_1385_ = v___x_1362_;
                        v_isShared_1386_ = v_isSharedCheck_1390_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1383_);
                        lean_dec(v___x_1362_);
                        v___x_1385_ = lean_box(0);
                        v_isShared_1386_ = v_isSharedCheck_1390_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1370_ = lean_apply_1(v_a_1363_, v_a_1366_);
                if v_isShared_1369_ == 0 {
                    lean_ctor_set(v___x_1368_, 0, v___x_1370_);
                    v___x_1372_ = v___x_1368_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
                    v___x_1372_ = v_reuseFailAlloc_1373_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1372_;
            }
            3 => {
                if v_isShared_1378_ == 0 {
                    v___x_1380_ = v___x_1377_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1375_);
                    v___x_1380_ = v_reuseFailAlloc_1381_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1380_;
            }
            5 => {
                if v_isShared_1386_ == 0 {
                    v___x_1388_ = v___x_1385_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
                    v___x_1388_ = v_reuseFailAlloc_1389_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1388_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadMainM___aux__7___redArg___boxed(
    mut v_a_1391_: *mut LeanObject,
    mut v_a_1392_: *mut LeanObject,
    mut v_a_1393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1394_: *mut LeanObject = core::ptr::null_mut();
    v_res_1394_ = l_Lake_instMonadMainM___aux__7___redArg(v_a_1391_, v_a_1392_);
    return v_res_1394_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__7(
    mut v_00_u03b1_1395_: *mut LeanObject,
    mut v_00_u03b2_1396_: *mut LeanObject,
    mut v_a_1397_: *mut LeanObject,
    mut v_a_1398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1407_: u8 = 0;
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1412_: u8 = 0;
    let mut v_a_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1416_: u8 = 0;
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1420_: u8 = 0;
    let mut v_a_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1424_: u8 = 0;
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1428_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1400_ = lean_apply_1(v_a_1397_, lean_box(0));
                if lean_obj_tag(v___x_1400_) == 0 {
                    v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
                    lean_inc(v_a_1401_);
                    lean_dec_ref_known(v___x_1400_, 1);
                    v___x_1402_ = lean_box(0);
                    v___x_1403_ = lean_apply_2(v_a_1398_, v___x_1402_, lean_box(0));
                    if lean_obj_tag(v___x_1403_) == 0 {
                        v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
                        v_isSharedCheck_1412_ = (!lean_is_exclusive(v___x_1403_)) as u8;
                        if v_isSharedCheck_1412_ == 0 {
                            v___x_1406_ = v___x_1403_;
                            v_isShared_1407_ = v_isSharedCheck_1412_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1404_);
                            lean_dec(v___x_1403_);
                            v___x_1406_ = lean_box(0);
                            v_isShared_1407_ = v_isSharedCheck_1412_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1401_);
                        v_a_1413_ = lean_ctor_get(v___x_1403_, 0);
                        v_isSharedCheck_1420_ = (!lean_is_exclusive(v___x_1403_)) as u8;
                        if v_isSharedCheck_1420_ == 0 {
                            v___x_1415_ = v___x_1403_;
                            v_isShared_1416_ = v_isSharedCheck_1420_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1413_);
                            lean_dec(v___x_1403_);
                            v___x_1415_ = lean_box(0);
                            v_isShared_1416_ = v_isSharedCheck_1420_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_a_1398_);
                    v_a_1421_ = lean_ctor_get(v___x_1400_, 0);
                    v_isSharedCheck_1428_ = (!lean_is_exclusive(v___x_1400_)) as u8;
                    if v_isSharedCheck_1428_ == 0 {
                        v___x_1423_ = v___x_1400_;
                        v_isShared_1424_ = v_isSharedCheck_1428_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1421_);
                        lean_dec(v___x_1400_);
                        v___x_1423_ = lean_box(0);
                        v_isShared_1424_ = v_isSharedCheck_1428_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1408_ = lean_apply_1(v_a_1401_, v_a_1404_);
                if v_isShared_1407_ == 0 {
                    lean_ctor_set(v___x_1406_, 0, v___x_1408_);
                    v___x_1410_ = v___x_1406_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1408_);
                    v___x_1410_ = v_reuseFailAlloc_1411_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1410_;
            }
            3 => {
                if v_isShared_1416_ == 0 {
                    v___x_1418_ = v___x_1415_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
                    v___x_1418_ = v_reuseFailAlloc_1419_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1418_;
            }
            5 => {
                if v_isShared_1424_ == 0 {
                    v___x_1426_ = v___x_1423_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
                    v___x_1426_ = v_reuseFailAlloc_1427_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1426_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadMainM___aux__7___boxed(
    mut v_00_u03b1_1429_: *mut LeanObject,
    mut v_00_u03b2_1430_: *mut LeanObject,
    mut v_a_1431_: *mut LeanObject,
    mut v_a_1432_: *mut LeanObject,
    mut v_a_1433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1434_: *mut LeanObject = core::ptr::null_mut();
    v_res_1434_ =
        l_Lake_instMonadMainM___aux__7(v_00_u03b1_1429_, v_00_u03b2_1430_, v_a_1431_, v_a_1432_);
    return v_res_1434_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__9___redArg(
    mut v_a_1435_: *mut LeanObject,
    mut v_a_1436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1444_: u8 = 0;
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1448_: u8 = 0;
    let mut v_unused_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1453_: u8 = 0;
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1457_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1438_ = lean_apply_1(v_a_1435_, lean_box(0));
                if lean_obj_tag(v___x_1438_) == 0 {
                    v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
                    lean_inc(v_a_1439_);
                    lean_dec_ref_known(v___x_1438_, 1);
                    v___x_1440_ = lean_box(0);
                    v___x_1441_ = lean_apply_2(v_a_1436_, v___x_1440_, lean_box(0));
                    if lean_obj_tag(v___x_1441_) == 0 {
                        v_isSharedCheck_1448_ = (!lean_is_exclusive(v___x_1441_)) as u8;
                        if v_isSharedCheck_1448_ == 0 {
                            v_unused_1449_ = lean_ctor_get(v___x_1441_, 0);
                            lean_dec(v_unused_1449_);
                            v___x_1443_ = v___x_1441_;
                            v_isShared_1444_ = v_isSharedCheck_1448_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_1441_);
                            v___x_1443_ = lean_box(0);
                            v_isShared_1444_ = v_isSharedCheck_1448_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1439_);
                        v_a_1450_ = lean_ctor_get(v___x_1441_, 0);
                        v_isSharedCheck_1457_ = (!lean_is_exclusive(v___x_1441_)) as u8;
                        if v_isSharedCheck_1457_ == 0 {
                            v___x_1452_ = v___x_1441_;
                            v_isShared_1453_ = v_isSharedCheck_1457_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1450_);
                            lean_dec(v___x_1441_);
                            v___x_1452_ = lean_box(0);
                            v_isShared_1453_ = v_isSharedCheck_1457_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_a_1436_);
                    return v___x_1438_;
                }
            }
            1 => {
                if v_isShared_1444_ == 0 {
                    lean_ctor_set(v___x_1443_, 0, v_a_1439_);
                    v___x_1446_ = v___x_1443_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1439_);
                    v___x_1446_ = v_reuseFailAlloc_1447_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1446_;
            }
            3 => {
                if v_isShared_1453_ == 0 {
                    v___x_1455_ = v___x_1452_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
                    v___x_1455_ = v_reuseFailAlloc_1456_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1455_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadMainM___aux__9___redArg___boxed(
    mut v_a_1458_: *mut LeanObject,
    mut v_a_1459_: *mut LeanObject,
    mut v_a_1460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1461_: *mut LeanObject = core::ptr::null_mut();
    v_res_1461_ = l_Lake_instMonadMainM___aux__9___redArg(v_a_1458_, v_a_1459_);
    return v_res_1461_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__9(
    mut v_00_u03b1_1462_: *mut LeanObject,
    mut v_00_u03b2_1463_: *mut LeanObject,
    mut v_a_1464_: *mut LeanObject,
    mut v_a_1465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1473_: u8 = 0;
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1477_: u8 = 0;
    let mut v_unused_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1482_: u8 = 0;
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1486_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1467_ = lean_apply_1(v_a_1464_, lean_box(0));
                if lean_obj_tag(v___x_1467_) == 0 {
                    v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
                    lean_inc(v_a_1468_);
                    lean_dec_ref_known(v___x_1467_, 1);
                    v___x_1469_ = lean_box(0);
                    v___x_1470_ = lean_apply_2(v_a_1465_, v___x_1469_, lean_box(0));
                    if lean_obj_tag(v___x_1470_) == 0 {
                        v_isSharedCheck_1477_ = (!lean_is_exclusive(v___x_1470_)) as u8;
                        if v_isSharedCheck_1477_ == 0 {
                            v_unused_1478_ = lean_ctor_get(v___x_1470_, 0);
                            lean_dec(v_unused_1478_);
                            v___x_1472_ = v___x_1470_;
                            v_isShared_1473_ = v_isSharedCheck_1477_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_1470_);
                            v___x_1472_ = lean_box(0);
                            v_isShared_1473_ = v_isSharedCheck_1477_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1468_);
                        v_a_1479_ = lean_ctor_get(v___x_1470_, 0);
                        v_isSharedCheck_1486_ = (!lean_is_exclusive(v___x_1470_)) as u8;
                        if v_isSharedCheck_1486_ == 0 {
                            v___x_1481_ = v___x_1470_;
                            v_isShared_1482_ = v_isSharedCheck_1486_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1479_);
                            lean_dec(v___x_1470_);
                            v___x_1481_ = lean_box(0);
                            v_isShared_1482_ = v_isSharedCheck_1486_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_a_1465_);
                    return v___x_1467_;
                }
            }
            1 => {
                if v_isShared_1473_ == 0 {
                    lean_ctor_set(v___x_1472_, 0, v_a_1468_);
                    v___x_1475_ = v___x_1472_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1468_);
                    v___x_1475_ = v_reuseFailAlloc_1476_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1475_;
            }
            3 => {
                if v_isShared_1482_ == 0 {
                    v___x_1484_ = v___x_1481_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
                    v___x_1484_ = v_reuseFailAlloc_1485_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1484_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadMainM___aux__9___boxed(
    mut v_00_u03b1_1487_: *mut LeanObject,
    mut v_00_u03b2_1488_: *mut LeanObject,
    mut v_a_1489_: *mut LeanObject,
    mut v_a_1490_: *mut LeanObject,
    mut v_a_1491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1492_: *mut LeanObject = core::ptr::null_mut();
    v_res_1492_ =
        l_Lake_instMonadMainM___aux__9(v_00_u03b1_1487_, v_00_u03b2_1488_, v_a_1489_, v_a_1490_);
    return v_res_1492_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__11___redArg(
    mut v_a_1493_: *mut LeanObject,
    mut v_a_1494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1502_: u8 = 0;
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1496_ = lean_apply_1(v_a_1493_, lean_box(0));
                if lean_obj_tag(v___x_1496_) == 0 {
                    lean_dec_ref_known(v___x_1496_, 1);
                    v___x_1497_ = lean_box(0);
                    v___x_1498_ = lean_apply_2(v_a_1494_, v___x_1497_, lean_box(0));
                    return v___x_1498_;
                } else {
                    lean_dec_ref(v_a_1494_);
                    v_a_1499_ = lean_ctor_get(v___x_1496_, 0);
                    v_isSharedCheck_1506_ = (!lean_is_exclusive(v___x_1496_)) as u8;
                    if v_isSharedCheck_1506_ == 0 {
                        v___x_1501_ = v___x_1496_;
                        v_isShared_1502_ = v_isSharedCheck_1506_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1499_);
                        lean_dec(v___x_1496_);
                        v___x_1501_ = lean_box(0);
                        v_isShared_1502_ = v_isSharedCheck_1506_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1502_ == 0 {
                    v___x_1504_ = v___x_1501_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
                    v___x_1504_ = v_reuseFailAlloc_1505_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1504_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadMainM___aux__11___redArg___boxed(
    mut v_a_1507_: *mut LeanObject,
    mut v_a_1508_: *mut LeanObject,
    mut v_a_1509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1510_: *mut LeanObject = core::ptr::null_mut();
    v_res_1510_ = l_Lake_instMonadMainM___aux__11___redArg(v_a_1507_, v_a_1508_);
    return v_res_1510_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__11(
    mut v_00_u03b1_1511_: *mut LeanObject,
    mut v_00_u03b2_1512_: *mut LeanObject,
    mut v_a_1513_: *mut LeanObject,
    mut v_a_1514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1522_: u8 = 0;
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1526_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1516_ = lean_apply_1(v_a_1513_, lean_box(0));
                if lean_obj_tag(v___x_1516_) == 0 {
                    lean_dec_ref_known(v___x_1516_, 1);
                    v___x_1517_ = lean_box(0);
                    v___x_1518_ = lean_apply_2(v_a_1514_, v___x_1517_, lean_box(0));
                    return v___x_1518_;
                } else {
                    lean_dec_ref(v_a_1514_);
                    v_a_1519_ = lean_ctor_get(v___x_1516_, 0);
                    v_isSharedCheck_1526_ = (!lean_is_exclusive(v___x_1516_)) as u8;
                    if v_isSharedCheck_1526_ == 0 {
                        v___x_1521_ = v___x_1516_;
                        v_isShared_1522_ = v_isSharedCheck_1526_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1519_);
                        lean_dec(v___x_1516_);
                        v___x_1521_ = lean_box(0);
                        v_isShared_1522_ = v_isSharedCheck_1526_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1522_ == 0 {
                    v___x_1524_ = v___x_1521_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
                    v___x_1524_ = v_reuseFailAlloc_1525_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1524_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadMainM___aux__11___boxed(
    mut v_00_u03b1_1527_: *mut LeanObject,
    mut v_00_u03b2_1528_: *mut LeanObject,
    mut v_a_1529_: *mut LeanObject,
    mut v_a_1530_: *mut LeanObject,
    mut v_a_1531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1532_: *mut LeanObject = core::ptr::null_mut();
    v_res_1532_ =
        l_Lake_instMonadMainM___aux__11(v_00_u03b1_1527_, v_00_u03b2_1528_, v_a_1529_, v_a_1530_);
    return v_res_1532_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__13___redArg(
    mut v_a_1533_: *mut LeanObject,
    mut v_a_1534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1542_: u8 = 0;
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1546_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1536_ = lean_apply_1(v_a_1533_, lean_box(0));
                if lean_obj_tag(v___x_1536_) == 0 {
                    v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
                    lean_inc(v_a_1537_);
                    lean_dec_ref_known(v___x_1536_, 1);
                    v___x_1538_ = lean_apply_2(v_a_1534_, v_a_1537_, lean_box(0));
                    return v___x_1538_;
                } else {
                    lean_dec_ref(v_a_1534_);
                    v_a_1539_ = lean_ctor_get(v___x_1536_, 0);
                    v_isSharedCheck_1546_ = (!lean_is_exclusive(v___x_1536_)) as u8;
                    if v_isSharedCheck_1546_ == 0 {
                        v___x_1541_ = v___x_1536_;
                        v_isShared_1542_ = v_isSharedCheck_1546_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1539_);
                        lean_dec(v___x_1536_);
                        v___x_1541_ = lean_box(0);
                        v_isShared_1542_ = v_isSharedCheck_1546_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1542_ == 0 {
                    v___x_1544_ = v___x_1541_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
                    v___x_1544_ = v_reuseFailAlloc_1545_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1544_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadMainM___aux__13___redArg___boxed(
    mut v_a_1547_: *mut LeanObject,
    mut v_a_1548_: *mut LeanObject,
    mut v_a_1549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1550_: *mut LeanObject = core::ptr::null_mut();
    v_res_1550_ = l_Lake_instMonadMainM___aux__13___redArg(v_a_1547_, v_a_1548_);
    return v_res_1550_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__13(
    mut v_00_u03b1_1551_: *mut LeanObject,
    mut v_00_u03b2_1552_: *mut LeanObject,
    mut v_a_1553_: *mut LeanObject,
    mut v_a_1554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1562_: u8 = 0;
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1566_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1556_ = lean_apply_1(v_a_1553_, lean_box(0));
                if lean_obj_tag(v___x_1556_) == 0 {
                    v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
                    lean_inc(v_a_1557_);
                    lean_dec_ref_known(v___x_1556_, 1);
                    v___x_1558_ = lean_apply_2(v_a_1554_, v_a_1557_, lean_box(0));
                    return v___x_1558_;
                } else {
                    lean_dec_ref(v_a_1554_);
                    v_a_1559_ = lean_ctor_get(v___x_1556_, 0);
                    v_isSharedCheck_1566_ = (!lean_is_exclusive(v___x_1556_)) as u8;
                    if v_isSharedCheck_1566_ == 0 {
                        v___x_1561_ = v___x_1556_;
                        v_isShared_1562_ = v_isSharedCheck_1566_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1559_);
                        lean_dec(v___x_1556_);
                        v___x_1561_ = lean_box(0);
                        v_isShared_1562_ = v_isSharedCheck_1566_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1562_ == 0 {
                    v___x_1564_ = v___x_1561_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
                    v___x_1564_ = v_reuseFailAlloc_1565_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1564_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadMainM___aux__13___boxed(
    mut v_00_u03b1_1567_: *mut LeanObject,
    mut v_00_u03b2_1568_: *mut LeanObject,
    mut v_a_1569_: *mut LeanObject,
    mut v_a_1570_: *mut LeanObject,
    mut v_a_1571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1572_: *mut LeanObject = core::ptr::null_mut();
    v_res_1572_ =
        l_Lake_instMonadMainM___aux__13(v_00_u03b1_1567_, v_00_u03b2_1568_, v_a_1569_, v_a_1570_);
    return v_res_1572_;
}
pub unsafe fn l_Lake_instMonadFinallyMainM___aux__1___redArg(
    mut v_x_1593_: *mut LeanObject,
    mut v_f_1594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1600_: u8 = 0;
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1607_: u8 = 0;
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1612_: u8 = 0;
    let mut v_a_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1616_: u8 = 0;
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1620_: u8 = 0;
    let mut v_reuseFailAlloc_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1622_: u8 = 0;
    let mut v_a_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1628_: u8 = 0;
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1632_: u8 = 0;
    let mut v_unused_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1637_: u8 = 0;
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1641_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_r_1596_ = lean_apply_1(v_x_1593_, lean_box(0));
                if lean_obj_tag(v_r_1596_) == 0 {
                    v_a_1597_ = lean_ctor_get(v_r_1596_, 0);
                    v_isSharedCheck_1622_ = (!lean_is_exclusive(v_r_1596_)) as u8;
                    if v_isSharedCheck_1622_ == 0 {
                        v___x_1599_ = v_r_1596_;
                        v_isShared_1600_ = v_isSharedCheck_1622_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1597_);
                        lean_dec(v_r_1596_);
                        v___x_1599_ = lean_box(0);
                        v_isShared_1600_ = v_isSharedCheck_1622_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1623_ = lean_ctor_get(v_r_1596_, 0);
                    lean_inc(v_a_1623_);
                    lean_dec_ref_known(v_r_1596_, 1);
                    v___x_1624_ = lean_box(0);
                    v___x_1625_ = lean_apply_2(v_f_1594_, v___x_1624_, lean_box(0));
                    if lean_obj_tag(v___x_1625_) == 0 {
                        v_isSharedCheck_1632_ = (!lean_is_exclusive(v___x_1625_)) as u8;
                        if v_isSharedCheck_1632_ == 0 {
                            v_unused_1633_ = lean_ctor_get(v___x_1625_, 0);
                            lean_dec(v_unused_1633_);
                            v___x_1627_ = v___x_1625_;
                            v_isShared_1628_ = v_isSharedCheck_1632_;
                            state = 7;
                            continue;
                        } else {
                            lean_dec(v___x_1625_);
                            v___x_1627_ = lean_box(0);
                            v_isShared_1628_ = v_isSharedCheck_1632_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1623_);
                        v_a_1634_ = lean_ctor_get(v___x_1625_, 0);
                        v_isSharedCheck_1641_ = (!lean_is_exclusive(v___x_1625_)) as u8;
                        if v_isSharedCheck_1641_ == 0 {
                            v___x_1636_ = v___x_1625_;
                            v_isShared_1637_ = v_isSharedCheck_1641_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_1634_);
                            lean_dec(v___x_1625_);
                            v___x_1636_ = lean_box(0);
                            v_isShared_1637_ = v_isSharedCheck_1641_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_a_1597_);
                if v_isShared_1600_ == 0 {
                    lean_ctor_set_tag(v___x_1599_, 1);
                    v___x_1602_ = v___x_1599_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1597_);
                    v___x_1602_ = v_reuseFailAlloc_1621_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1603_ = lean_apply_2(v_f_1594_, v___x_1602_, lean_box(0));
                if lean_obj_tag(v___x_1603_) == 0 {
                    v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
                    v_isSharedCheck_1612_ = (!lean_is_exclusive(v___x_1603_)) as u8;
                    if v_isSharedCheck_1612_ == 0 {
                        v___x_1606_ = v___x_1603_;
                        v_isShared_1607_ = v_isSharedCheck_1612_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1604_);
                        lean_dec(v___x_1603_);
                        v___x_1606_ = lean_box(0);
                        v_isShared_1607_ = v_isSharedCheck_1612_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1597_);
                    v_a_1613_ = lean_ctor_get(v___x_1603_, 0);
                    v_isSharedCheck_1620_ = (!lean_is_exclusive(v___x_1603_)) as u8;
                    if v_isSharedCheck_1620_ == 0 {
                        v___x_1615_ = v___x_1603_;
                        v_isShared_1616_ = v_isSharedCheck_1620_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1613_);
                        lean_dec(v___x_1603_);
                        v___x_1615_ = lean_box(0);
                        v_isShared_1616_ = v_isSharedCheck_1620_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1608_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1608_, 0, v_a_1597_);
                lean_ctor_set(v___x_1608_, 1, v_a_1604_);
                if v_isShared_1607_ == 0 {
                    lean_ctor_set(v___x_1606_, 0, v___x_1608_);
                    v___x_1610_ = v___x_1606_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1608_);
                    v___x_1610_ = v_reuseFailAlloc_1611_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1610_;
            }
            5 => {
                if v_isShared_1616_ == 0 {
                    v___x_1618_ = v___x_1615_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
                    v___x_1618_ = v_reuseFailAlloc_1619_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1618_;
            }
            7 => {
                if v_isShared_1628_ == 0 {
                    lean_ctor_set_tag(v___x_1627_, 1);
                    lean_ctor_set(v___x_1627_, 0, v_a_1623_);
                    v___x_1630_ = v___x_1627_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1623_);
                    v___x_1630_ = v_reuseFailAlloc_1631_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1630_;
            }
            9 => {
                if v_isShared_1637_ == 0 {
                    v___x_1639_ = v___x_1636_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
                    v___x_1639_ = v_reuseFailAlloc_1640_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1639_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadFinallyMainM___aux__1___redArg___boxed(
    mut v_x_1642_: *mut LeanObject,
    mut v_f_1643_: *mut LeanObject,
    mut v_a_1644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1645_: *mut LeanObject = core::ptr::null_mut();
    v_res_1645_ = l_Lake_instMonadFinallyMainM___aux__1___redArg(v_x_1642_, v_f_1643_);
    return v_res_1645_;
}
pub unsafe fn l_Lake_instMonadFinallyMainM___aux__1(
    mut v_00_u03b1_1646_: *mut LeanObject,
    mut v_00_u03b2_1647_: *mut LeanObject,
    mut v_x_1648_: *mut LeanObject,
    mut v_f_1649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_r_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1655_: u8 = 0;
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1662_: u8 = 0;
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1667_: u8 = 0;
    let mut v_a_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1671_: u8 = 0;
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1675_: u8 = 0;
    let mut v_reuseFailAlloc_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1677_: u8 = 0;
    let mut v_a_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1683_: u8 = 0;
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1687_: u8 = 0;
    let mut v_unused_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1692_: u8 = 0;
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1696_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_r_1651_ = lean_apply_1(v_x_1648_, lean_box(0));
                if lean_obj_tag(v_r_1651_) == 0 {
                    v_a_1652_ = lean_ctor_get(v_r_1651_, 0);
                    v_isSharedCheck_1677_ = (!lean_is_exclusive(v_r_1651_)) as u8;
                    if v_isSharedCheck_1677_ == 0 {
                        v___x_1654_ = v_r_1651_;
                        v_isShared_1655_ = v_isSharedCheck_1677_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1652_);
                        lean_dec(v_r_1651_);
                        v___x_1654_ = lean_box(0);
                        v_isShared_1655_ = v_isSharedCheck_1677_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1678_ = lean_ctor_get(v_r_1651_, 0);
                    lean_inc(v_a_1678_);
                    lean_dec_ref_known(v_r_1651_, 1);
                    v___x_1679_ = lean_box(0);
                    v___x_1680_ = lean_apply_2(v_f_1649_, v___x_1679_, lean_box(0));
                    if lean_obj_tag(v___x_1680_) == 0 {
                        v_isSharedCheck_1687_ = (!lean_is_exclusive(v___x_1680_)) as u8;
                        if v_isSharedCheck_1687_ == 0 {
                            v_unused_1688_ = lean_ctor_get(v___x_1680_, 0);
                            lean_dec(v_unused_1688_);
                            v___x_1682_ = v___x_1680_;
                            v_isShared_1683_ = v_isSharedCheck_1687_;
                            state = 7;
                            continue;
                        } else {
                            lean_dec(v___x_1680_);
                            v___x_1682_ = lean_box(0);
                            v_isShared_1683_ = v_isSharedCheck_1687_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1678_);
                        v_a_1689_ = lean_ctor_get(v___x_1680_, 0);
                        v_isSharedCheck_1696_ = (!lean_is_exclusive(v___x_1680_)) as u8;
                        if v_isSharedCheck_1696_ == 0 {
                            v___x_1691_ = v___x_1680_;
                            v_isShared_1692_ = v_isSharedCheck_1696_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_1689_);
                            lean_dec(v___x_1680_);
                            v___x_1691_ = lean_box(0);
                            v_isShared_1692_ = v_isSharedCheck_1696_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_a_1652_);
                if v_isShared_1655_ == 0 {
                    lean_ctor_set_tag(v___x_1654_, 1);
                    v___x_1657_ = v___x_1654_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1652_);
                    v___x_1657_ = v_reuseFailAlloc_1676_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1658_ = lean_apply_2(v_f_1649_, v___x_1657_, lean_box(0));
                if lean_obj_tag(v___x_1658_) == 0 {
                    v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
                    v_isSharedCheck_1667_ = (!lean_is_exclusive(v___x_1658_)) as u8;
                    if v_isSharedCheck_1667_ == 0 {
                        v___x_1661_ = v___x_1658_;
                        v_isShared_1662_ = v_isSharedCheck_1667_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1659_);
                        lean_dec(v___x_1658_);
                        v___x_1661_ = lean_box(0);
                        v_isShared_1662_ = v_isSharedCheck_1667_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1652_);
                    v_a_1668_ = lean_ctor_get(v___x_1658_, 0);
                    v_isSharedCheck_1675_ = (!lean_is_exclusive(v___x_1658_)) as u8;
                    if v_isSharedCheck_1675_ == 0 {
                        v___x_1670_ = v___x_1658_;
                        v_isShared_1671_ = v_isSharedCheck_1675_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1668_);
                        lean_dec(v___x_1658_);
                        v___x_1670_ = lean_box(0);
                        v_isShared_1671_ = v_isSharedCheck_1675_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1663_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1663_, 0, v_a_1652_);
                lean_ctor_set(v___x_1663_, 1, v_a_1659_);
                if v_isShared_1662_ == 0 {
                    lean_ctor_set(v___x_1661_, 0, v___x_1663_);
                    v___x_1665_ = v___x_1661_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
                    v___x_1665_ = v_reuseFailAlloc_1666_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1665_;
            }
            5 => {
                if v_isShared_1671_ == 0 {
                    v___x_1673_ = v___x_1670_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
                    v___x_1673_ = v_reuseFailAlloc_1674_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1673_;
            }
            7 => {
                if v_isShared_1683_ == 0 {
                    lean_ctor_set_tag(v___x_1682_, 1);
                    lean_ctor_set(v___x_1682_, 0, v_a_1678_);
                    v___x_1685_ = v___x_1682_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1678_);
                    v___x_1685_ = v_reuseFailAlloc_1686_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1685_;
            }
            9 => {
                if v_isShared_1692_ == 0 {
                    v___x_1694_ = v___x_1691_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
                    v___x_1694_ = v_reuseFailAlloc_1695_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1694_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadFinallyMainM___aux__1___boxed(
    mut v_00_u03b1_1697_: *mut LeanObject,
    mut v_00_u03b2_1698_: *mut LeanObject,
    mut v_x_1699_: *mut LeanObject,
    mut v_f_1700_: *mut LeanObject,
    mut v_a_1701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1702_: *mut LeanObject = core::ptr::null_mut();
    v_res_1702_ = l_Lake_instMonadFinallyMainM___aux__1(
        v_00_u03b1_1697_,
        v_00_u03b2_1698_,
        v_x_1699_,
        v_f_1700_,
    );
    return v_res_1702_;
}
pub unsafe fn l_Lake_instMonadLiftBaseIOMainM___aux__1___redArg(
    mut v_act_1705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    v___x_1707_ = lean_apply_1(v_act_1705_, lean_box(0));
    v___x_1708_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1708_, 0, v___x_1707_);
    return v___x_1708_;
}
pub unsafe fn l_Lake_instMonadLiftBaseIOMainM___aux__1___redArg___boxed(
    mut v_act_1709_: *mut LeanObject,
    mut v_a_1710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1711_: *mut LeanObject = core::ptr::null_mut();
    v_res_1711_ = l_Lake_instMonadLiftBaseIOMainM___aux__1___redArg(v_act_1709_);
    return v_res_1711_;
}
pub unsafe fn l_Lake_instMonadLiftBaseIOMainM___aux__1(
    mut v_00_u03b1_1712_: *mut LeanObject,
    mut v_act_1713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    v___x_1715_ = lean_apply_1(v_act_1713_, lean_box(0));
    v___x_1716_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1716_, 0, v___x_1715_);
    return v___x_1716_;
}
pub unsafe fn l_Lake_instMonadLiftBaseIOMainM___aux__1___boxed(
    mut v_00_u03b1_1717_: *mut LeanObject,
    mut v_act_1718_: *mut LeanObject,
    mut v_a_1719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1720_: *mut LeanObject = core::ptr::null_mut();
    v_res_1720_ = l_Lake_instMonadLiftBaseIOMainM___aux__1(v_00_u03b1_1717_, v_act_1718_);
    return v_res_1720_;
}
pub unsafe fn l_Lake_MainM_mk___redArg(mut v_x_1723_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    v___x_1725_ = lean_apply_1(v_x_1723_, lean_box(0));
    return v___x_1725_;
}
pub unsafe fn l_Lake_MainM_mk___redArg___boxed(
    mut v_x_1726_: *mut LeanObject,
    mut v_a_1727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1728_: *mut LeanObject = core::ptr::null_mut();
    v_res_1728_ = l_Lake_MainM_mk___redArg(v_x_1726_);
    return v_res_1728_;
}
pub unsafe fn l_Lake_MainM_mk(
    mut v_00_u03b1_1729_: *mut LeanObject,
    mut v_x_1730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    v___x_1732_ = lean_apply_1(v_x_1730_, lean_box(0));
    return v___x_1732_;
}
pub unsafe fn l_Lake_MainM_mk___boxed(
    mut v_00_u03b1_1733_: *mut LeanObject,
    mut v_x_1734_: *mut LeanObject,
    mut v_a_1735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1736_: *mut LeanObject = core::ptr::null_mut();
    v_res_1736_ = l_Lake_MainM_mk(v_00_u03b1_1733_, v_x_1734_);
    return v_res_1736_;
}
pub unsafe fn l_Lake_MainM_toEIO___redArg(mut v_self_1737_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    v___x_1739_ = lean_apply_1(v_self_1737_, lean_box(0));
    return v___x_1739_;
}
pub unsafe fn l_Lake_MainM_toEIO___redArg___boxed(
    mut v_self_1740_: *mut LeanObject,
    mut v_a_1741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1742_: *mut LeanObject = core::ptr::null_mut();
    v_res_1742_ = l_Lake_MainM_toEIO___redArg(v_self_1740_);
    return v_res_1742_;
}
pub unsafe fn l_Lake_MainM_toEIO(
    mut v_00_u03b1_1743_: *mut LeanObject,
    mut v_self_1744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    v___x_1746_ = lean_apply_1(v_self_1744_, lean_box(0));
    return v___x_1746_;
}
pub unsafe fn l_Lake_MainM_toEIO___boxed(
    mut v_00_u03b1_1747_: *mut LeanObject,
    mut v_self_1748_: *mut LeanObject,
    mut v_a_1749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1750_: *mut LeanObject = core::ptr::null_mut();
    v_res_1750_ = l_Lake_MainM_toEIO(v_00_u03b1_1747_, v_self_1748_);
    return v_res_1750_;
}
pub unsafe fn l_Lake_MainM_toBaseIO___redArg(mut v_self_1751_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1757_: u8 = 0;
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1761_: u8 = 0;
    let mut v_a_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1765_: u8 = 0;
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1769_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1753_ = lean_apply_1(v_self_1751_, lean_box(0));
                if lean_obj_tag(v___x_1753_) == 0 {
                    v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
                    v_isSharedCheck_1761_ = (!lean_is_exclusive(v___x_1753_)) as u8;
                    if v_isSharedCheck_1761_ == 0 {
                        v___x_1756_ = v___x_1753_;
                        v_isShared_1757_ = v_isSharedCheck_1761_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1754_);
                        lean_dec(v___x_1753_);
                        v___x_1756_ = lean_box(0);
                        v_isShared_1757_ = v_isSharedCheck_1761_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1762_ = lean_ctor_get(v___x_1753_, 0);
                    v_isSharedCheck_1769_ = (!lean_is_exclusive(v___x_1753_)) as u8;
                    if v_isSharedCheck_1769_ == 0 {
                        v___x_1764_ = v___x_1753_;
                        v_isShared_1765_ = v_isSharedCheck_1769_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1762_);
                        lean_dec(v___x_1753_);
                        v___x_1764_ = lean_box(0);
                        v_isShared_1765_ = v_isSharedCheck_1769_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1757_ == 0 {
                    lean_ctor_set_tag(v___x_1756_, 1);
                    v___x_1759_ = v___x_1756_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
                    v___x_1759_ = v_reuseFailAlloc_1760_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1759_;
            }
            3 => {
                if v_isShared_1765_ == 0 {
                    lean_ctor_set_tag(v___x_1764_, 0);
                    v___x_1767_ = v___x_1764_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
                    v___x_1767_ = v_reuseFailAlloc_1768_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1767_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_MainM_toBaseIO___redArg___boxed(
    mut v_self_1770_: *mut LeanObject,
    mut v_a_1771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1772_: *mut LeanObject = core::ptr::null_mut();
    v_res_1772_ = l_Lake_MainM_toBaseIO___redArg(v_self_1770_);
    return v_res_1772_;
}
pub unsafe fn l_Lake_MainM_toBaseIO(
    mut v_00_u03b1_1773_: *mut LeanObject,
    mut v_self_1774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1780_: u8 = 0;
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1784_: u8 = 0;
    let mut v_a_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1788_: u8 = 0;
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1792_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1776_ = lean_apply_1(v_self_1774_, lean_box(0));
                if lean_obj_tag(v___x_1776_) == 0 {
                    v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
                    v_isSharedCheck_1784_ = (!lean_is_exclusive(v___x_1776_)) as u8;
                    if v_isSharedCheck_1784_ == 0 {
                        v___x_1779_ = v___x_1776_;
                        v_isShared_1780_ = v_isSharedCheck_1784_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1777_);
                        lean_dec(v___x_1776_);
                        v___x_1779_ = lean_box(0);
                        v_isShared_1780_ = v_isSharedCheck_1784_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1785_ = lean_ctor_get(v___x_1776_, 0);
                    v_isSharedCheck_1792_ = (!lean_is_exclusive(v___x_1776_)) as u8;
                    if v_isSharedCheck_1792_ == 0 {
                        v___x_1787_ = v___x_1776_;
                        v_isShared_1788_ = v_isSharedCheck_1792_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1785_);
                        lean_dec(v___x_1776_);
                        v___x_1787_ = lean_box(0);
                        v_isShared_1788_ = v_isSharedCheck_1792_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1780_ == 0 {
                    lean_ctor_set_tag(v___x_1779_, 1);
                    v___x_1782_ = v___x_1779_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
                    v___x_1782_ = v_reuseFailAlloc_1783_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1782_;
            }
            3 => {
                if v_isShared_1788_ == 0 {
                    lean_ctor_set_tag(v___x_1787_, 0);
                    v___x_1790_ = v___x_1787_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
                    v___x_1790_ = v_reuseFailAlloc_1791_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1790_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_MainM_toBaseIO___boxed(
    mut v_00_u03b1_1793_: *mut LeanObject,
    mut v_self_1794_: *mut LeanObject,
    mut v_a_1795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1796_: *mut LeanObject = core::ptr::null_mut();
    v_res_1796_ = l_Lake_MainM_toBaseIO(v_00_u03b1_1793_, v_self_1794_);
    return v_res_1796_;
}
pub unsafe fn l_Lake_MainM_run___redArg(mut v_self_1797_: *mut LeanObject) -> u32 {
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    v___x_1799_ = lean_apply_1(v_self_1797_, lean_box(0));
    if lean_obj_tag(v___x_1799_) == 0 {
        let mut v___x_1800_: u32 = 0;
        lean_dec_ref_known(v___x_1799_, 1);
        v___x_1800_ = 0;
        return v___x_1800_;
    } else {
        let mut v_a_1801_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1802_: u32 = 0;
        v_a_1801_ = lean_ctor_get(v___x_1799_, 0);
        lean_inc(v_a_1801_);
        lean_dec_ref_known(v___x_1799_, 1);
        v___x_1802_ = lean_unbox_uint32(v_a_1801_);
        lean_dec(v_a_1801_);
        return v___x_1802_;
    }
}
pub unsafe fn l_Lake_MainM_run___redArg___boxed(
    mut v_self_1803_: *mut LeanObject,
    mut v_a_1804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1805_: u32 = 0;
    let mut v_r_1806_: *mut LeanObject = core::ptr::null_mut();
    v_res_1805_ = l_Lake_MainM_run___redArg(v_self_1803_);
    v_r_1806_ = lean_box_uint32(v_res_1805_);
    return v_r_1806_;
}
pub unsafe fn l_Lake_MainM_run(
    mut v_00_u03b1_1807_: *mut LeanObject,
    mut v_self_1808_: *mut LeanObject,
) -> u32 {
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    v___x_1810_ = lean_apply_1(v_self_1808_, lean_box(0));
    if lean_obj_tag(v___x_1810_) == 0 {
        let mut v___x_1811_: u32 = 0;
        lean_dec_ref_known(v___x_1810_, 1);
        v___x_1811_ = 0;
        return v___x_1811_;
    } else {
        let mut v_a_1812_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1813_: u32 = 0;
        v_a_1812_ = lean_ctor_get(v___x_1810_, 0);
        lean_inc(v_a_1812_);
        lean_dec_ref_known(v___x_1810_, 1);
        v___x_1813_ = lean_unbox_uint32(v_a_1812_);
        lean_dec(v_a_1812_);
        return v___x_1813_;
    }
}
pub unsafe fn l_Lake_MainM_run___boxed(
    mut v_00_u03b1_1814_: *mut LeanObject,
    mut v_self_1815_: *mut LeanObject,
    mut v_a_1816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1817_: u32 = 0;
    let mut v_r_1818_: *mut LeanObject = core::ptr::null_mut();
    v_res_1817_ = l_Lake_MainM_run(v_00_u03b1_1814_, v_self_1815_);
    v_r_1818_ = lean_box_uint32(v_res_1817_);
    return v_r_1818_;
}
pub unsafe fn l_Lake_MainM_exit___redArg(mut v_rc_1819_: u32) -> *mut LeanObject {
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    v___x_1821_ = lean_box_uint32(v_rc_1819_);
    v___x_1822_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1822_, 0, v___x_1821_);
    return v___x_1822_;
}
pub unsafe fn l_Lake_MainM_exit___redArg___boxed(
    mut v_rc_1823_: *mut LeanObject,
    mut v_a_1824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_rc_boxed_1825_: u32 = 0;
    let mut v_res_1826_: *mut LeanObject = core::ptr::null_mut();
    v_rc_boxed_1825_ = lean_unbox_uint32(v_rc_1823_);
    lean_dec(v_rc_1823_);
    v_res_1826_ = l_Lake_MainM_exit___redArg(v_rc_boxed_1825_);
    return v_res_1826_;
}
pub unsafe fn l_Lake_MainM_exit(
    mut v_00_u03b1_1827_: *mut LeanObject,
    mut v_rc_1828_: u32,
) -> *mut LeanObject {
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    v___x_1830_ = lean_box_uint32(v_rc_1828_);
    v___x_1831_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1831_, 0, v___x_1830_);
    return v___x_1831_;
}
pub unsafe fn l_Lake_MainM_exit___boxed(
    mut v_00_u03b1_1832_: *mut LeanObject,
    mut v_rc_1833_: *mut LeanObject,
    mut v_a_1834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_rc_boxed_1835_: u32 = 0;
    let mut v_res_1836_: *mut LeanObject = core::ptr::null_mut();
    v_rc_boxed_1835_ = lean_unbox_uint32(v_rc_1833_);
    lean_dec(v_rc_1833_);
    v_res_1836_ = l_Lake_MainM_exit(v_00_u03b1_1832_, v_rc_boxed_1835_);
    return v_res_1836_;
}
pub unsafe fn l_Lake_MainM_tryCatchExit___redArg(
    mut v_f_1839_: *mut LeanObject,
    mut v_self_1840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    v___x_1842_ = lean_apply_1(v_self_1840_, lean_box(0));
    if lean_obj_tag(v___x_1842_) == 0 {
        lean_dec_ref(v_f_1839_);
        return v___x_1842_;
    } else {
        let mut v_a_1843_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
        v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
        lean_inc(v_a_1843_);
        lean_dec_ref_known(v___x_1842_, 1);
        v___x_1844_ = lean_apply_2(v_f_1839_, v_a_1843_, lean_box(0));
        return v___x_1844_;
    }
}
pub unsafe fn l_Lake_MainM_tryCatchExit___redArg___boxed(
    mut v_f_1845_: *mut LeanObject,
    mut v_self_1846_: *mut LeanObject,
    mut v_a_1847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1848_: *mut LeanObject = core::ptr::null_mut();
    v_res_1848_ = l_Lake_MainM_tryCatchExit___redArg(v_f_1845_, v_self_1846_);
    return v_res_1848_;
}
pub unsafe fn l_Lake_MainM_tryCatchExit(
    mut v_00_u03b1_1849_: *mut LeanObject,
    mut v_f_1850_: *mut LeanObject,
    mut v_self_1851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    v___x_1853_ = lean_apply_1(v_self_1851_, lean_box(0));
    if lean_obj_tag(v___x_1853_) == 0 {
        lean_dec_ref(v_f_1850_);
        return v___x_1853_;
    } else {
        let mut v_a_1854_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
        v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
        lean_inc(v_a_1854_);
        lean_dec_ref_known(v___x_1853_, 1);
        v___x_1855_ = lean_apply_2(v_f_1850_, v_a_1854_, lean_box(0));
        return v___x_1855_;
    }
}
pub unsafe fn l_Lake_MainM_tryCatchExit___boxed(
    mut v_00_u03b1_1856_: *mut LeanObject,
    mut v_f_1857_: *mut LeanObject,
    mut v_self_1858_: *mut LeanObject,
    mut v_a_1859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1860_: *mut LeanObject = core::ptr::null_mut();
    v_res_1860_ = l_Lake_MainM_tryCatchExit(v_00_u03b1_1856_, v_f_1857_, v_self_1858_);
    return v_res_1860_;
}
pub unsafe fn _init_l_Lake_MainM_tryCatchError___redArg___boxed__const__1() -> *mut LeanObject {
    let mut v___x_1861_: u32 = 0;
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    v___x_1861_ = 0;
    v___x_1862_ = lean_box_uint32(v___x_1861_);
    return v___x_1862_;
}
pub unsafe fn l_Lake_MainM_tryCatchError___redArg(
    mut v_f_1863_: *mut LeanObject,
    mut v_self_1864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1870_: u8 = 0;
    let mut v___x_1871_: u32 = 0;
    let mut v___x_1872_: u32 = 0;
    let mut v___x_1873_: u8 = 0;
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1879_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1866_ = lean_apply_1(v_self_1864_, lean_box(0));
                if lean_obj_tag(v___x_1866_) == 0 {
                    lean_dec_ref(v_f_1863_);
                    return v___x_1866_;
                } else {
                    v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
                    v_isSharedCheck_1879_ = (!lean_is_exclusive(v___x_1866_)) as u8;
                    if v_isSharedCheck_1879_ == 0 {
                        v___x_1869_ = v___x_1866_;
                        v_isShared_1870_ = v_isSharedCheck_1879_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1867_);
                        lean_dec(v___x_1866_);
                        v___x_1869_ = lean_box(0);
                        v_isShared_1870_ = v_isSharedCheck_1879_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1871_ = 0;
                v___x_1872_ = lean_unbox_uint32(v_a_1867_);
                v___x_1873_ = lean_uint32_dec_eq(v___x_1872_, v___x_1871_);
                if v___x_1873_ == 0 {
                    lean_del_object(v___x_1869_);
                    v___x_1874_ = lean_apply_2(v_f_1863_, v_a_1867_, lean_box(0));
                    return v___x_1874_;
                } else {
                    lean_dec(v_a_1867_);
                    lean_dec_ref(v_f_1863_);
                    v___x_1875_ = l_Lake_MainM_tryCatchError___redArg___boxed__const__1;
                    if v_isShared_1870_ == 0 {
                        lean_ctor_set(v___x_1869_, 0, v___x_1875_);
                        v___x_1877_ = v___x_1869_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1875_);
                        v___x_1877_ = v_reuseFailAlloc_1878_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1877_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_MainM_tryCatchError___redArg___boxed(
    mut v_f_1880_: *mut LeanObject,
    mut v_self_1881_: *mut LeanObject,
    mut v_a_1882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1883_: *mut LeanObject = core::ptr::null_mut();
    v_res_1883_ = l_Lake_MainM_tryCatchError___redArg(v_f_1880_, v_self_1881_);
    return v_res_1883_;
}
pub unsafe fn l_Lake_MainM_tryCatchError(
    mut v_00_u03b1_1884_: *mut LeanObject,
    mut v_f_1885_: *mut LeanObject,
    mut v_self_1886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1892_: u8 = 0;
    let mut v___x_1893_: u32 = 0;
    let mut v___x_1894_: u32 = 0;
    let mut v___x_1895_: u8 = 0;
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1901_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1888_ = lean_apply_1(v_self_1886_, lean_box(0));
                if lean_obj_tag(v___x_1888_) == 0 {
                    lean_dec_ref(v_f_1885_);
                    return v___x_1888_;
                } else {
                    v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
                    v_isSharedCheck_1901_ = (!lean_is_exclusive(v___x_1888_)) as u8;
                    if v_isSharedCheck_1901_ == 0 {
                        v___x_1891_ = v___x_1888_;
                        v_isShared_1892_ = v_isSharedCheck_1901_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1889_);
                        lean_dec(v___x_1888_);
                        v___x_1891_ = lean_box(0);
                        v_isShared_1892_ = v_isSharedCheck_1901_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1893_ = 0;
                v___x_1894_ = lean_unbox_uint32(v_a_1889_);
                v___x_1895_ = lean_uint32_dec_eq(v___x_1894_, v___x_1893_);
                if v___x_1895_ == 0 {
                    lean_del_object(v___x_1891_);
                    v___x_1896_ = lean_apply_2(v_f_1885_, v_a_1889_, lean_box(0));
                    return v___x_1896_;
                } else {
                    lean_dec(v_a_1889_);
                    lean_dec_ref(v_f_1885_);
                    v___x_1897_ = l_Lake_MainM_tryCatchError___redArg___boxed__const__1;
                    if v_isShared_1892_ == 0 {
                        lean_ctor_set(v___x_1891_, 0, v___x_1897_);
                        v___x_1899_ = v___x_1891_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1897_);
                        v___x_1899_ = v_reuseFailAlloc_1900_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1899_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_MainM_tryCatchError___boxed(
    mut v_00_u03b1_1902_: *mut LeanObject,
    mut v_f_1903_: *mut LeanObject,
    mut v_self_1904_: *mut LeanObject,
    mut v_a_1905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1906_: *mut LeanObject = core::ptr::null_mut();
    v_res_1906_ = l_Lake_MainM_tryCatchError(v_00_u03b1_1902_, v_f_1903_, v_self_1904_);
    return v_res_1906_;
}
pub unsafe fn _init_l_Lake_MainM_failure___redArg___boxed__const__1() -> *mut LeanObject {
    let mut v___x_1907_: u32 = 0;
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    v___x_1907_ = 1;
    v___x_1908_ = lean_box_uint32(v___x_1907_);
    return v___x_1908_;
}
pub unsafe fn l_Lake_MainM_failure___redArg() -> *mut LeanObject {
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    v___x_1910_ = l_Lake_MainM_failure___redArg___boxed__const__1;
    v___x_1911_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1911_, 0, v___x_1910_);
    return v___x_1911_;
}
pub unsafe fn l_Lake_MainM_failure___redArg___boxed(
    mut v_a_1912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1913_: *mut LeanObject = core::ptr::null_mut();
    v_res_1913_ = l_Lake_MainM_failure___redArg();
    return v_res_1913_;
}
pub unsafe fn l_Lake_MainM_failure(mut v_00_u03b1_1914_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    v___x_1916_ = l_Lake_MainM_failure___redArg___boxed__const__1;
    v___x_1917_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1917_, 0, v___x_1916_);
    return v___x_1917_;
}
pub unsafe fn l_Lake_MainM_failure___boxed(
    mut v_00_u03b1_1918_: *mut LeanObject,
    mut v_a_1919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1920_: *mut LeanObject = core::ptr::null_mut();
    v_res_1920_ = l_Lake_MainM_failure(v_00_u03b1_1918_);
    return v_res_1920_;
}
pub unsafe fn l_Lake_MainM_orElse___redArg(
    mut v_self_1921_: *mut LeanObject,
    mut v_other_1922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1928_: u8 = 0;
    let mut v___x_1929_: u32 = 0;
    let mut v___x_1930_: u32 = 0;
    let mut v___x_1931_: u8 = 0;
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1938_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1924_ = lean_apply_1(v_self_1921_, lean_box(0));
                if lean_obj_tag(v___x_1924_) == 0 {
                    lean_dec_ref(v_other_1922_);
                    return v___x_1924_;
                } else {
                    v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
                    v_isSharedCheck_1938_ = (!lean_is_exclusive(v___x_1924_)) as u8;
                    if v_isSharedCheck_1938_ == 0 {
                        v___x_1927_ = v___x_1924_;
                        v_isShared_1928_ = v_isSharedCheck_1938_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1925_);
                        lean_dec(v___x_1924_);
                        v___x_1927_ = lean_box(0);
                        v_isShared_1928_ = v_isSharedCheck_1938_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1929_ = 0;
                v___x_1930_ = lean_unbox_uint32(v_a_1925_);
                lean_dec(v_a_1925_);
                v___x_1931_ = lean_uint32_dec_eq(v___x_1930_, v___x_1929_);
                if v___x_1931_ == 0 {
                    lean_del_object(v___x_1927_);
                    v___x_1932_ = lean_box(0);
                    v___x_1933_ = lean_apply_2(v_other_1922_, v___x_1932_, lean_box(0));
                    return v___x_1933_;
                } else {
                    lean_dec_ref(v_other_1922_);
                    v___x_1934_ = l_Lake_MainM_tryCatchError___redArg___boxed__const__1;
                    if v_isShared_1928_ == 0 {
                        lean_ctor_set(v___x_1927_, 0, v___x_1934_);
                        v___x_1936_ = v___x_1927_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1934_);
                        v___x_1936_ = v_reuseFailAlloc_1937_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1936_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_MainM_orElse___redArg___boxed(
    mut v_self_1939_: *mut LeanObject,
    mut v_other_1940_: *mut LeanObject,
    mut v_a_1941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1942_: *mut LeanObject = core::ptr::null_mut();
    v_res_1942_ = l_Lake_MainM_orElse___redArg(v_self_1939_, v_other_1940_);
    return v_res_1942_;
}
pub unsafe fn l_Lake_MainM_orElse(
    mut v_00_u03b1_1943_: *mut LeanObject,
    mut v_self_1944_: *mut LeanObject,
    mut v_other_1945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1951_: u8 = 0;
    let mut v___x_1952_: u32 = 0;
    let mut v___x_1953_: u32 = 0;
    let mut v___x_1954_: u8 = 0;
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1961_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1947_ = lean_apply_1(v_self_1944_, lean_box(0));
                if lean_obj_tag(v___x_1947_) == 0 {
                    lean_dec_ref(v_other_1945_);
                    return v___x_1947_;
                } else {
                    v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
                    v_isSharedCheck_1961_ = (!lean_is_exclusive(v___x_1947_)) as u8;
                    if v_isSharedCheck_1961_ == 0 {
                        v___x_1950_ = v___x_1947_;
                        v_isShared_1951_ = v_isSharedCheck_1961_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1948_);
                        lean_dec(v___x_1947_);
                        v___x_1950_ = lean_box(0);
                        v_isShared_1951_ = v_isSharedCheck_1961_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1952_ = 0;
                v___x_1953_ = lean_unbox_uint32(v_a_1948_);
                lean_dec(v_a_1948_);
                v___x_1954_ = lean_uint32_dec_eq(v___x_1953_, v___x_1952_);
                if v___x_1954_ == 0 {
                    lean_del_object(v___x_1950_);
                    v___x_1955_ = lean_box(0);
                    v___x_1956_ = lean_apply_2(v_other_1945_, v___x_1955_, lean_box(0));
                    return v___x_1956_;
                } else {
                    lean_dec_ref(v_other_1945_);
                    v___x_1957_ = l_Lake_MainM_tryCatchError___redArg___boxed__const__1;
                    if v_isShared_1951_ == 0 {
                        lean_ctor_set(v___x_1950_, 0, v___x_1957_);
                        v___x_1959_ = v___x_1950_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1957_);
                        v___x_1959_ = v_reuseFailAlloc_1960_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1959_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_MainM_orElse___boxed(
    mut v_00_u03b1_1962_: *mut LeanObject,
    mut v_self_1963_: *mut LeanObject,
    mut v_other_1964_: *mut LeanObject,
    mut v_a_1965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1966_: *mut LeanObject = core::ptr::null_mut();
    v_res_1966_ = l_Lake_MainM_orElse(v_00_u03b1_1962_, v_self_1963_, v_other_1964_);
    return v_res_1966_;
}
pub unsafe fn _init_l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative() -> *mut LeanObject {
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    v___x_1969_ = l_Lake_instMonadMainM;
    v_toApplicative_1970_ = lean_ctor_get(v___x_1969_, 0);
    v___x_1971_ = l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__0;
    v___x_1972_ = l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__1;
    lean_inc_ref(v_toApplicative_1970_);
    v___x_1973_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1973_, 0, v_toApplicative_1970_);
    lean_ctor_set(v___x_1973_, 1, v___x_1971_);
    lean_ctor_set(v___x_1973_, 2, v___x_1972_);
    return v___x_1973_;
}
pub unsafe fn l_Lake_MainM_instMonadLog___lam__0(
    mut v___x_1974_: *mut LeanObject,
    mut v___x_1975_: u8,
    mut v___x_1976_: u8,
    mut v_e_1977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    v___x_1979_ = l_Lake_OutStream_logEntry(v___x_1974_, v_e_1977_, v___x_1975_, v___x_1976_);
    v___x_1980_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1980_, 0, v___x_1979_);
    return v___x_1980_;
}
pub unsafe fn l_Lake_MainM_instMonadLog___lam__0___boxed(
    mut v___x_1981_: *mut LeanObject,
    mut v___x_1982_: *mut LeanObject,
    mut v___x_1983_: *mut LeanObject,
    mut v_e_1984_: *mut LeanObject,
    mut v___y_1985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_37__boxed_1986_: u8 = 0;
    let mut v___x_38__boxed_1987_: u8 = 0;
    let mut v_res_1988_: *mut LeanObject = core::ptr::null_mut();
    v___x_37__boxed_1986_ = (lean_unbox(v___x_1982_) as u8);
    v___x_38__boxed_1987_ = (lean_unbox(v___x_1983_) as u8);
    v_res_1988_ = l_Lake_MainM_instMonadLog___lam__0(
        v___x_1981_,
        v___x_37__boxed_1986_,
        v___x_38__boxed_1987_,
        v_e_1984_,
    );
    lean_dec_ref(v_e_1984_);
    lean_dec(v___x_1981_);
    return v_res_1988_;
}
pub unsafe fn l_Lake_MainM_error___redArg(
    mut v_msg_1996_: *mut LeanObject,
    mut v_rc_1997_: u32,
) -> *mut LeanObject {
    let mut v___x_1999_: u8 = 0;
    let mut v___x_2000_: u8 = 0;
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: u8 = 0;
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    v___x_1999_ = 1;
    v___x_2000_ = 0;
    v___x_2001_ = lean_box(1);
    v___x_2002_ = 3;
    v___x_2003_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_2003_, 0, v_msg_1996_);
    lean_ctor_set_uint8(
        v___x_2003_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2002_,
    );
    v___x_2004_ = l_Lake_OutStream_logEntry(v___x_2001_, v___x_2003_, v___x_1999_, v___x_2000_);
    lean_dec_ref_known(v___x_2003_, 1);
    v___x_2005_ = lean_box_uint32(v_rc_1997_);
    v___x_2006_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2006_, 0, v___x_2005_);
    return v___x_2006_;
}
pub unsafe fn l_Lake_MainM_error___redArg___boxed(
    mut v_msg_2007_: *mut LeanObject,
    mut v_rc_2008_: *mut LeanObject,
    mut v_a_2009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_rc_boxed_2010_: u32 = 0;
    let mut v_res_2011_: *mut LeanObject = core::ptr::null_mut();
    v_rc_boxed_2010_ = lean_unbox_uint32(v_rc_2008_);
    lean_dec(v_rc_2008_);
    v_res_2011_ = l_Lake_MainM_error___redArg(v_msg_2007_, v_rc_boxed_2010_);
    return v_res_2011_;
}
pub unsafe fn l_Lake_MainM_error(
    mut v_00_u03b1_2012_: *mut LeanObject,
    mut v_msg_2013_: *mut LeanObject,
    mut v_rc_2014_: u32,
) -> *mut LeanObject {
    let mut v___x_2016_: u8 = 0;
    let mut v___x_2017_: u8 = 0;
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: u8 = 0;
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    v___x_2016_ = 1;
    v___x_2017_ = 0;
    v___x_2018_ = lean_box(1);
    v___x_2019_ = 3;
    v___x_2020_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_2020_, 0, v_msg_2013_);
    lean_ctor_set_uint8(
        v___x_2020_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2019_,
    );
    v___x_2021_ = l_Lake_OutStream_logEntry(v___x_2018_, v___x_2020_, v___x_2016_, v___x_2017_);
    lean_dec_ref_known(v___x_2020_, 1);
    v___x_2022_ = lean_box_uint32(v_rc_2014_);
    v___x_2023_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2023_, 0, v___x_2022_);
    return v___x_2023_;
}
pub unsafe fn l_Lake_MainM_error___boxed(
    mut v_00_u03b1_2024_: *mut LeanObject,
    mut v_msg_2025_: *mut LeanObject,
    mut v_rc_2026_: *mut LeanObject,
    mut v_a_2027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_rc_boxed_2028_: u32 = 0;
    let mut v_res_2029_: *mut LeanObject = core::ptr::null_mut();
    v_rc_boxed_2028_ = lean_unbox_uint32(v_rc_2026_);
    lean_dec(v_rc_2026_);
    v_res_2029_ = l_Lake_MainM_error(v_00_u03b1_2024_, v_msg_2025_, v_rc_boxed_2028_);
    return v_res_2029_;
}
pub unsafe fn l_Lake_MainM_instMonadError___lam__0(
    mut v_00_u03b1_2030_: *mut LeanObject,
    mut v_msg_2031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2033_: u8 = 0;
    let mut v___x_2034_: u8 = 0;
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: u8 = 0;
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    v___x_2033_ = 1;
    v___x_2034_ = 0;
    v___x_2035_ = lean_box(1);
    v___x_2036_ = 3;
    v___x_2037_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_2037_, 0, v_msg_2031_);
    lean_ctor_set_uint8(
        v___x_2037_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2036_,
    );
    v___x_2038_ = l_Lake_OutStream_logEntry(v___x_2035_, v___x_2037_, v___x_2033_, v___x_2034_);
    lean_dec_ref_known(v___x_2037_, 1);
    v___x_2039_ = l_Lake_MainM_failure___redArg___boxed__const__1;
    v___x_2040_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2040_, 0, v___x_2039_);
    return v___x_2040_;
}
pub unsafe fn l_Lake_MainM_instMonadError___lam__0___boxed(
    mut v_00_u03b1_2041_: *mut LeanObject,
    mut v_msg_2042_: *mut LeanObject,
    mut v___y_2043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2044_: *mut LeanObject = core::ptr::null_mut();
    v_res_2044_ = l_Lake_MainM_instMonadError___lam__0(v_00_u03b1_2041_, v_msg_2042_);
    return v_res_2044_;
}
pub unsafe fn l_Lake_MainM_instMonadLiftIO___lam__0(
    mut v_00_u03b1_2047_: *mut LeanObject,
    mut v___y_2048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2054_: u8 = 0;
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut v_a_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2062_: u8 = 0;
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: u8 = 0;
    let mut v___x_2065_: u8 = 0;
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: u8 = 0;
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2074_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2050_ = lean_apply_1(v___y_2048_, lean_box(0));
                if lean_obj_tag(v___x_2050_) == 0 {
                    v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
                    v_isSharedCheck_2058_ = (!lean_is_exclusive(v___x_2050_)) as u8;
                    if v_isSharedCheck_2058_ == 0 {
                        v___x_2053_ = v___x_2050_;
                        v_isShared_2054_ = v_isSharedCheck_2058_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2051_);
                        lean_dec(v___x_2050_);
                        v___x_2053_ = lean_box(0);
                        v_isShared_2054_ = v_isSharedCheck_2058_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2059_ = lean_ctor_get(v___x_2050_, 0);
                    v_isSharedCheck_2074_ = (!lean_is_exclusive(v___x_2050_)) as u8;
                    if v_isSharedCheck_2074_ == 0 {
                        v___x_2061_ = v___x_2050_;
                        v_isShared_2062_ = v_isSharedCheck_2074_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2059_);
                        lean_dec(v___x_2050_);
                        v___x_2061_ = lean_box(0);
                        v_isShared_2062_ = v_isSharedCheck_2074_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2054_ == 0 {
                    v___x_2056_ = v___x_2053_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
                    v___x_2056_ = v_reuseFailAlloc_2057_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2056_;
            }
            3 => {
                v___x_2063_ = lean_io_error_to_string(v_a_2059_);
                v___x_2064_ = 1;
                v___x_2065_ = 0;
                v___x_2066_ = lean_box(1);
                v___x_2067_ = 3;
                v___x_2068_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_2068_, 0, v___x_2063_);
                lean_ctor_set_uint8(
                    v___x_2068_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2067_,
                );
                v___x_2069_ =
                    l_Lake_OutStream_logEntry(v___x_2066_, v___x_2068_, v___x_2064_, v___x_2065_);
                lean_dec_ref_known(v___x_2068_, 1);
                v___x_2070_ = l_Lake_MainM_failure___redArg___boxed__const__1;
                if v_isShared_2062_ == 0 {
                    lean_ctor_set(v___x_2061_, 0, v___x_2070_);
                    v___x_2072_ = v___x_2061_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2070_);
                    v___x_2072_ = v_reuseFailAlloc_2073_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2072_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_MainM_instMonadLiftIO___lam__0___boxed(
    mut v_00_u03b1_2075_: *mut LeanObject,
    mut v___y_2076_: *mut LeanObject,
    mut v___y_2077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2078_: *mut LeanObject = core::ptr::null_mut();
    v_res_2078_ = l_Lake_MainM_instMonadLiftIO___lam__0(v_00_u03b1_2075_, v___y_2076_);
    return v_res_2078_;
}
pub unsafe fn l_Lake_MainM_runLogIO___redArg___lam__0(
    mut v_val_2081_: *mut LeanObject,
    mut v___y_2082_: u8,
    mut v_val_2083_: u8,
    mut v_x_2084_: *mut LeanObject,
    mut v___y_2085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    v___x_2087_ = l_Lake_logToStream(v___y_2085_, v_val_2081_, v___y_2082_, v_val_2083_);
    return v___x_2087_;
}
pub unsafe fn l_Lake_MainM_runLogIO___redArg___lam__0___boxed(
    mut v_val_2088_: *mut LeanObject,
    mut v___y_2089_: *mut LeanObject,
    mut v_val_2090_: *mut LeanObject,
    mut v_x_2091_: *mut LeanObject,
    mut v___y_2092_: *mut LeanObject,
    mut v___y_2093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_373__boxed_2094_: u8 = 0;
    let mut v_val_374__boxed_2095_: u8 = 0;
    let mut v_res_2096_: *mut LeanObject = core::ptr::null_mut();
    v___y_373__boxed_2094_ = (lean_unbox(v___y_2089_) as u8);
    v_val_374__boxed_2095_ = (lean_unbox(v_val_2090_) as u8);
    v_res_2096_ = l_Lake_MainM_runLogIO___redArg___lam__0(
        v_val_2088_,
        v___y_373__boxed_2094_,
        v_val_374__boxed_2095_,
        v_x_2091_,
        v___y_2092_,
    );
    lean_dec_ref(v___y_2092_);
    return v_res_2096_;
}
pub unsafe fn l_Lake_MainM_runLogIO___redArg(
    mut v_x_2099_: *mut LeanObject,
    mut v_cfg_2100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2107_: u8 = 0;
    let mut v_val_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2111_: u8 = 0;
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2115_: u8 = 0;
    let mut v___y_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2118_: u8 = 0;
    let mut v___y_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2124_: u8 = 0;
    let mut v___y_2125_: u8 = 0;
    let mut v_ansiMode_2126_: u8 = 0;
    let mut v_out_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: u8 = 0;
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: u8 = 0;
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: u8 = 0;
    let mut v___x_2138_: usize = 0;
    let mut v___x_2139_: usize = 0;
    let mut v___x_141__overap_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: usize = 0;
    let mut v___x_2143_: usize = 0;
    let mut v___x_145__overap_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2149_: u8 = 0;
    let mut v___x_2150_: u8 = 0;
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_failLv_2155_: u8 = 0;
    let mut v_outLv_2156_: u8 = 0;
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: u8 = 0;
    let mut v___x_2159_: u8 = 0;
    let mut v___x_2160_: u8 = 0;
    let mut v___x_2161_: u8 = 0;
    let mut v_a_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2120_ = l_instMonadBaseIO;
                v___x_2151_ = l_Lake_MainM_runLogIO___redArg___closed__0;
                v___x_2152_ = lean_apply_2(v_x_2099_, v___x_2151_, lean_box(0));
                if lean_obj_tag(v___x_2152_) == 0 {
                    v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
                    lean_inc(v_a_2153_);
                    v_a_2154_ = lean_ctor_get(v___x_2152_, 1);
                    lean_inc(v_a_2154_);
                    lean_dec_ref_known(v___x_2152_, 2);
                    v_failLv_2155_ = lean_ctor_get_uint8(
                        v_cfg_2100_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_outLv_2156_ = lean_ctor_get_uint8(
                        v_cfg_2100_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    );
                    v___x_2157_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2157_, 0, v_a_2153_);
                    v___x_2158_ = l_Lake_Log_maxLv(v_a_2154_);
                    v___x_2159_ = l_Lake_instOrdLogLevel_ord(v_failLv_2155_, v___x_2158_);
                    if v___x_2159_ == 2 {
                        v___x_2160_ = 0;
                        v___y_2122_ = v___x_2157_;
                        v___y_2123_ = v_a_2154_;
                        v___y_2124_ = v___x_2160_;
                        v___y_2125_ = v_outLv_2156_;
                        state = 6;
                        continue;
                    } else {
                        v___x_2161_ = 1;
                        v___y_2147_ = v___x_2157_;
                        v___y_2148_ = v_a_2154_;
                        v___y_2149_ = v___x_2161_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_a_2162_ = lean_ctor_get(v___x_2152_, 1);
                    lean_inc(v_a_2162_);
                    lean_dec_ref_known(v___x_2152_, 2);
                    v___x_2163_ = lean_box(0);
                    v___x_2164_ = 1;
                    v___y_2147_ = v___x_2163_;
                    v___y_2148_ = v_a_2162_;
                    v___y_2149_ = v___x_2164_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                v___x_2103_ = l_Lake_MainM_failure___redArg___boxed__const__1;
                v___x_2104_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2104_, 0, v___x_2103_);
                return v___x_2104_;
            }
            2 => {
                if v___y_2107_ == 0 {
                    if lean_obj_tag(v___y_2106_) == 0 {
                        state = 1;
                        continue;
                    } else {
                        v_val_2108_ = lean_ctor_get(v___y_2106_, 0);
                        v_isSharedCheck_2115_ = (!lean_is_exclusive(v___y_2106_)) as u8;
                        if v_isSharedCheck_2115_ == 0 {
                            v___x_2110_ = v___y_2106_;
                            v_isShared_2111_ = v_isSharedCheck_2115_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_2108_);
                            lean_dec(v___y_2106_);
                            v___x_2110_ = lean_box(0);
                            v_isShared_2111_ = v_isSharedCheck_2115_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_2106_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_2111_ == 0 {
                    lean_ctor_set_tag(v___x_2110_, 0);
                    v___x_2113_ = v___x_2110_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_val_2108_);
                    v___x_2113_ = v_reuseFailAlloc_2114_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2113_;
            }
            5 => {
                v___y_2106_ = v___y_2117_;
                v___y_2107_ = v___y_2118_;
                state = 2;
                continue;
            }
            6 => {
                v_ansiMode_2126_ = lean_ctor_get_uint8(
                    v_cfg_2100_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                v_out_2127_ = lean_ctor_get(v_cfg_2100_, 0);
                v___x_2128_ = l_Lake_OutStream_get(v_out_2127_);
                lean_inc_ref(v___x_2128_);
                v___x_2129_ = l_Lake_AnsiMode_isEnabled(v___x_2128_, v_ansiMode_2126_);
                v___x_2130_ = lean_unsigned_to_nat(0);
                v___x_2131_ = lean_array_get_size(v___y_2123_);
                v___x_2132_ = lean_nat_dec_lt(v___x_2130_, v___x_2131_);
                if v___x_2132_ == 0 {
                    lean_dec_ref(v___x_2128_);
                    lean_dec_ref(v___y_2123_);
                    v___y_2106_ = v___y_2122_;
                    v___y_2107_ = v___y_2124_;
                    state = 2;
                    continue;
                } else {
                    v___x_2133_ = lean_box((v___y_2125_) as usize);
                    v___x_2134_ = lean_box((v___x_2129_) as usize);
                    v___f_2135_ = lean_alloc_closure(
                        l_Lake_MainM_runLogIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        6,
                        3,
                    );
                    lean_closure_set(v___f_2135_, 0, v___x_2128_);
                    lean_closure_set(v___f_2135_, 1, v___x_2133_);
                    lean_closure_set(v___f_2135_, 2, v___x_2134_);
                    v___x_2136_ = lean_box(0);
                    v___x_2137_ = lean_nat_dec_le(v___x_2131_, v___x_2131_);
                    if v___x_2137_ == 0 {
                        if v___x_2132_ == 0 {
                            lean_dec_ref(v___f_2135_);
                            lean_dec_ref(v___y_2123_);
                            v___y_2106_ = v___y_2122_;
                            v___y_2107_ = v___y_2124_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2138_ = 0usize;
                            v___x_2139_ = lean_usize_of_nat(v___x_2131_);
                            v___x_141__overap_2140_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_2120_,
                                    v___f_2135_,
                                    v___y_2123_,
                                    v___x_2138_,
                                    v___x_2139_,
                                    v___x_2136_,
                                );
                            v___x_2141_ = lean_apply_1(v___x_141__overap_2140_, lean_box(0));
                            v___y_2117_ = v___y_2122_;
                            v___y_2118_ = v___y_2124_;
                            v___y_2119_ = v___x_2141_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v___x_2142_ = 0usize;
                        v___x_2143_ = lean_usize_of_nat(v___x_2131_);
                        v___x_145__overap_2144_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                lean_box(0),
                                lean_box(0),
                                lean_box(0),
                                v___x_2120_,
                                v___f_2135_,
                                v___y_2123_,
                                v___x_2142_,
                                v___x_2143_,
                                v___x_2136_,
                            );
                        v___x_2145_ = lean_apply_1(v___x_145__overap_2144_, lean_box(0));
                        v___y_2117_ = v___y_2122_;
                        v___y_2118_ = v___y_2124_;
                        v___y_2119_ = v___x_2145_;
                        state = 5;
                        continue;
                    }
                }
            }
            7 => {
                v___x_2150_ = 0;
                v___y_2122_ = v___y_2147_;
                v___y_2123_ = v___y_2148_;
                v___y_2124_ = v___y_2149_;
                v___y_2125_ = v___x_2150_;
                state = 6;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_MainM_runLogIO___redArg___boxed(
    mut v_x_2165_: *mut LeanObject,
    mut v_cfg_2166_: *mut LeanObject,
    mut v_a_2167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2168_: *mut LeanObject = core::ptr::null_mut();
    v_res_2168_ = l_Lake_MainM_runLogIO___redArg(v_x_2165_, v_cfg_2166_);
    lean_dec_ref(v_cfg_2166_);
    return v_res_2168_;
}
pub unsafe fn l_Lake_MainM_runLogIO(
    mut v_00_u03b1_2169_: *mut LeanObject,
    mut v_x_2170_: *mut LeanObject,
    mut v_cfg_2171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2178_: u8 = 0;
    let mut v_val_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2182_: u8 = 0;
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2186_: u8 = 0;
    let mut v___y_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2189_: u8 = 0;
    let mut v___y_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2195_: u8 = 0;
    let mut v___y_2196_: u8 = 0;
    let mut v_ansiMode_2197_: u8 = 0;
    let mut v_out_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: u8 = 0;
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: u8 = 0;
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: u8 = 0;
    let mut v___x_2209_: usize = 0;
    let mut v___x_2210_: usize = 0;
    let mut v___x_302__overap_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: usize = 0;
    let mut v___x_2214_: usize = 0;
    let mut v___x_305__overap_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2220_: u8 = 0;
    let mut v___x_2221_: u8 = 0;
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_failLv_2226_: u8 = 0;
    let mut v_outLv_2227_: u8 = 0;
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: u8 = 0;
    let mut v___x_2230_: u8 = 0;
    let mut v___x_2231_: u8 = 0;
    let mut v___x_2232_: u8 = 0;
    let mut v_a_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2191_ = l_instMonadBaseIO;
                v___x_2222_ = l_Lake_MainM_runLogIO___redArg___closed__0;
                v___x_2223_ = lean_apply_2(v_x_2170_, v___x_2222_, lean_box(0));
                if lean_obj_tag(v___x_2223_) == 0 {
                    v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
                    lean_inc(v_a_2224_);
                    v_a_2225_ = lean_ctor_get(v___x_2223_, 1);
                    lean_inc(v_a_2225_);
                    lean_dec_ref_known(v___x_2223_, 2);
                    v_failLv_2226_ = lean_ctor_get_uint8(
                        v_cfg_2171_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v_outLv_2227_ = lean_ctor_get_uint8(
                        v_cfg_2171_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    );
                    v___x_2228_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2228_, 0, v_a_2224_);
                    v___x_2229_ = l_Lake_Log_maxLv(v_a_2225_);
                    v___x_2230_ = l_Lake_instOrdLogLevel_ord(v_failLv_2226_, v___x_2229_);
                    if v___x_2230_ == 2 {
                        v___x_2231_ = 0;
                        v___y_2193_ = v___x_2228_;
                        v___y_2194_ = v_a_2225_;
                        v___y_2195_ = v___x_2231_;
                        v___y_2196_ = v_outLv_2227_;
                        state = 6;
                        continue;
                    } else {
                        v___x_2232_ = 1;
                        v___y_2218_ = v___x_2228_;
                        v___y_2219_ = v_a_2225_;
                        v___y_2220_ = v___x_2232_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_a_2233_ = lean_ctor_get(v___x_2223_, 1);
                    lean_inc(v_a_2233_);
                    lean_dec_ref_known(v___x_2223_, 2);
                    v___x_2234_ = lean_box(0);
                    v___x_2235_ = 1;
                    v___y_2218_ = v___x_2234_;
                    v___y_2219_ = v_a_2233_;
                    v___y_2220_ = v___x_2235_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                v___x_2174_ = l_Lake_MainM_failure___redArg___boxed__const__1;
                v___x_2175_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2175_, 0, v___x_2174_);
                return v___x_2175_;
            }
            2 => {
                if v___y_2178_ == 0 {
                    if lean_obj_tag(v___y_2177_) == 0 {
                        state = 1;
                        continue;
                    } else {
                        v_val_2179_ = lean_ctor_get(v___y_2177_, 0);
                        v_isSharedCheck_2186_ = (!lean_is_exclusive(v___y_2177_)) as u8;
                        if v_isSharedCheck_2186_ == 0 {
                            v___x_2181_ = v___y_2177_;
                            v_isShared_2182_ = v_isSharedCheck_2186_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_2179_);
                            lean_dec(v___y_2177_);
                            v___x_2181_ = lean_box(0);
                            v_isShared_2182_ = v_isSharedCheck_2186_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_2177_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_2182_ == 0 {
                    lean_ctor_set_tag(v___x_2181_, 0);
                    v___x_2184_ = v___x_2181_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_val_2179_);
                    v___x_2184_ = v_reuseFailAlloc_2185_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2184_;
            }
            5 => {
                v___y_2177_ = v___y_2188_;
                v___y_2178_ = v___y_2189_;
                state = 2;
                continue;
            }
            6 => {
                v_ansiMode_2197_ = lean_ctor_get_uint8(
                    v_cfg_2171_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                v_out_2198_ = lean_ctor_get(v_cfg_2171_, 0);
                v___x_2199_ = l_Lake_OutStream_get(v_out_2198_);
                lean_inc_ref(v___x_2199_);
                v___x_2200_ = l_Lake_AnsiMode_isEnabled(v___x_2199_, v_ansiMode_2197_);
                v___x_2201_ = lean_unsigned_to_nat(0);
                v___x_2202_ = lean_array_get_size(v___y_2194_);
                v___x_2203_ = lean_nat_dec_lt(v___x_2201_, v___x_2202_);
                if v___x_2203_ == 0 {
                    lean_dec_ref(v___x_2199_);
                    lean_dec_ref(v___y_2194_);
                    v___y_2177_ = v___y_2193_;
                    v___y_2178_ = v___y_2195_;
                    state = 2;
                    continue;
                } else {
                    v___x_2204_ = lean_box((v___y_2196_) as usize);
                    v___x_2205_ = lean_box((v___x_2200_) as usize);
                    v___f_2206_ = lean_alloc_closure(
                        l_Lake_MainM_runLogIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        6,
                        3,
                    );
                    lean_closure_set(v___f_2206_, 0, v___x_2199_);
                    lean_closure_set(v___f_2206_, 1, v___x_2204_);
                    lean_closure_set(v___f_2206_, 2, v___x_2205_);
                    v___x_2207_ = lean_box(0);
                    v___x_2208_ = lean_nat_dec_le(v___x_2202_, v___x_2202_);
                    if v___x_2208_ == 0 {
                        if v___x_2203_ == 0 {
                            lean_dec_ref(v___f_2206_);
                            lean_dec_ref(v___y_2194_);
                            v___y_2177_ = v___y_2193_;
                            v___y_2178_ = v___y_2195_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2209_ = 0usize;
                            v___x_2210_ = lean_usize_of_nat(v___x_2202_);
                            v___x_302__overap_2211_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    lean_box(0),
                                    lean_box(0),
                                    lean_box(0),
                                    v___x_2191_,
                                    v___f_2206_,
                                    v___y_2194_,
                                    v___x_2209_,
                                    v___x_2210_,
                                    v___x_2207_,
                                );
                            v___x_2212_ = lean_apply_1(v___x_302__overap_2211_, lean_box(0));
                            v___y_2188_ = v___y_2193_;
                            v___y_2189_ = v___y_2195_;
                            v___y_2190_ = v___x_2212_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v___x_2213_ = 0usize;
                        v___x_2214_ = lean_usize_of_nat(v___x_2202_);
                        v___x_305__overap_2215_ =
                            l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                lean_box(0),
                                lean_box(0),
                                lean_box(0),
                                v___x_2191_,
                                v___f_2206_,
                                v___y_2194_,
                                v___x_2213_,
                                v___x_2214_,
                                v___x_2207_,
                            );
                        v___x_2216_ = lean_apply_1(v___x_305__overap_2215_, lean_box(0));
                        v___y_2188_ = v___y_2193_;
                        v___y_2189_ = v___y_2195_;
                        v___y_2190_ = v___x_2216_;
                        state = 5;
                        continue;
                    }
                }
            }
            7 => {
                v___x_2221_ = 0;
                v___y_2193_ = v___y_2218_;
                v___y_2194_ = v___y_2219_;
                v___y_2195_ = v___y_2220_;
                v___y_2196_ = v___x_2221_;
                state = 6;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_MainM_runLogIO___boxed(
    mut v_00_u03b1_2236_: *mut LeanObject,
    mut v_x_2237_: *mut LeanObject,
    mut v_cfg_2238_: *mut LeanObject,
    mut v_a_2239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2240_: *mut LeanObject = core::ptr::null_mut();
    v_res_2240_ = l_Lake_MainM_runLogIO(v_00_u03b1_2236_, v_x_2237_, v_cfg_2238_);
    lean_dec_ref(v_cfg_2238_);
    return v_res_2240_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0(
    mut v_val_2241_: *mut LeanObject,
    mut v___y_2242_: u8,
    mut v_val_2243_: u8,
    mut v_as_2244_: *mut LeanObject,
    mut v_i_2245_: usize,
    mut v_stop_2246_: usize,
    mut v_b_2247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2249_: u8 = 0;
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: usize = 0;
    let mut v___x_2253_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2249_ = lean_usize_dec_eq(v_i_2245_, v_stop_2246_);
                if v___x_2249_ == 0 {
                    v___x_2250_ = lean_array_uget_borrowed(v_as_2244_, v_i_2245_);
                    lean_inc_ref(v_val_2241_);
                    v___x_2251_ =
                        l_Lake_logToStream(v___x_2250_, v_val_2241_, v___y_2242_, v_val_2243_);
                    v___x_2252_ = 1usize;
                    v___x_2253_ = lean_usize_add(v_i_2245_, v___x_2252_);
                    v_i_2245_ = v___x_2253_;
                    v_b_2247_ = v___x_2251_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_val_2241_);
                    return v_b_2247_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0___boxed(
    mut v_val_2255_: *mut LeanObject,
    mut v___y_2256_: *mut LeanObject,
    mut v_val_2257_: *mut LeanObject,
    mut v_as_2258_: *mut LeanObject,
    mut v_i_2259_: *mut LeanObject,
    mut v_stop_2260_: *mut LeanObject,
    mut v_b_2261_: *mut LeanObject,
    mut v___y_2262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_227__boxed_2263_: u8 = 0;
    let mut v_val_228__boxed_2264_: u8 = 0;
    let mut v_i_boxed_2265_: usize = 0;
    let mut v_stop_boxed_2266_: usize = 0;
    let mut v_res_2267_: *mut LeanObject = core::ptr::null_mut();
    v___y_227__boxed_2263_ = (lean_unbox(v___y_2256_) as u8);
    v_val_228__boxed_2264_ = (lean_unbox(v_val_2257_) as u8);
    v_i_boxed_2265_ = lean_unbox_usize(v_i_2259_);
    lean_dec(v_i_2259_);
    v_stop_boxed_2266_ = lean_unbox_usize(v_stop_2260_);
    lean_dec(v_stop_2260_);
    v_res_2267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0(v_val_2255_, v___y_227__boxed_2263_, v_val_228__boxed_2264_, v_as_2258_, v_i_boxed_2265_, v_stop_boxed_2266_, v_b_2261_);
    lean_dec_ref(v_as_2258_);
    return v_res_2267_;
}
pub unsafe fn l_Lake_MainM_liftLogIO___redArg(mut v_x_2268_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2275_: u8 = 0;
    let mut v_val_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2279_: u8 = 0;
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2283_: u8 = 0;
    let mut v___y_2285_: u8 = 0;
    let mut v___y_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: u8 = 0;
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2295_: u8 = 0;
    let mut v___y_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2297_: u8 = 0;
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: u8 = 0;
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: u8 = 0;
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: u8 = 0;
    let mut v___x_2304_: usize = 0;
    let mut v___x_2305_: usize = 0;
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: usize = 0;
    let mut v___x_2308_: usize = 0;
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2313_: u8 = 0;
    let mut v___x_2314_: u8 = 0;
    let mut v_a_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: u8 = 0;
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: u8 = 0;
    let mut v___x_2320_: u8 = 0;
    let mut v___x_2321_: u8 = 0;
    let mut v___x_2322_: u8 = 0;
    let mut v___x_2323_: u8 = 0;
    let mut v_a_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2288_ = lean_unsigned_to_nat(0);
                v___x_2289_ = l_Lake_MainM_runLogIO___redArg___closed__0;
                v___x_2290_ = lean_apply_2(v_x_2268_, v___x_2289_, lean_box(0));
                v___x_2291_ = 0;
                v___x_2292_ = lean_box(1);
                if lean_obj_tag(v___x_2290_) == 0 {
                    v_a_2315_ = lean_ctor_get(v___x_2290_, 0);
                    lean_inc(v_a_2315_);
                    v_a_2316_ = lean_ctor_get(v___x_2290_, 1);
                    lean_inc(v_a_2316_);
                    lean_dec_ref_known(v___x_2290_, 2);
                    v___x_2317_ = 3;
                    v___x_2318_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2318_, 0, v_a_2315_);
                    v___x_2319_ = l_Lake_Log_maxLv(v_a_2316_);
                    v___x_2320_ = l_Lake_instOrdLogLevel_ord(v___x_2317_, v___x_2319_);
                    if v___x_2320_ == 2 {
                        v___x_2321_ = 1;
                        v___x_2322_ = 0;
                        v___y_2294_ = v_a_2316_;
                        v___y_2295_ = v___x_2322_;
                        v___y_2296_ = v___x_2318_;
                        v___y_2297_ = v___x_2321_;
                        state = 6;
                        continue;
                    } else {
                        v___x_2323_ = 1;
                        v___y_2311_ = v_a_2316_;
                        v___y_2312_ = v___x_2318_;
                        v___y_2313_ = v___x_2323_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_a_2324_ = lean_ctor_get(v___x_2290_, 1);
                    lean_inc(v_a_2324_);
                    lean_dec_ref_known(v___x_2290_, 2);
                    v___x_2325_ = lean_box(0);
                    v___x_2326_ = 1;
                    v___y_2311_ = v_a_2324_;
                    v___y_2312_ = v___x_2325_;
                    v___y_2313_ = v___x_2326_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                v___x_2271_ = l_Lake_MainM_failure___redArg___boxed__const__1;
                v___x_2272_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2272_, 0, v___x_2271_);
                return v___x_2272_;
            }
            2 => {
                if v___y_2275_ == 0 {
                    if lean_obj_tag(v___y_2274_) == 0 {
                        state = 1;
                        continue;
                    } else {
                        v_val_2276_ = lean_ctor_get(v___y_2274_, 0);
                        v_isSharedCheck_2283_ = (!lean_is_exclusive(v___y_2274_)) as u8;
                        if v_isSharedCheck_2283_ == 0 {
                            v___x_2278_ = v___y_2274_;
                            v_isShared_2279_ = v_isSharedCheck_2283_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_2276_);
                            lean_dec(v___y_2274_);
                            v___x_2278_ = lean_box(0);
                            v_isShared_2279_ = v_isSharedCheck_2283_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_2274_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_2279_ == 0 {
                    lean_ctor_set_tag(v___x_2278_, 0);
                    v___x_2281_ = v___x_2278_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_val_2276_);
                    v___x_2281_ = v_reuseFailAlloc_2282_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2281_;
            }
            5 => {
                v___y_2274_ = v___y_2286_;
                v___y_2275_ = v___y_2285_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2298_ = l_Lake_OutStream_get(v___x_2292_);
                lean_inc_ref(v___x_2298_);
                v___x_2299_ = l_Lake_AnsiMode_isEnabled(v___x_2298_, v___x_2291_);
                v___x_2300_ = lean_array_get_size(v___y_2294_);
                v___x_2301_ = lean_nat_dec_lt(v___x_2288_, v___x_2300_);
                if v___x_2301_ == 0 {
                    lean_dec_ref(v___x_2298_);
                    lean_dec_ref(v___y_2294_);
                    v___y_2274_ = v___y_2296_;
                    v___y_2275_ = v___y_2295_;
                    state = 2;
                    continue;
                } else {
                    v___x_2302_ = lean_box(0);
                    v___x_2303_ = lean_nat_dec_le(v___x_2300_, v___x_2300_);
                    if v___x_2303_ == 0 {
                        if v___x_2301_ == 0 {
                            lean_dec_ref(v___x_2298_);
                            lean_dec_ref(v___y_2294_);
                            v___y_2274_ = v___y_2296_;
                            v___y_2275_ = v___y_2295_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2304_ = 0usize;
                            v___x_2305_ = lean_usize_of_nat(v___x_2300_);
                            v___x_2306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0(v___x_2298_, v___y_2297_, v___x_2299_, v___y_2294_, v___x_2304_, v___x_2305_, v___x_2302_);
                            lean_dec_ref(v___y_2294_);
                            v___y_2285_ = v___y_2295_;
                            v___y_2286_ = v___y_2296_;
                            v___y_2287_ = v___x_2306_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v___x_2307_ = 0usize;
                        v___x_2308_ = lean_usize_of_nat(v___x_2300_);
                        v___x_2309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0(v___x_2298_, v___y_2297_, v___x_2299_, v___y_2294_, v___x_2307_, v___x_2308_, v___x_2302_);
                        lean_dec_ref(v___y_2294_);
                        v___y_2285_ = v___y_2295_;
                        v___y_2286_ = v___y_2296_;
                        v___y_2287_ = v___x_2309_;
                        state = 5;
                        continue;
                    }
                }
            }
            7 => {
                v___x_2314_ = 0;
                v___y_2294_ = v___y_2311_;
                v___y_2295_ = v___y_2313_;
                v___y_2296_ = v___y_2312_;
                v___y_2297_ = v___x_2314_;
                state = 6;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_MainM_liftLogIO___redArg___boxed(
    mut v_x_2327_: *mut LeanObject,
    mut v_a_2328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2329_: *mut LeanObject = core::ptr::null_mut();
    v_res_2329_ = l_Lake_MainM_liftLogIO___redArg(v_x_2327_);
    return v_res_2329_;
}
pub unsafe fn l_Lake_MainM_liftLogIO(
    mut v_00_u03b1_2330_: *mut LeanObject,
    mut v_x_2331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    v___x_2333_ = l_Lake_MainM_liftLogIO___redArg(v_x_2331_);
    return v___x_2333_;
}
pub unsafe fn l_Lake_MainM_liftLogIO___boxed(
    mut v_00_u03b1_2334_: *mut LeanObject,
    mut v_x_2335_: *mut LeanObject,
    mut v_a_2336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2337_: *mut LeanObject = core::ptr::null_mut();
    v_res_2337_ = l_Lake_MainM_liftLogIO(v_00_u03b1_2334_, v_x_2335_);
    return v_res_2337_;
}
pub unsafe fn l_Lake_MainM_runLoggerIO___redArg___lam__0(
    mut v_val_2340_: *mut LeanObject,
    mut v_outLv_2341_: u8,
    mut v_val_2342_: u8,
    mut v_e_2343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    v___x_2345_ = l_Lake_logToStream(v_e_2343_, v_val_2340_, v_outLv_2341_, v_val_2342_);
    return v___x_2345_;
}
pub unsafe fn l_Lake_MainM_runLoggerIO___redArg___lam__0___boxed(
    mut v_val_2346_: *mut LeanObject,
    mut v_outLv_2347_: *mut LeanObject,
    mut v_val_2348_: *mut LeanObject,
    mut v_e_2349_: *mut LeanObject,
    mut v___y_2350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_outLv_boxed_2351_: u8 = 0;
    let mut v_val_188__boxed_2352_: u8 = 0;
    let mut v_res_2353_: *mut LeanObject = core::ptr::null_mut();
    v_outLv_boxed_2351_ = (lean_unbox(v_outLv_2347_) as u8);
    v_val_188__boxed_2352_ = (lean_unbox(v_val_2348_) as u8);
    v_res_2353_ = l_Lake_MainM_runLoggerIO___redArg___lam__0(
        v_val_2346_,
        v_outLv_boxed_2351_,
        v_val_188__boxed_2352_,
        v_e_2349_,
    );
    lean_dec_ref(v_e_2349_);
    return v_res_2353_;
}
pub unsafe fn l_Lake_MainM_runLoggerIO___redArg(
    mut v_x_2354_: *mut LeanObject,
    mut v_cfg_2355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_outLv_2357_: u8 = 0;
    let mut v_ansiMode_2358_: u8 = 0;
    let mut v_out_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: u8 = 0;
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2369_: u8 = 0;
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2373_: u8 = 0;
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2376_: u8 = 0;
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2381_: u8 = 0;
    let mut v_unused_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_outLv_2357_ = lean_ctor_get_uint8(
                    v_cfg_2355_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v_ansiMode_2358_ = lean_ctor_get_uint8(
                    v_cfg_2355_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                v_out_2359_ = lean_ctor_get(v_cfg_2355_, 0);
                v___x_2360_ = l_Lake_OutStream_get(v_out_2359_);
                lean_inc_ref(v___x_2360_);
                v___x_2361_ = l_Lake_AnsiMode_isEnabled(v___x_2360_, v_ansiMode_2358_);
                v___x_2362_ = lean_box((v_outLv_2357_) as usize);
                v___x_2363_ = lean_box((v___x_2361_) as usize);
                v___f_2364_ = lean_alloc_closure(
                    l_Lake_MainM_runLoggerIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                lean_closure_set(v___f_2364_, 0, v___x_2360_);
                lean_closure_set(v___f_2364_, 1, v___x_2362_);
                lean_closure_set(v___f_2364_, 2, v___x_2363_);
                v___x_2365_ = lean_apply_2(v_x_2354_, v___f_2364_, lean_box(0));
                if lean_obj_tag(v___x_2365_) == 0 {
                    v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
                    v_isSharedCheck_2373_ = (!lean_is_exclusive(v___x_2365_)) as u8;
                    if v_isSharedCheck_2373_ == 0 {
                        v___x_2368_ = v___x_2365_;
                        v_isShared_2369_ = v_isSharedCheck_2373_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2366_);
                        lean_dec(v___x_2365_);
                        v___x_2368_ = lean_box(0);
                        v_isShared_2369_ = v_isSharedCheck_2373_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_2381_ = (!lean_is_exclusive(v___x_2365_)) as u8;
                    if v_isSharedCheck_2381_ == 0 {
                        v_unused_2382_ = lean_ctor_get(v___x_2365_, 0);
                        lean_dec(v_unused_2382_);
                        v___x_2375_ = v___x_2365_;
                        v_isShared_2376_ = v_isSharedCheck_2381_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_2365_);
                        v___x_2375_ = lean_box(0);
                        v_isShared_2376_ = v_isSharedCheck_2381_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2369_ == 0 {
                    v___x_2371_ = v___x_2368_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
                    v___x_2371_ = v_reuseFailAlloc_2372_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2371_;
            }
            3 => {
                v___x_2377_ = l_Lake_MainM_failure___redArg___boxed__const__1;
                if v_isShared_2376_ == 0 {
                    lean_ctor_set(v___x_2375_, 0, v___x_2377_);
                    v___x_2379_ = v___x_2375_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2377_);
                    v___x_2379_ = v_reuseFailAlloc_2380_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2379_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_MainM_runLoggerIO___redArg___boxed(
    mut v_x_2383_: *mut LeanObject,
    mut v_cfg_2384_: *mut LeanObject,
    mut v_a_2385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2386_: *mut LeanObject = core::ptr::null_mut();
    v_res_2386_ = l_Lake_MainM_runLoggerIO___redArg(v_x_2383_, v_cfg_2384_);
    lean_dec_ref(v_cfg_2384_);
    return v_res_2386_;
}
pub unsafe fn l_Lake_MainM_runLoggerIO(
    mut v_00_u03b1_2387_: *mut LeanObject,
    mut v_x_2388_: *mut LeanObject,
    mut v_cfg_2389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_outLv_2391_: u8 = 0;
    let mut v_ansiMode_2392_: u8 = 0;
    let mut v_out_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: u8 = 0;
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2403_: u8 = 0;
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2407_: u8 = 0;
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2410_: u8 = 0;
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2415_: u8 = 0;
    let mut v_unused_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_outLv_2391_ = lean_ctor_get_uint8(
                    v_cfg_2389_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v_ansiMode_2392_ = lean_ctor_get_uint8(
                    v_cfg_2389_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                v_out_2393_ = lean_ctor_get(v_cfg_2389_, 0);
                v___x_2394_ = l_Lake_OutStream_get(v_out_2393_);
                lean_inc_ref(v___x_2394_);
                v___x_2395_ = l_Lake_AnsiMode_isEnabled(v___x_2394_, v_ansiMode_2392_);
                v___x_2396_ = lean_box((v_outLv_2391_) as usize);
                v___x_2397_ = lean_box((v___x_2395_) as usize);
                v___f_2398_ = lean_alloc_closure(
                    l_Lake_MainM_runLoggerIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                lean_closure_set(v___f_2398_, 0, v___x_2394_);
                lean_closure_set(v___f_2398_, 1, v___x_2396_);
                lean_closure_set(v___f_2398_, 2, v___x_2397_);
                v___x_2399_ = lean_apply_2(v_x_2388_, v___f_2398_, lean_box(0));
                if lean_obj_tag(v___x_2399_) == 0 {
                    v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
                    v_isSharedCheck_2407_ = (!lean_is_exclusive(v___x_2399_)) as u8;
                    if v_isSharedCheck_2407_ == 0 {
                        v___x_2402_ = v___x_2399_;
                        v_isShared_2403_ = v_isSharedCheck_2407_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2400_);
                        lean_dec(v___x_2399_);
                        v___x_2402_ = lean_box(0);
                        v_isShared_2403_ = v_isSharedCheck_2407_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_2415_ = (!lean_is_exclusive(v___x_2399_)) as u8;
                    if v_isSharedCheck_2415_ == 0 {
                        v_unused_2416_ = lean_ctor_get(v___x_2399_, 0);
                        lean_dec(v_unused_2416_);
                        v___x_2409_ = v___x_2399_;
                        v_isShared_2410_ = v_isSharedCheck_2415_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_2399_);
                        v___x_2409_ = lean_box(0);
                        v_isShared_2410_ = v_isSharedCheck_2415_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2403_ == 0 {
                    v___x_2405_ = v___x_2402_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
                    v___x_2405_ = v_reuseFailAlloc_2406_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2405_;
            }
            3 => {
                v___x_2411_ = l_Lake_MainM_failure___redArg___boxed__const__1;
                if v_isShared_2410_ == 0 {
                    lean_ctor_set(v___x_2409_, 0, v___x_2411_);
                    v___x_2413_ = v___x_2409_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2411_);
                    v___x_2413_ = v_reuseFailAlloc_2414_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_MainM_runLoggerIO___boxed(
    mut v_00_u03b1_2417_: *mut LeanObject,
    mut v_x_2418_: *mut LeanObject,
    mut v_cfg_2419_: *mut LeanObject,
    mut v_a_2420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2421_: *mut LeanObject = core::ptr::null_mut();
    v_res_2421_ = l_Lake_MainM_runLoggerIO(v_00_u03b1_2417_, v_x_2418_, v_cfg_2419_);
    lean_dec_ref(v_cfg_2419_);
    return v_res_2421_;
}
pub unsafe fn l_Lake_MainM_liftLoggerIO___redArg___lam__0(
    mut v_val_2422_: *mut LeanObject,
    mut v___x_2423_: u8,
    mut v_val_2424_: u8,
    mut v_e_2425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    v___x_2427_ = l_Lake_logToStream(v_e_2425_, v_val_2422_, v___x_2423_, v_val_2424_);
    return v___x_2427_;
}
pub unsafe fn l_Lake_MainM_liftLoggerIO___redArg___lam__0___boxed(
    mut v_val_2428_: *mut LeanObject,
    mut v___x_2429_: *mut LeanObject,
    mut v_val_2430_: *mut LeanObject,
    mut v_e_2431_: *mut LeanObject,
    mut v___y_2432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_38__boxed_2433_: u8 = 0;
    let mut v_val_39__boxed_2434_: u8 = 0;
    let mut v_res_2435_: *mut LeanObject = core::ptr::null_mut();
    v___x_38__boxed_2433_ = (lean_unbox(v___x_2429_) as u8);
    v_val_39__boxed_2434_ = (lean_unbox(v_val_2430_) as u8);
    v_res_2435_ = l_Lake_MainM_liftLoggerIO___redArg___lam__0(
        v_val_2428_,
        v___x_38__boxed_2433_,
        v_val_39__boxed_2434_,
        v_e_2431_,
    );
    lean_dec_ref(v_e_2431_);
    return v_res_2435_;
}
pub unsafe fn l_Lake_MainM_liftLoggerIO___redArg(
    mut v_x_2436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: u8 = 0;
    let mut v___x_2441_: u8 = 0;
    let mut v___x_2442_: u8 = 0;
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2450_: u8 = 0;
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2454_: u8 = 0;
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2457_: u8 = 0;
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2462_: u8 = 0;
    let mut v_unused_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2438_ = lean_box(1);
                v___x_2439_ = l_Lake_OutStream_get(v___x_2438_);
                v___x_2440_ = 0;
                lean_inc_ref(v___x_2439_);
                v___x_2441_ = l_Lake_AnsiMode_isEnabled(v___x_2439_, v___x_2440_);
                v___x_2442_ = 1;
                v___x_2443_ = lean_box((v___x_2442_) as usize);
                v___x_2444_ = lean_box((v___x_2441_) as usize);
                v___f_2445_ = lean_alloc_closure(
                    l_Lake_MainM_liftLoggerIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                lean_closure_set(v___f_2445_, 0, v___x_2439_);
                lean_closure_set(v___f_2445_, 1, v___x_2443_);
                lean_closure_set(v___f_2445_, 2, v___x_2444_);
                v___x_2446_ = lean_apply_2(v_x_2436_, v___f_2445_, lean_box(0));
                if lean_obj_tag(v___x_2446_) == 0 {
                    v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
                    v_isSharedCheck_2454_ = (!lean_is_exclusive(v___x_2446_)) as u8;
                    if v_isSharedCheck_2454_ == 0 {
                        v___x_2449_ = v___x_2446_;
                        v_isShared_2450_ = v_isSharedCheck_2454_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2447_);
                        lean_dec(v___x_2446_);
                        v___x_2449_ = lean_box(0);
                        v_isShared_2450_ = v_isSharedCheck_2454_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_2462_ = (!lean_is_exclusive(v___x_2446_)) as u8;
                    if v_isSharedCheck_2462_ == 0 {
                        v_unused_2463_ = lean_ctor_get(v___x_2446_, 0);
                        lean_dec(v_unused_2463_);
                        v___x_2456_ = v___x_2446_;
                        v_isShared_2457_ = v_isSharedCheck_2462_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_2446_);
                        v___x_2456_ = lean_box(0);
                        v_isShared_2457_ = v_isSharedCheck_2462_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2450_ == 0 {
                    v___x_2452_ = v___x_2449_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
                    v___x_2452_ = v_reuseFailAlloc_2453_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2452_;
            }
            3 => {
                v___x_2458_ = l_Lake_MainM_failure___redArg___boxed__const__1;
                if v_isShared_2457_ == 0 {
                    lean_ctor_set(v___x_2456_, 0, v___x_2458_);
                    v___x_2460_ = v___x_2456_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2458_);
                    v___x_2460_ = v_reuseFailAlloc_2461_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2460_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_MainM_liftLoggerIO___redArg___boxed(
    mut v_x_2464_: *mut LeanObject,
    mut v_a_2465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2466_: *mut LeanObject = core::ptr::null_mut();
    v_res_2466_ = l_Lake_MainM_liftLoggerIO___redArg(v_x_2464_);
    return v_res_2466_;
}
pub unsafe fn l_Lake_MainM_liftLoggerIO(
    mut v_00_u03b1_2467_: *mut LeanObject,
    mut v_x_2468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    v___x_2470_ = l_Lake_MainM_liftLoggerIO___redArg(v_x_2468_);
    return v___x_2470_;
}
pub unsafe fn l_Lake_MainM_liftLoggerIO___boxed(
    mut v_00_u03b1_2471_: *mut LeanObject,
    mut v_x_2472_: *mut LeanObject,
    mut v_a_2473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2474_: *mut LeanObject = core::ptr::null_mut();
    v_res_2474_ = l_Lake_MainM_liftLoggerIO(v_00_u03b1_2471_, v_x_2472_);
    return v_res_2474_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_MainM(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Util_Log(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Exit(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lake_MainM_tryCatchError___redArg___boxed__const__1 =
        _init_l_Lake_MainM_tryCatchError___redArg___boxed__const__1();
    lean_mark_persistent(l_Lake_MainM_tryCatchError___redArg___boxed__const__1);
    l_Lake_MainM_failure___redArg___boxed__const__1 =
        _init_l_Lake_MainM_failure___redArg___boxed__const__1();
    lean_mark_persistent(l_Lake_MainM_failure___redArg___boxed__const__1);
    l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative =
        _init_l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative();
    lean_mark_persistent(l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_MainM(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_MainM(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Util_Log(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Exit(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_MainM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Util_MainM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Util_MainM(builtin);
}

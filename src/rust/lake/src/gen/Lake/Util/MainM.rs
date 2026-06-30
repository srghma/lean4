// Lean compiler output
// Module: Lake.Util.MainM
// Imports: Lake.Util.Log Lake.Util.Exit
use crate::ffi::{
    lean_array_get_size, lean_array_uget_borrowed, lean_nat_dec_le, lean_nat_dec_lt,
    lean_uint32_dec_eq, lean_usize_add, lean_usize_dec_eq, lean_usize_of_nat,
};
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
pub static l_Lake_instMonadMainM___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadMainM___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadMainM___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadMainM___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_instMonadMainM___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadMainM___aux__3___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadMainM___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadMainM___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lake_instMonadMainM___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instMonadMainM___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instMonadMainM___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instMonadMainM___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadMainM___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lake_instMonadMainM___closed__3_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadMainM___aux__5___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadMainM___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadMainM___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lake_instMonadMainM___closed__4_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadMainM___aux__7___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadMainM___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadMainM___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lake_instMonadMainM___closed__5_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadMainM___aux__9___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadMainM___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadMainM___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lake_instMonadMainM___closed__6_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadMainM___aux__11___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadMainM___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadMainM___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lake_instMonadMainM___closed__7_value: leanh::LeanCtorObject<5> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instMonadMainM___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instMonadMainM___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instMonadMainM___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instMonadMainM___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instMonadMainM___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instMonadMainM___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadMainM___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lake_instMonadMainM___closed__8_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadMainM___aux__13___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadMainM___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadMainM___closed__8_value) as *mut leanh::LeanObject;
pub static l_Lake_instMonadMainM___closed__9_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instMonadMainM___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_instMonadMainM___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instMonadMainM___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadMainM___closed__9_value) as *mut leanh::LeanObject;
pub static mut l_Lake_instMonadMainM: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadMainM___closed__9_value) as *mut leanh::LeanObject;
pub static l_Lake_instMonadFinallyMainM___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadFinallyMainM___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadFinallyMainM___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadFinallyMainM___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instMonadFinallyMainM: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadFinallyMainM___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instMonadLiftBaseIOMainM___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instMonadLiftBaseIOMainM___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instMonadLiftBaseIOMainM___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadLiftBaseIOMainM___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instMonadLiftBaseIOMainM: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instMonadLiftBaseIOMainM___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_MainM_instMonadExit___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_MainM_exit___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_MainM_instMonadExit___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_instMonadExit___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_MainM_instMonadExit: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_instMonadExit___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_MainM_tryCatchError___redArg___boxed__const__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_MainM_failure___redArg___boxed__const__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__0_value:
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
    m_fun: l_Lake_MainM_failure___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__1_value:
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
    m_fun: l_Lake_MainM_orElse___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__1_value
) as *mut leanh::LeanObject;
pub static mut l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_MainM_instMonadLog___closed__0_value: leanh::LeanClosureObject<3> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_MainM_instMonadLog___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 3,
        m_objs: [
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_MainM_instMonadLog___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_instMonadLog___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_MainM_instMonadLog: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_instMonadLog___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_MainM_instMonadError___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_MainM_instMonadError___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_MainM_instMonadError___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_instMonadError___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_MainM_instMonadError: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_instMonadError___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_MainM_instMonadLiftIO___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_MainM_instMonadLiftIO___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_MainM_instMonadLiftIO___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_instMonadLiftIO___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_MainM_instMonadLiftIO: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_instMonadLiftIO___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_MainM_runLogIO___redArg___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lake_MainM_runLogIO___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_runLogIO___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_MainM_instMonadLiftLogIO___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_MainM_liftLogIO___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_MainM_instMonadLiftLogIO___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_instMonadLiftLogIO___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_MainM_instMonadLiftLogIO: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_instMonadLiftLogIO___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_MainM_instMonadLiftLoggerIO___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_MainM_liftLoggerIO___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_MainM_instMonadLiftLoggerIO___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_instMonadLiftLoggerIO___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_MainM_instMonadLiftLoggerIO: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_MainM_instMonadLiftLoggerIO___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lake_instMonadMainM___aux__1___redArg(
    mut v_a_1239_: *mut leanh::LeanObject,
    mut v_a_1240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1246_: u8 = 0;
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1251_: u8 = 0;
    let mut v_a_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1255_: u8 = 0;
    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1259_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1242_ = leanh::lean_apply_1(v_a_1240_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1242_) == 0 {
                    v_a_1243_ = leanh::lean_ctor_get(v___x_1242_, 0);
                    v_isSharedCheck_1251_ = (!leanh::lean_is_exclusive(v___x_1242_)) as u8;
                    if v_isSharedCheck_1251_ == 0 {
                        v___x_1245_ = v___x_1242_;
                        v_isShared_1246_ = v_isSharedCheck_1251_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1243_);
                        leanh::lean_dec(v___x_1242_);
                        v___x_1245_ = leanh::lean_box(0);
                        v_isShared_1246_ = v_isSharedCheck_1251_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1239_);
                    v_a_1252_ = leanh::lean_ctor_get(v___x_1242_, 0);
                    v_isSharedCheck_1259_ = (!leanh::lean_is_exclusive(v___x_1242_)) as u8;
                    if v_isSharedCheck_1259_ == 0 {
                        v___x_1254_ = v___x_1242_;
                        v_isShared_1255_ = v_isSharedCheck_1259_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1252_);
                        leanh::lean_dec(v___x_1242_);
                        v___x_1254_ = leanh::lean_box(0);
                        v_isShared_1255_ = v_isSharedCheck_1259_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1247_ = leanh::lean_apply_1(v_a_1239_, v_a_1243_);
                if v_isShared_1246_ == 0 {
                    leanh::lean_ctor_set(v___x_1245_, 0, v___x_1247_);
                    v___x_1249_ = v___x_1245_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1250_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1247_);
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
                    v_reuseFailAlloc_1258_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
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
    mut v_a_1260_: *mut leanh::LeanObject,
    mut v_a_1261_: *mut leanh::LeanObject,
    mut v_a_1262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1263_ = l_Lake_instMonadMainM___aux__1___redArg(v_a_1260_, v_a_1261_);
    return v_res_1263_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__1(
    mut v_00_u03b1_1264_: *mut leanh::LeanObject,
    mut v_00_u03b2_1265_: *mut leanh::LeanObject,
    mut v_a_1266_: *mut leanh::LeanObject,
    mut v_a_1267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1273_: u8 = 0;
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1278_: u8 = 0;
    let mut v_a_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1282_: u8 = 0;
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1286_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1269_ = leanh::lean_apply_1(v_a_1267_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1269_) == 0 {
                    v_a_1270_ = leanh::lean_ctor_get(v___x_1269_, 0);
                    v_isSharedCheck_1278_ = (!leanh::lean_is_exclusive(v___x_1269_)) as u8;
                    if v_isSharedCheck_1278_ == 0 {
                        v___x_1272_ = v___x_1269_;
                        v_isShared_1273_ = v_isSharedCheck_1278_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1270_);
                        leanh::lean_dec(v___x_1269_);
                        v___x_1272_ = leanh::lean_box(0);
                        v_isShared_1273_ = v_isSharedCheck_1278_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1266_);
                    v_a_1279_ = leanh::lean_ctor_get(v___x_1269_, 0);
                    v_isSharedCheck_1286_ = (!leanh::lean_is_exclusive(v___x_1269_)) as u8;
                    if v_isSharedCheck_1286_ == 0 {
                        v___x_1281_ = v___x_1269_;
                        v_isShared_1282_ = v_isSharedCheck_1286_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1279_);
                        leanh::lean_dec(v___x_1269_);
                        v___x_1281_ = leanh::lean_box(0);
                        v_isShared_1282_ = v_isSharedCheck_1286_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1274_ = leanh::lean_apply_1(v_a_1266_, v_a_1270_);
                if v_isShared_1273_ == 0 {
                    leanh::lean_ctor_set(v___x_1272_, 0, v___x_1274_);
                    v___x_1276_ = v___x_1272_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1277_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1274_);
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
                    v_reuseFailAlloc_1285_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
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
    mut v_00_u03b1_1287_: *mut leanh::LeanObject,
    mut v_00_u03b2_1288_: *mut leanh::LeanObject,
    mut v_a_1289_: *mut leanh::LeanObject,
    mut v_a_1290_: *mut leanh::LeanObject,
    mut v_a_1291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1292_ =
        l_Lake_instMonadMainM___aux__1(v_00_u03b1_1287_, v_00_u03b2_1288_, v_a_1289_, v_a_1290_);
    return v_res_1292_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__3___redArg(
    mut v_a_1293_: *mut leanh::LeanObject,
    mut v_a_1294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1299_: u8 = 0;
    let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1303_: u8 = 0;
    let mut v_unused_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1308_: u8 = 0;
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1312_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1296_ = leanh::lean_apply_1(v_a_1294_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1296_) == 0 {
                    v_isSharedCheck_1303_ = (!leanh::lean_is_exclusive(v___x_1296_)) as u8;
                    if v_isSharedCheck_1303_ == 0 {
                        v_unused_1304_ = leanh::lean_ctor_get(v___x_1296_, 0);
                        leanh::lean_dec(v_unused_1304_);
                        v___x_1298_ = v___x_1296_;
                        v_isShared_1299_ = v_isSharedCheck_1303_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1296_);
                        v___x_1298_ = leanh::lean_box(0);
                        v_isShared_1299_ = v_isSharedCheck_1303_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1293_);
                    v_a_1305_ = leanh::lean_ctor_get(v___x_1296_, 0);
                    v_isSharedCheck_1312_ = (!leanh::lean_is_exclusive(v___x_1296_)) as u8;
                    if v_isSharedCheck_1312_ == 0 {
                        v___x_1307_ = v___x_1296_;
                        v_isShared_1308_ = v_isSharedCheck_1312_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1305_);
                        leanh::lean_dec(v___x_1296_);
                        v___x_1307_ = leanh::lean_box(0);
                        v_isShared_1308_ = v_isSharedCheck_1312_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1299_ == 0 {
                    leanh::lean_ctor_set(v___x_1298_, 0, v_a_1293_);
                    v___x_1301_ = v___x_1298_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1302_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1293_);
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
                    v_reuseFailAlloc_1311_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
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
    mut v_a_1313_: *mut leanh::LeanObject,
    mut v_a_1314_: *mut leanh::LeanObject,
    mut v_a_1315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1316_ = l_Lake_instMonadMainM___aux__3___redArg(v_a_1313_, v_a_1314_);
    return v_res_1316_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__3(
    mut v_00_u03b1_1317_: *mut leanh::LeanObject,
    mut v_00_u03b2_1318_: *mut leanh::LeanObject,
    mut v_a_1319_: *mut leanh::LeanObject,
    mut v_a_1320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1325_: u8 = 0;
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1329_: u8 = 0;
    let mut v_unused_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1334_: u8 = 0;
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1338_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1322_ = leanh::lean_apply_1(v_a_1320_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1322_) == 0 {
                    v_isSharedCheck_1329_ = (!leanh::lean_is_exclusive(v___x_1322_)) as u8;
                    if v_isSharedCheck_1329_ == 0 {
                        v_unused_1330_ = leanh::lean_ctor_get(v___x_1322_, 0);
                        leanh::lean_dec(v_unused_1330_);
                        v___x_1324_ = v___x_1322_;
                        v_isShared_1325_ = v_isSharedCheck_1329_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1322_);
                        v___x_1324_ = leanh::lean_box(0);
                        v_isShared_1325_ = v_isSharedCheck_1329_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1319_);
                    v_a_1331_ = leanh::lean_ctor_get(v___x_1322_, 0);
                    v_isSharedCheck_1338_ = (!leanh::lean_is_exclusive(v___x_1322_)) as u8;
                    if v_isSharedCheck_1338_ == 0 {
                        v___x_1333_ = v___x_1322_;
                        v_isShared_1334_ = v_isSharedCheck_1338_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1331_);
                        leanh::lean_dec(v___x_1322_);
                        v___x_1333_ = leanh::lean_box(0);
                        v_isShared_1334_ = v_isSharedCheck_1338_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1325_ == 0 {
                    leanh::lean_ctor_set(v___x_1324_, 0, v_a_1319_);
                    v___x_1327_ = v___x_1324_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1328_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1319_);
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
                    v_reuseFailAlloc_1337_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
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
    mut v_00_u03b1_1339_: *mut leanh::LeanObject,
    mut v_00_u03b2_1340_: *mut leanh::LeanObject,
    mut v_a_1341_: *mut leanh::LeanObject,
    mut v_a_1342_: *mut leanh::LeanObject,
    mut v_a_1343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1344_ =
        l_Lake_instMonadMainM___aux__3(v_00_u03b1_1339_, v_00_u03b2_1340_, v_a_1341_, v_a_1342_);
    return v_res_1344_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__5___redArg(
    mut v_a_1345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1347_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1347_, 0, v_a_1345_);
    return v___x_1347_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__5___redArg___boxed(
    mut v_a_1348_: *mut leanh::LeanObject,
    mut v_a_1349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1350_ = l_Lake_instMonadMainM___aux__5___redArg(v_a_1348_);
    return v_res_1350_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__5(
    mut v_00_u03b1_1351_: *mut leanh::LeanObject,
    mut v_a_1352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1354_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1354_, 0, v_a_1352_);
    return v___x_1354_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__5___boxed(
    mut v_00_u03b1_1355_: *mut leanh::LeanObject,
    mut v_a_1356_: *mut leanh::LeanObject,
    mut v_a_1357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1358_ = l_Lake_instMonadMainM___aux__5(v_00_u03b1_1355_, v_a_1356_);
    return v_res_1358_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__7___redArg(
    mut v_a_1359_: *mut leanh::LeanObject,
    mut v_a_1360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1369_: u8 = 0;
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1374_: u8 = 0;
    let mut v_a_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1378_: u8 = 0;
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1382_: u8 = 0;
    let mut v_a_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1386_: u8 = 0;
    let mut v___x_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1390_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1362_ = leanh::lean_apply_1(v_a_1359_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1362_) == 0 {
                    v_a_1363_ = leanh::lean_ctor_get(v___x_1362_, 0);
                    leanh::lean_inc(v_a_1363_);
                    leanh::lean_dec_ref_known(v___x_1362_, 1);
                    v___x_1364_ = leanh::lean_box(0);
                    v___x_1365_ = leanh::lean_apply_2(
                        v_a_1360_,
                        v___x_1364_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_1365_) == 0 {
                        v_a_1366_ = leanh::lean_ctor_get(v___x_1365_, 0);
                        v_isSharedCheck_1374_ =
                            (!leanh::lean_is_exclusive(v___x_1365_)) as u8;
                        if v_isSharedCheck_1374_ == 0 {
                            v___x_1368_ = v___x_1365_;
                            v_isShared_1369_ = v_isSharedCheck_1374_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1366_);
                            leanh::lean_dec(v___x_1365_);
                            v___x_1368_ = leanh::lean_box(0);
                            v_isShared_1369_ = v_isSharedCheck_1374_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1363_);
                        v_a_1375_ = leanh::lean_ctor_get(v___x_1365_, 0);
                        v_isSharedCheck_1382_ =
                            (!leanh::lean_is_exclusive(v___x_1365_)) as u8;
                        if v_isSharedCheck_1382_ == 0 {
                            v___x_1377_ = v___x_1365_;
                            v_isShared_1378_ = v_isSharedCheck_1382_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1375_);
                            leanh::lean_dec(v___x_1365_);
                            v___x_1377_ = leanh::lean_box(0);
                            v_isShared_1378_ = v_isSharedCheck_1382_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_a_1360_);
                    v_a_1383_ = leanh::lean_ctor_get(v___x_1362_, 0);
                    v_isSharedCheck_1390_ = (!leanh::lean_is_exclusive(v___x_1362_)) as u8;
                    if v_isSharedCheck_1390_ == 0 {
                        v___x_1385_ = v___x_1362_;
                        v_isShared_1386_ = v_isSharedCheck_1390_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1383_);
                        leanh::lean_dec(v___x_1362_);
                        v___x_1385_ = leanh::lean_box(0);
                        v_isShared_1386_ = v_isSharedCheck_1390_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1370_ = leanh::lean_apply_1(v_a_1363_, v_a_1366_);
                if v_isShared_1369_ == 0 {
                    leanh::lean_ctor_set(v___x_1368_, 0, v___x_1370_);
                    v___x_1372_ = v___x_1368_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1373_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
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
                    v_reuseFailAlloc_1381_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1375_);
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
                    v_reuseFailAlloc_1389_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
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
    mut v_a_1391_: *mut leanh::LeanObject,
    mut v_a_1392_: *mut leanh::LeanObject,
    mut v_a_1393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1394_ = l_Lake_instMonadMainM___aux__7___redArg(v_a_1391_, v_a_1392_);
    return v_res_1394_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__7(
    mut v_00_u03b1_1395_: *mut leanh::LeanObject,
    mut v_00_u03b2_1396_: *mut leanh::LeanObject,
    mut v_a_1397_: *mut leanh::LeanObject,
    mut v_a_1398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1407_: u8 = 0;
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1412_: u8 = 0;
    let mut v_a_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1416_: u8 = 0;
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1420_: u8 = 0;
    let mut v_a_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1424_: u8 = 0;
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1428_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1400_ = leanh::lean_apply_1(v_a_1397_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1400_) == 0 {
                    v_a_1401_ = leanh::lean_ctor_get(v___x_1400_, 0);
                    leanh::lean_inc(v_a_1401_);
                    leanh::lean_dec_ref_known(v___x_1400_, 1);
                    v___x_1402_ = leanh::lean_box(0);
                    v___x_1403_ = leanh::lean_apply_2(
                        v_a_1398_,
                        v___x_1402_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_1403_) == 0 {
                        v_a_1404_ = leanh::lean_ctor_get(v___x_1403_, 0);
                        v_isSharedCheck_1412_ =
                            (!leanh::lean_is_exclusive(v___x_1403_)) as u8;
                        if v_isSharedCheck_1412_ == 0 {
                            v___x_1406_ = v___x_1403_;
                            v_isShared_1407_ = v_isSharedCheck_1412_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1404_);
                            leanh::lean_dec(v___x_1403_);
                            v___x_1406_ = leanh::lean_box(0);
                            v_isShared_1407_ = v_isSharedCheck_1412_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1401_);
                        v_a_1413_ = leanh::lean_ctor_get(v___x_1403_, 0);
                        v_isSharedCheck_1420_ =
                            (!leanh::lean_is_exclusive(v___x_1403_)) as u8;
                        if v_isSharedCheck_1420_ == 0 {
                            v___x_1415_ = v___x_1403_;
                            v_isShared_1416_ = v_isSharedCheck_1420_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1413_);
                            leanh::lean_dec(v___x_1403_);
                            v___x_1415_ = leanh::lean_box(0);
                            v_isShared_1416_ = v_isSharedCheck_1420_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_a_1398_);
                    v_a_1421_ = leanh::lean_ctor_get(v___x_1400_, 0);
                    v_isSharedCheck_1428_ = (!leanh::lean_is_exclusive(v___x_1400_)) as u8;
                    if v_isSharedCheck_1428_ == 0 {
                        v___x_1423_ = v___x_1400_;
                        v_isShared_1424_ = v_isSharedCheck_1428_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1421_);
                        leanh::lean_dec(v___x_1400_);
                        v___x_1423_ = leanh::lean_box(0);
                        v_isShared_1424_ = v_isSharedCheck_1428_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1408_ = leanh::lean_apply_1(v_a_1401_, v_a_1404_);
                if v_isShared_1407_ == 0 {
                    leanh::lean_ctor_set(v___x_1406_, 0, v___x_1408_);
                    v___x_1410_ = v___x_1406_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1411_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1408_);
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
                    v_reuseFailAlloc_1419_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
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
                    v_reuseFailAlloc_1427_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
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
    mut v_00_u03b1_1429_: *mut leanh::LeanObject,
    mut v_00_u03b2_1430_: *mut leanh::LeanObject,
    mut v_a_1431_: *mut leanh::LeanObject,
    mut v_a_1432_: *mut leanh::LeanObject,
    mut v_a_1433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1434_ =
        l_Lake_instMonadMainM___aux__7(v_00_u03b1_1429_, v_00_u03b2_1430_, v_a_1431_, v_a_1432_);
    return v_res_1434_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__9___redArg(
    mut v_a_1435_: *mut leanh::LeanObject,
    mut v_a_1436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1444_: u8 = 0;
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1448_: u8 = 0;
    let mut v_unused_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1453_: u8 = 0;
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1457_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1438_ = leanh::lean_apply_1(v_a_1435_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1438_) == 0 {
                    v_a_1439_ = leanh::lean_ctor_get(v___x_1438_, 0);
                    leanh::lean_inc(v_a_1439_);
                    leanh::lean_dec_ref_known(v___x_1438_, 1);
                    v___x_1440_ = leanh::lean_box(0);
                    v___x_1441_ = leanh::lean_apply_2(
                        v_a_1436_,
                        v___x_1440_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_1441_) == 0 {
                        v_isSharedCheck_1448_ =
                            (!leanh::lean_is_exclusive(v___x_1441_)) as u8;
                        if v_isSharedCheck_1448_ == 0 {
                            v_unused_1449_ = leanh::lean_ctor_get(v___x_1441_, 0);
                            leanh::lean_dec(v_unused_1449_);
                            v___x_1443_ = v___x_1441_;
                            v_isShared_1444_ = v_isSharedCheck_1448_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1441_);
                            v___x_1443_ = leanh::lean_box(0);
                            v_isShared_1444_ = v_isSharedCheck_1448_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1439_);
                        v_a_1450_ = leanh::lean_ctor_get(v___x_1441_, 0);
                        v_isSharedCheck_1457_ =
                            (!leanh::lean_is_exclusive(v___x_1441_)) as u8;
                        if v_isSharedCheck_1457_ == 0 {
                            v___x_1452_ = v___x_1441_;
                            v_isShared_1453_ = v_isSharedCheck_1457_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1450_);
                            leanh::lean_dec(v___x_1441_);
                            v___x_1452_ = leanh::lean_box(0);
                            v_isShared_1453_ = v_isSharedCheck_1457_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_a_1436_);
                    return v___x_1438_;
                }
            }
            1 => {
                if v_isShared_1444_ == 0 {
                    leanh::lean_ctor_set(v___x_1443_, 0, v_a_1439_);
                    v___x_1446_ = v___x_1443_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1447_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1439_);
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
                    v_reuseFailAlloc_1456_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
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
    mut v_a_1458_: *mut leanh::LeanObject,
    mut v_a_1459_: *mut leanh::LeanObject,
    mut v_a_1460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1461_ = l_Lake_instMonadMainM___aux__9___redArg(v_a_1458_, v_a_1459_);
    return v_res_1461_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__9(
    mut v_00_u03b1_1462_: *mut leanh::LeanObject,
    mut v_00_u03b2_1463_: *mut leanh::LeanObject,
    mut v_a_1464_: *mut leanh::LeanObject,
    mut v_a_1465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1473_: u8 = 0;
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1477_: u8 = 0;
    let mut v_unused_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1482_: u8 = 0;
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1486_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1467_ = leanh::lean_apply_1(v_a_1464_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1467_) == 0 {
                    v_a_1468_ = leanh::lean_ctor_get(v___x_1467_, 0);
                    leanh::lean_inc(v_a_1468_);
                    leanh::lean_dec_ref_known(v___x_1467_, 1);
                    v___x_1469_ = leanh::lean_box(0);
                    v___x_1470_ = leanh::lean_apply_2(
                        v_a_1465_,
                        v___x_1469_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_1470_) == 0 {
                        v_isSharedCheck_1477_ =
                            (!leanh::lean_is_exclusive(v___x_1470_)) as u8;
                        if v_isSharedCheck_1477_ == 0 {
                            v_unused_1478_ = leanh::lean_ctor_get(v___x_1470_, 0);
                            leanh::lean_dec(v_unused_1478_);
                            v___x_1472_ = v___x_1470_;
                            v_isShared_1473_ = v_isSharedCheck_1477_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1470_);
                            v___x_1472_ = leanh::lean_box(0);
                            v_isShared_1473_ = v_isSharedCheck_1477_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1468_);
                        v_a_1479_ = leanh::lean_ctor_get(v___x_1470_, 0);
                        v_isSharedCheck_1486_ =
                            (!leanh::lean_is_exclusive(v___x_1470_)) as u8;
                        if v_isSharedCheck_1486_ == 0 {
                            v___x_1481_ = v___x_1470_;
                            v_isShared_1482_ = v_isSharedCheck_1486_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1479_);
                            leanh::lean_dec(v___x_1470_);
                            v___x_1481_ = leanh::lean_box(0);
                            v_isShared_1482_ = v_isSharedCheck_1486_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_a_1465_);
                    return v___x_1467_;
                }
            }
            1 => {
                if v_isShared_1473_ == 0 {
                    leanh::lean_ctor_set(v___x_1472_, 0, v_a_1468_);
                    v___x_1475_ = v___x_1472_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1476_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1468_);
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
                    v_reuseFailAlloc_1485_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
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
    mut v_00_u03b1_1487_: *mut leanh::LeanObject,
    mut v_00_u03b2_1488_: *mut leanh::LeanObject,
    mut v_a_1489_: *mut leanh::LeanObject,
    mut v_a_1490_: *mut leanh::LeanObject,
    mut v_a_1491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1492_ =
        l_Lake_instMonadMainM___aux__9(v_00_u03b1_1487_, v_00_u03b2_1488_, v_a_1489_, v_a_1490_);
    return v_res_1492_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__11___redArg(
    mut v_a_1493_: *mut leanh::LeanObject,
    mut v_a_1494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1502_: u8 = 0;
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1496_ = leanh::lean_apply_1(v_a_1493_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1496_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1496_, 1);
                    v___x_1497_ = leanh::lean_box(0);
                    v___x_1498_ = leanh::lean_apply_2(
                        v_a_1494_,
                        v___x_1497_,
                        leanh::lean_box(0),
                    );
                    return v___x_1498_;
                } else {
                    leanh::lean_dec_ref(v_a_1494_);
                    v_a_1499_ = leanh::lean_ctor_get(v___x_1496_, 0);
                    v_isSharedCheck_1506_ = (!leanh::lean_is_exclusive(v___x_1496_)) as u8;
                    if v_isSharedCheck_1506_ == 0 {
                        v___x_1501_ = v___x_1496_;
                        v_isShared_1502_ = v_isSharedCheck_1506_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1499_);
                        leanh::lean_dec(v___x_1496_);
                        v___x_1501_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1505_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
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
    mut v_a_1507_: *mut leanh::LeanObject,
    mut v_a_1508_: *mut leanh::LeanObject,
    mut v_a_1509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1510_ = l_Lake_instMonadMainM___aux__11___redArg(v_a_1507_, v_a_1508_);
    return v_res_1510_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__11(
    mut v_00_u03b1_1511_: *mut leanh::LeanObject,
    mut v_00_u03b2_1512_: *mut leanh::LeanObject,
    mut v_a_1513_: *mut leanh::LeanObject,
    mut v_a_1514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1522_: u8 = 0;
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1526_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1516_ = leanh::lean_apply_1(v_a_1513_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1516_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1516_, 1);
                    v___x_1517_ = leanh::lean_box(0);
                    v___x_1518_ = leanh::lean_apply_2(
                        v_a_1514_,
                        v___x_1517_,
                        leanh::lean_box(0),
                    );
                    return v___x_1518_;
                } else {
                    leanh::lean_dec_ref(v_a_1514_);
                    v_a_1519_ = leanh::lean_ctor_get(v___x_1516_, 0);
                    v_isSharedCheck_1526_ = (!leanh::lean_is_exclusive(v___x_1516_)) as u8;
                    if v_isSharedCheck_1526_ == 0 {
                        v___x_1521_ = v___x_1516_;
                        v_isShared_1522_ = v_isSharedCheck_1526_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1519_);
                        leanh::lean_dec(v___x_1516_);
                        v___x_1521_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1525_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
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
    mut v_00_u03b1_1527_: *mut leanh::LeanObject,
    mut v_00_u03b2_1528_: *mut leanh::LeanObject,
    mut v_a_1529_: *mut leanh::LeanObject,
    mut v_a_1530_: *mut leanh::LeanObject,
    mut v_a_1531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1532_ =
        l_Lake_instMonadMainM___aux__11(v_00_u03b1_1527_, v_00_u03b2_1528_, v_a_1529_, v_a_1530_);
    return v_res_1532_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__13___redArg(
    mut v_a_1533_: *mut leanh::LeanObject,
    mut v_a_1534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1542_: u8 = 0;
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1546_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1536_ = leanh::lean_apply_1(v_a_1533_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1536_) == 0 {
                    v_a_1537_ = leanh::lean_ctor_get(v___x_1536_, 0);
                    leanh::lean_inc(v_a_1537_);
                    leanh::lean_dec_ref_known(v___x_1536_, 1);
                    v___x_1538_ =
                        leanh::lean_apply_2(v_a_1534_, v_a_1537_, leanh::lean_box(0));
                    return v___x_1538_;
                } else {
                    leanh::lean_dec_ref(v_a_1534_);
                    v_a_1539_ = leanh::lean_ctor_get(v___x_1536_, 0);
                    v_isSharedCheck_1546_ = (!leanh::lean_is_exclusive(v___x_1536_)) as u8;
                    if v_isSharedCheck_1546_ == 0 {
                        v___x_1541_ = v___x_1536_;
                        v_isShared_1542_ = v_isSharedCheck_1546_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1539_);
                        leanh::lean_dec(v___x_1536_);
                        v___x_1541_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1545_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
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
    mut v_a_1547_: *mut leanh::LeanObject,
    mut v_a_1548_: *mut leanh::LeanObject,
    mut v_a_1549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1550_ = l_Lake_instMonadMainM___aux__13___redArg(v_a_1547_, v_a_1548_);
    return v_res_1550_;
}
pub unsafe fn l_Lake_instMonadMainM___aux__13(
    mut v_00_u03b1_1551_: *mut leanh::LeanObject,
    mut v_00_u03b2_1552_: *mut leanh::LeanObject,
    mut v_a_1553_: *mut leanh::LeanObject,
    mut v_a_1554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1562_: u8 = 0;
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1566_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1556_ = leanh::lean_apply_1(v_a_1553_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1556_) == 0 {
                    v_a_1557_ = leanh::lean_ctor_get(v___x_1556_, 0);
                    leanh::lean_inc(v_a_1557_);
                    leanh::lean_dec_ref_known(v___x_1556_, 1);
                    v___x_1558_ =
                        leanh::lean_apply_2(v_a_1554_, v_a_1557_, leanh::lean_box(0));
                    return v___x_1558_;
                } else {
                    leanh::lean_dec_ref(v_a_1554_);
                    v_a_1559_ = leanh::lean_ctor_get(v___x_1556_, 0);
                    v_isSharedCheck_1566_ = (!leanh::lean_is_exclusive(v___x_1556_)) as u8;
                    if v_isSharedCheck_1566_ == 0 {
                        v___x_1561_ = v___x_1556_;
                        v_isShared_1562_ = v_isSharedCheck_1566_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1559_);
                        leanh::lean_dec(v___x_1556_);
                        v___x_1561_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1565_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
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
    mut v_00_u03b1_1567_: *mut leanh::LeanObject,
    mut v_00_u03b2_1568_: *mut leanh::LeanObject,
    mut v_a_1569_: *mut leanh::LeanObject,
    mut v_a_1570_: *mut leanh::LeanObject,
    mut v_a_1571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1572_ =
        l_Lake_instMonadMainM___aux__13(v_00_u03b1_1567_, v_00_u03b2_1568_, v_a_1569_, v_a_1570_);
    return v_res_1572_;
}
pub unsafe fn l_Lake_instMonadFinallyMainM___aux__1___redArg(
    mut v_x_1593_: *mut leanh::LeanObject,
    mut v_f_1594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1600_: u8 = 0;
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1607_: u8 = 0;
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1612_: u8 = 0;
    let mut v_a_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1616_: u8 = 0;
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1620_: u8 = 0;
    let mut v_reuseFailAlloc_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1622_: u8 = 0;
    let mut v_a_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1628_: u8 = 0;
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1632_: u8 = 0;
    let mut v_unused_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1637_: u8 = 0;
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1641_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_r_1596_ = leanh::lean_apply_1(v_x_1593_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v_r_1596_) == 0 {
                    v_a_1597_ = leanh::lean_ctor_get(v_r_1596_, 0);
                    v_isSharedCheck_1622_ = (!leanh::lean_is_exclusive(v_r_1596_)) as u8;
                    if v_isSharedCheck_1622_ == 0 {
                        v___x_1599_ = v_r_1596_;
                        v_isShared_1600_ = v_isSharedCheck_1622_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1597_);
                        leanh::lean_dec(v_r_1596_);
                        v___x_1599_ = leanh::lean_box(0);
                        v_isShared_1600_ = v_isSharedCheck_1622_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1623_ = leanh::lean_ctor_get(v_r_1596_, 0);
                    leanh::lean_inc(v_a_1623_);
                    leanh::lean_dec_ref_known(v_r_1596_, 1);
                    v___x_1624_ = leanh::lean_box(0);
                    v___x_1625_ = leanh::lean_apply_2(
                        v_f_1594_,
                        v___x_1624_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_1625_) == 0 {
                        v_isSharedCheck_1632_ =
                            (!leanh::lean_is_exclusive(v___x_1625_)) as u8;
                        if v_isSharedCheck_1632_ == 0 {
                            v_unused_1633_ = leanh::lean_ctor_get(v___x_1625_, 0);
                            leanh::lean_dec(v_unused_1633_);
                            v___x_1627_ = v___x_1625_;
                            v_isShared_1628_ = v_isSharedCheck_1632_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1625_);
                            v___x_1627_ = leanh::lean_box(0);
                            v_isShared_1628_ = v_isSharedCheck_1632_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1623_);
                        v_a_1634_ = leanh::lean_ctor_get(v___x_1625_, 0);
                        v_isSharedCheck_1641_ =
                            (!leanh::lean_is_exclusive(v___x_1625_)) as u8;
                        if v_isSharedCheck_1641_ == 0 {
                            v___x_1636_ = v___x_1625_;
                            v_isShared_1637_ = v_isSharedCheck_1641_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1634_);
                            leanh::lean_dec(v___x_1625_);
                            v___x_1636_ = leanh::lean_box(0);
                            v_isShared_1637_ = v_isSharedCheck_1641_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_1597_);
                if v_isShared_1600_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1599_, 1);
                    v___x_1602_ = v___x_1599_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1621_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1597_);
                    v___x_1602_ = v_reuseFailAlloc_1621_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1603_ =
                    leanh::lean_apply_2(v_f_1594_, v___x_1602_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1603_) == 0 {
                    v_a_1604_ = leanh::lean_ctor_get(v___x_1603_, 0);
                    v_isSharedCheck_1612_ = (!leanh::lean_is_exclusive(v___x_1603_)) as u8;
                    if v_isSharedCheck_1612_ == 0 {
                        v___x_1606_ = v___x_1603_;
                        v_isShared_1607_ = v_isSharedCheck_1612_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1604_);
                        leanh::lean_dec(v___x_1603_);
                        v___x_1606_ = leanh::lean_box(0);
                        v_isShared_1607_ = v_isSharedCheck_1612_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1597_);
                    v_a_1613_ = leanh::lean_ctor_get(v___x_1603_, 0);
                    v_isSharedCheck_1620_ = (!leanh::lean_is_exclusive(v___x_1603_)) as u8;
                    if v_isSharedCheck_1620_ == 0 {
                        v___x_1615_ = v___x_1603_;
                        v_isShared_1616_ = v_isSharedCheck_1620_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1613_);
                        leanh::lean_dec(v___x_1603_);
                        v___x_1615_ = leanh::lean_box(0);
                        v_isShared_1616_ = v_isSharedCheck_1620_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1608_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1608_, 0, v_a_1597_);
                leanh::lean_ctor_set(v___x_1608_, 1, v_a_1604_);
                if v_isShared_1607_ == 0 {
                    leanh::lean_ctor_set(v___x_1606_, 0, v___x_1608_);
                    v___x_1610_ = v___x_1606_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1611_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1608_);
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
                    v_reuseFailAlloc_1619_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
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
                    leanh::lean_ctor_set_tag(v___x_1627_, 1);
                    leanh::lean_ctor_set(v___x_1627_, 0, v_a_1623_);
                    v___x_1630_ = v___x_1627_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1631_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1623_);
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
                    v_reuseFailAlloc_1640_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
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
    mut v_x_1642_: *mut leanh::LeanObject,
    mut v_f_1643_: *mut leanh::LeanObject,
    mut v_a_1644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1645_ = l_Lake_instMonadFinallyMainM___aux__1___redArg(v_x_1642_, v_f_1643_);
    return v_res_1645_;
}
pub unsafe fn l_Lake_instMonadFinallyMainM___aux__1(
    mut v_00_u03b1_1646_: *mut leanh::LeanObject,
    mut v_00_u03b2_1647_: *mut leanh::LeanObject,
    mut v_x_1648_: *mut leanh::LeanObject,
    mut v_f_1649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1655_: u8 = 0;
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1662_: u8 = 0;
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1667_: u8 = 0;
    let mut v_a_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1671_: u8 = 0;
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1675_: u8 = 0;
    let mut v_reuseFailAlloc_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1677_: u8 = 0;
    let mut v_a_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1683_: u8 = 0;
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1687_: u8 = 0;
    let mut v_unused_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1692_: u8 = 0;
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1696_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_r_1651_ = leanh::lean_apply_1(v_x_1648_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v_r_1651_) == 0 {
                    v_a_1652_ = leanh::lean_ctor_get(v_r_1651_, 0);
                    v_isSharedCheck_1677_ = (!leanh::lean_is_exclusive(v_r_1651_)) as u8;
                    if v_isSharedCheck_1677_ == 0 {
                        v___x_1654_ = v_r_1651_;
                        v_isShared_1655_ = v_isSharedCheck_1677_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1652_);
                        leanh::lean_dec(v_r_1651_);
                        v___x_1654_ = leanh::lean_box(0);
                        v_isShared_1655_ = v_isSharedCheck_1677_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1678_ = leanh::lean_ctor_get(v_r_1651_, 0);
                    leanh::lean_inc(v_a_1678_);
                    leanh::lean_dec_ref_known(v_r_1651_, 1);
                    v___x_1679_ = leanh::lean_box(0);
                    v___x_1680_ = leanh::lean_apply_2(
                        v_f_1649_,
                        v___x_1679_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_1680_) == 0 {
                        v_isSharedCheck_1687_ =
                            (!leanh::lean_is_exclusive(v___x_1680_)) as u8;
                        if v_isSharedCheck_1687_ == 0 {
                            v_unused_1688_ = leanh::lean_ctor_get(v___x_1680_, 0);
                            leanh::lean_dec(v_unused_1688_);
                            v___x_1682_ = v___x_1680_;
                            v_isShared_1683_ = v_isSharedCheck_1687_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1680_);
                            v___x_1682_ = leanh::lean_box(0);
                            v_isShared_1683_ = v_isSharedCheck_1687_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1678_);
                        v_a_1689_ = leanh::lean_ctor_get(v___x_1680_, 0);
                        v_isSharedCheck_1696_ =
                            (!leanh::lean_is_exclusive(v___x_1680_)) as u8;
                        if v_isSharedCheck_1696_ == 0 {
                            v___x_1691_ = v___x_1680_;
                            v_isShared_1692_ = v_isSharedCheck_1696_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1689_);
                            leanh::lean_dec(v___x_1680_);
                            v___x_1691_ = leanh::lean_box(0);
                            v_isShared_1692_ = v_isSharedCheck_1696_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_1652_);
                if v_isShared_1655_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1654_, 1);
                    v___x_1657_ = v___x_1654_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1676_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1652_);
                    v___x_1657_ = v_reuseFailAlloc_1676_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1658_ =
                    leanh::lean_apply_2(v_f_1649_, v___x_1657_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1658_) == 0 {
                    v_a_1659_ = leanh::lean_ctor_get(v___x_1658_, 0);
                    v_isSharedCheck_1667_ = (!leanh::lean_is_exclusive(v___x_1658_)) as u8;
                    if v_isSharedCheck_1667_ == 0 {
                        v___x_1661_ = v___x_1658_;
                        v_isShared_1662_ = v_isSharedCheck_1667_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1659_);
                        leanh::lean_dec(v___x_1658_);
                        v___x_1661_ = leanh::lean_box(0);
                        v_isShared_1662_ = v_isSharedCheck_1667_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1652_);
                    v_a_1668_ = leanh::lean_ctor_get(v___x_1658_, 0);
                    v_isSharedCheck_1675_ = (!leanh::lean_is_exclusive(v___x_1658_)) as u8;
                    if v_isSharedCheck_1675_ == 0 {
                        v___x_1670_ = v___x_1658_;
                        v_isShared_1671_ = v_isSharedCheck_1675_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1668_);
                        leanh::lean_dec(v___x_1658_);
                        v___x_1670_ = leanh::lean_box(0);
                        v_isShared_1671_ = v_isSharedCheck_1675_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1663_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1663_, 0, v_a_1652_);
                leanh::lean_ctor_set(v___x_1663_, 1, v_a_1659_);
                if v_isShared_1662_ == 0 {
                    leanh::lean_ctor_set(v___x_1661_, 0, v___x_1663_);
                    v___x_1665_ = v___x_1661_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1666_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
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
                    v_reuseFailAlloc_1674_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
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
                    leanh::lean_ctor_set_tag(v___x_1682_, 1);
                    leanh::lean_ctor_set(v___x_1682_, 0, v_a_1678_);
                    v___x_1685_ = v___x_1682_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1686_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1678_);
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
                    v_reuseFailAlloc_1695_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
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
    mut v_00_u03b1_1697_: *mut leanh::LeanObject,
    mut v_00_u03b2_1698_: *mut leanh::LeanObject,
    mut v_x_1699_: *mut leanh::LeanObject,
    mut v_f_1700_: *mut leanh::LeanObject,
    mut v_a_1701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1702_ = l_Lake_instMonadFinallyMainM___aux__1(
        v_00_u03b1_1697_,
        v_00_u03b2_1698_,
        v_x_1699_,
        v_f_1700_,
    );
    return v_res_1702_;
}
pub unsafe fn l_Lake_instMonadLiftBaseIOMainM___aux__1___redArg(
    mut v_act_1705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1707_ = leanh::lean_apply_1(v_act_1705_, leanh::lean_box(0));
    v___x_1708_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1708_, 0, v___x_1707_);
    return v___x_1708_;
}
pub unsafe fn l_Lake_instMonadLiftBaseIOMainM___aux__1___redArg___boxed(
    mut v_act_1709_: *mut leanh::LeanObject,
    mut v_a_1710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1711_ = l_Lake_instMonadLiftBaseIOMainM___aux__1___redArg(v_act_1709_);
    return v_res_1711_;
}
pub unsafe fn l_Lake_instMonadLiftBaseIOMainM___aux__1(
    mut v_00_u03b1_1712_: *mut leanh::LeanObject,
    mut v_act_1713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1715_ = leanh::lean_apply_1(v_act_1713_, leanh::lean_box(0));
    v___x_1716_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1716_, 0, v___x_1715_);
    return v___x_1716_;
}
pub unsafe fn l_Lake_instMonadLiftBaseIOMainM___aux__1___boxed(
    mut v_00_u03b1_1717_: *mut leanh::LeanObject,
    mut v_act_1718_: *mut leanh::LeanObject,
    mut v_a_1719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1720_ = l_Lake_instMonadLiftBaseIOMainM___aux__1(v_00_u03b1_1717_, v_act_1718_);
    return v_res_1720_;
}
pub unsafe fn l_Lake_MainM_mk___redArg(
    mut v_x_1723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1725_ = leanh::lean_apply_1(v_x_1723_, leanh::lean_box(0));
    return v___x_1725_;
}
pub unsafe fn l_Lake_MainM_mk___redArg___boxed(
    mut v_x_1726_: *mut leanh::LeanObject,
    mut v_a_1727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1728_ = l_Lake_MainM_mk___redArg(v_x_1726_);
    return v_res_1728_;
}
pub unsafe fn l_Lake_MainM_mk(
    mut v_00_u03b1_1729_: *mut leanh::LeanObject,
    mut v_x_1730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1732_ = leanh::lean_apply_1(v_x_1730_, leanh::lean_box(0));
    return v___x_1732_;
}
pub unsafe fn l_Lake_MainM_mk___boxed(
    mut v_00_u03b1_1733_: *mut leanh::LeanObject,
    mut v_x_1734_: *mut leanh::LeanObject,
    mut v_a_1735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1736_ = l_Lake_MainM_mk(v_00_u03b1_1733_, v_x_1734_);
    return v_res_1736_;
}
pub unsafe fn l_Lake_MainM_toEIO___redArg(
    mut v_self_1737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1739_ = leanh::lean_apply_1(v_self_1737_, leanh::lean_box(0));
    return v___x_1739_;
}
pub unsafe fn l_Lake_MainM_toEIO___redArg___boxed(
    mut v_self_1740_: *mut leanh::LeanObject,
    mut v_a_1741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1742_ = l_Lake_MainM_toEIO___redArg(v_self_1740_);
    return v_res_1742_;
}
pub unsafe fn l_Lake_MainM_toEIO(
    mut v_00_u03b1_1743_: *mut leanh::LeanObject,
    mut v_self_1744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1746_ = leanh::lean_apply_1(v_self_1744_, leanh::lean_box(0));
    return v___x_1746_;
}
pub unsafe fn l_Lake_MainM_toEIO___boxed(
    mut v_00_u03b1_1747_: *mut leanh::LeanObject,
    mut v_self_1748_: *mut leanh::LeanObject,
    mut v_a_1749_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1750_ = l_Lake_MainM_toEIO(v_00_u03b1_1747_, v_self_1748_);
    return v_res_1750_;
}
pub unsafe fn l_Lake_MainM_toBaseIO___redArg(
    mut v_self_1751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1757_: u8 = 0;
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1761_: u8 = 0;
    let mut v_a_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1765_: u8 = 0;
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1769_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1753_ = leanh::lean_apply_1(v_self_1751_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1753_) == 0 {
                    v_a_1754_ = leanh::lean_ctor_get(v___x_1753_, 0);
                    v_isSharedCheck_1761_ = (!leanh::lean_is_exclusive(v___x_1753_)) as u8;
                    if v_isSharedCheck_1761_ == 0 {
                        v___x_1756_ = v___x_1753_;
                        v_isShared_1757_ = v_isSharedCheck_1761_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1754_);
                        leanh::lean_dec(v___x_1753_);
                        v___x_1756_ = leanh::lean_box(0);
                        v_isShared_1757_ = v_isSharedCheck_1761_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1762_ = leanh::lean_ctor_get(v___x_1753_, 0);
                    v_isSharedCheck_1769_ = (!leanh::lean_is_exclusive(v___x_1753_)) as u8;
                    if v_isSharedCheck_1769_ == 0 {
                        v___x_1764_ = v___x_1753_;
                        v_isShared_1765_ = v_isSharedCheck_1769_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1762_);
                        leanh::lean_dec(v___x_1753_);
                        v___x_1764_ = leanh::lean_box(0);
                        v_isShared_1765_ = v_isSharedCheck_1769_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1757_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1756_, 1);
                    v___x_1759_ = v___x_1756_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1760_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
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
                    leanh::lean_ctor_set_tag(v___x_1764_, 0);
                    v___x_1767_ = v___x_1764_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1768_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
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
    mut v_self_1770_: *mut leanh::LeanObject,
    mut v_a_1771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1772_ = l_Lake_MainM_toBaseIO___redArg(v_self_1770_);
    return v_res_1772_;
}
pub unsafe fn l_Lake_MainM_toBaseIO(
    mut v_00_u03b1_1773_: *mut leanh::LeanObject,
    mut v_self_1774_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1780_: u8 = 0;
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1784_: u8 = 0;
    let mut v_a_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1788_: u8 = 0;
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1792_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1776_ = leanh::lean_apply_1(v_self_1774_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1776_) == 0 {
                    v_a_1777_ = leanh::lean_ctor_get(v___x_1776_, 0);
                    v_isSharedCheck_1784_ = (!leanh::lean_is_exclusive(v___x_1776_)) as u8;
                    if v_isSharedCheck_1784_ == 0 {
                        v___x_1779_ = v___x_1776_;
                        v_isShared_1780_ = v_isSharedCheck_1784_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1777_);
                        leanh::lean_dec(v___x_1776_);
                        v___x_1779_ = leanh::lean_box(0);
                        v_isShared_1780_ = v_isSharedCheck_1784_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1785_ = leanh::lean_ctor_get(v___x_1776_, 0);
                    v_isSharedCheck_1792_ = (!leanh::lean_is_exclusive(v___x_1776_)) as u8;
                    if v_isSharedCheck_1792_ == 0 {
                        v___x_1787_ = v___x_1776_;
                        v_isShared_1788_ = v_isSharedCheck_1792_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1785_);
                        leanh::lean_dec(v___x_1776_);
                        v___x_1787_ = leanh::lean_box(0);
                        v_isShared_1788_ = v_isSharedCheck_1792_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1780_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1779_, 1);
                    v___x_1782_ = v___x_1779_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1783_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
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
                    leanh::lean_ctor_set_tag(v___x_1787_, 0);
                    v___x_1790_ = v___x_1787_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1791_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
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
    mut v_00_u03b1_1793_: *mut leanh::LeanObject,
    mut v_self_1794_: *mut leanh::LeanObject,
    mut v_a_1795_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1796_ = l_Lake_MainM_toBaseIO(v_00_u03b1_1793_, v_self_1794_);
    return v_res_1796_;
}
pub unsafe fn l_Lake_MainM_run___redArg(mut v_self_1797_: *mut leanh::LeanObject) -> u32 {
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1799_ = leanh::lean_apply_1(v_self_1797_, leanh::lean_box(0));
    if leanh::lean_obj_tag(v___x_1799_) == 0 {
        let mut v___x_1800_: u32 = 0;
        leanh::lean_dec_ref_known(v___x_1799_, 1);
        v___x_1800_ = 0;
        return v___x_1800_;
    } else {
        let mut v_a_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1802_: u32 = 0;
        v_a_1801_ = leanh::lean_ctor_get(v___x_1799_, 0);
        leanh::lean_inc(v_a_1801_);
        leanh::lean_dec_ref_known(v___x_1799_, 1);
        v___x_1802_ = leanh::lean_unbox_uint32(v_a_1801_);
        leanh::lean_dec(v_a_1801_);
        return v___x_1802_;
    }
}
pub unsafe fn l_Lake_MainM_run___redArg___boxed(
    mut v_self_1803_: *mut leanh::LeanObject,
    mut v_a_1804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1805_: u32 = 0;
    let mut v_r_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1805_ = l_Lake_MainM_run___redArg(v_self_1803_);
    v_r_1806_ = leanh::lean_box_uint32(v_res_1805_);
    return v_r_1806_;
}
pub unsafe fn l_Lake_MainM_run(
    mut v_00_u03b1_1807_: *mut leanh::LeanObject,
    mut v_self_1808_: *mut leanh::LeanObject,
) -> u32 {
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1810_ = leanh::lean_apply_1(v_self_1808_, leanh::lean_box(0));
    if leanh::lean_obj_tag(v___x_1810_) == 0 {
        let mut v___x_1811_: u32 = 0;
        leanh::lean_dec_ref_known(v___x_1810_, 1);
        v___x_1811_ = 0;
        return v___x_1811_;
    } else {
        let mut v_a_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1813_: u32 = 0;
        v_a_1812_ = leanh::lean_ctor_get(v___x_1810_, 0);
        leanh::lean_inc(v_a_1812_);
        leanh::lean_dec_ref_known(v___x_1810_, 1);
        v___x_1813_ = leanh::lean_unbox_uint32(v_a_1812_);
        leanh::lean_dec(v_a_1812_);
        return v___x_1813_;
    }
}
pub unsafe fn l_Lake_MainM_run___boxed(
    mut v_00_u03b1_1814_: *mut leanh::LeanObject,
    mut v_self_1815_: *mut leanh::LeanObject,
    mut v_a_1816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1817_: u32 = 0;
    let mut v_r_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1817_ = l_Lake_MainM_run(v_00_u03b1_1814_, v_self_1815_);
    v_r_1818_ = leanh::lean_box_uint32(v_res_1817_);
    return v_r_1818_;
}
pub unsafe fn l_Lake_MainM_exit___redArg(mut v_rc_1819_: u32) -> *mut leanh::LeanObject {
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1821_ = leanh::lean_box_uint32(v_rc_1819_);
    v___x_1822_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1822_, 0, v___x_1821_);
    return v___x_1822_;
}
pub unsafe fn l_Lake_MainM_exit___redArg___boxed(
    mut v_rc_1823_: *mut leanh::LeanObject,
    mut v_a_1824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_rc_boxed_1825_: u32 = 0;
    let mut v_res_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_rc_boxed_1825_ = leanh::lean_unbox_uint32(v_rc_1823_);
    leanh::lean_dec(v_rc_1823_);
    v_res_1826_ = l_Lake_MainM_exit___redArg(v_rc_boxed_1825_);
    return v_res_1826_;
}
pub unsafe fn l_Lake_MainM_exit(
    mut v_00_u03b1_1827_: *mut leanh::LeanObject,
    mut v_rc_1828_: u32,
) -> *mut leanh::LeanObject {
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1830_ = leanh::lean_box_uint32(v_rc_1828_);
    v___x_1831_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1831_, 0, v___x_1830_);
    return v___x_1831_;
}
pub unsafe fn l_Lake_MainM_exit___boxed(
    mut v_00_u03b1_1832_: *mut leanh::LeanObject,
    mut v_rc_1833_: *mut leanh::LeanObject,
    mut v_a_1834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_rc_boxed_1835_: u32 = 0;
    let mut v_res_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_rc_boxed_1835_ = leanh::lean_unbox_uint32(v_rc_1833_);
    leanh::lean_dec(v_rc_1833_);
    v_res_1836_ = l_Lake_MainM_exit(v_00_u03b1_1832_, v_rc_boxed_1835_);
    return v_res_1836_;
}
pub unsafe fn l_Lake_MainM_tryCatchExit___redArg(
    mut v_f_1839_: *mut leanh::LeanObject,
    mut v_self_1840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1842_ = leanh::lean_apply_1(v_self_1840_, leanh::lean_box(0));
    if leanh::lean_obj_tag(v___x_1842_) == 0 {
        leanh::lean_dec_ref(v_f_1839_);
        return v___x_1842_;
    } else {
        let mut v_a_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1843_ = leanh::lean_ctor_get(v___x_1842_, 0);
        leanh::lean_inc(v_a_1843_);
        leanh::lean_dec_ref_known(v___x_1842_, 1);
        v___x_1844_ = leanh::lean_apply_2(v_f_1839_, v_a_1843_, leanh::lean_box(0));
        return v___x_1844_;
    }
}
pub unsafe fn l_Lake_MainM_tryCatchExit___redArg___boxed(
    mut v_f_1845_: *mut leanh::LeanObject,
    mut v_self_1846_: *mut leanh::LeanObject,
    mut v_a_1847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1848_ = l_Lake_MainM_tryCatchExit___redArg(v_f_1845_, v_self_1846_);
    return v_res_1848_;
}
pub unsafe fn l_Lake_MainM_tryCatchExit(
    mut v_00_u03b1_1849_: *mut leanh::LeanObject,
    mut v_f_1850_: *mut leanh::LeanObject,
    mut v_self_1851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1853_ = leanh::lean_apply_1(v_self_1851_, leanh::lean_box(0));
    if leanh::lean_obj_tag(v___x_1853_) == 0 {
        leanh::lean_dec_ref(v_f_1850_);
        return v___x_1853_;
    } else {
        let mut v_a_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1854_ = leanh::lean_ctor_get(v___x_1853_, 0);
        leanh::lean_inc(v_a_1854_);
        leanh::lean_dec_ref_known(v___x_1853_, 1);
        v___x_1855_ = leanh::lean_apply_2(v_f_1850_, v_a_1854_, leanh::lean_box(0));
        return v___x_1855_;
    }
}
pub unsafe fn l_Lake_MainM_tryCatchExit___boxed(
    mut v_00_u03b1_1856_: *mut leanh::LeanObject,
    mut v_f_1857_: *mut leanh::LeanObject,
    mut v_self_1858_: *mut leanh::LeanObject,
    mut v_a_1859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1860_ = l_Lake_MainM_tryCatchExit(v_00_u03b1_1856_, v_f_1857_, v_self_1858_);
    return v_res_1860_;
}
pub unsafe fn _init_l_Lake_MainM_tryCatchError___redArg___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_1861_: u32 = 0;
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1861_ = 0;
    v___x_1862_ = leanh::lean_box_uint32(v___x_1861_);
    return v___x_1862_;
}
pub unsafe fn l_Lake_MainM_tryCatchError___redArg(
    mut v_f_1863_: *mut leanh::LeanObject,
    mut v_self_1864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1870_: u8 = 0;
    let mut v___x_1871_: u32 = 0;
    let mut v___x_1872_: u32 = 0;
    let mut v___x_1873_: u8 = 0;
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1879_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1866_ = leanh::lean_apply_1(v_self_1864_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1866_) == 0 {
                    leanh::lean_dec_ref(v_f_1863_);
                    return v___x_1866_;
                } else {
                    v_a_1867_ = leanh::lean_ctor_get(v___x_1866_, 0);
                    v_isSharedCheck_1879_ = (!leanh::lean_is_exclusive(v___x_1866_)) as u8;
                    if v_isSharedCheck_1879_ == 0 {
                        v___x_1869_ = v___x_1866_;
                        v_isShared_1870_ = v_isSharedCheck_1879_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1867_);
                        leanh::lean_dec(v___x_1866_);
                        v___x_1869_ = leanh::lean_box(0);
                        v_isShared_1870_ = v_isSharedCheck_1879_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1871_ = 0;
                v___x_1872_ = leanh::lean_unbox_uint32(v_a_1867_);
                v___x_1873_ = lean_uint32_dec_eq(v___x_1872_, v___x_1871_);
                if v___x_1873_ == 0 {
                    leanh::lean_del_object(v___x_1869_);
                    v___x_1874_ =
                        leanh::lean_apply_2(v_f_1863_, v_a_1867_, leanh::lean_box(0));
                    return v___x_1874_;
                } else {
                    leanh::lean_dec(v_a_1867_);
                    leanh::lean_dec_ref(v_f_1863_);
                    v___x_1875_ = l_Lake_MainM_tryCatchError___redArg___boxed__const__1;
                    if v_isShared_1870_ == 0 {
                        leanh::lean_ctor_set(v___x_1869_, 0, v___x_1875_);
                        v___x_1877_ = v___x_1869_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1878_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1875_);
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
    mut v_f_1880_: *mut leanh::LeanObject,
    mut v_self_1881_: *mut leanh::LeanObject,
    mut v_a_1882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1883_ = l_Lake_MainM_tryCatchError___redArg(v_f_1880_, v_self_1881_);
    return v_res_1883_;
}
pub unsafe fn l_Lake_MainM_tryCatchError(
    mut v_00_u03b1_1884_: *mut leanh::LeanObject,
    mut v_f_1885_: *mut leanh::LeanObject,
    mut v_self_1886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1892_: u8 = 0;
    let mut v___x_1893_: u32 = 0;
    let mut v___x_1894_: u32 = 0;
    let mut v___x_1895_: u8 = 0;
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1901_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1888_ = leanh::lean_apply_1(v_self_1886_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1888_) == 0 {
                    leanh::lean_dec_ref(v_f_1885_);
                    return v___x_1888_;
                } else {
                    v_a_1889_ = leanh::lean_ctor_get(v___x_1888_, 0);
                    v_isSharedCheck_1901_ = (!leanh::lean_is_exclusive(v___x_1888_)) as u8;
                    if v_isSharedCheck_1901_ == 0 {
                        v___x_1891_ = v___x_1888_;
                        v_isShared_1892_ = v_isSharedCheck_1901_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1889_);
                        leanh::lean_dec(v___x_1888_);
                        v___x_1891_ = leanh::lean_box(0);
                        v_isShared_1892_ = v_isSharedCheck_1901_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1893_ = 0;
                v___x_1894_ = leanh::lean_unbox_uint32(v_a_1889_);
                v___x_1895_ = lean_uint32_dec_eq(v___x_1894_, v___x_1893_);
                if v___x_1895_ == 0 {
                    leanh::lean_del_object(v___x_1891_);
                    v___x_1896_ =
                        leanh::lean_apply_2(v_f_1885_, v_a_1889_, leanh::lean_box(0));
                    return v___x_1896_;
                } else {
                    leanh::lean_dec(v_a_1889_);
                    leanh::lean_dec_ref(v_f_1885_);
                    v___x_1897_ = l_Lake_MainM_tryCatchError___redArg___boxed__const__1;
                    if v_isShared_1892_ == 0 {
                        leanh::lean_ctor_set(v___x_1891_, 0, v___x_1897_);
                        v___x_1899_ = v___x_1891_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1900_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1897_);
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
    mut v_00_u03b1_1902_: *mut leanh::LeanObject,
    mut v_f_1903_: *mut leanh::LeanObject,
    mut v_self_1904_: *mut leanh::LeanObject,
    mut v_a_1905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1906_ = l_Lake_MainM_tryCatchError(v_00_u03b1_1902_, v_f_1903_, v_self_1904_);
    return v_res_1906_;
}
pub unsafe fn _init_l_Lake_MainM_failure___redArg___boxed__const__1()
-> *mut leanh::LeanObject {
    let mut v___x_1907_: u32 = 0;
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1907_ = 1;
    v___x_1908_ = leanh::lean_box_uint32(v___x_1907_);
    return v___x_1908_;
}
pub unsafe fn l_Lake_MainM_failure___redArg() -> *mut leanh::LeanObject {
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1910_ = l_Lake_MainM_failure___redArg___boxed__const__1;
    v___x_1911_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1911_, 0, v___x_1910_);
    return v___x_1911_;
}
pub unsafe fn l_Lake_MainM_failure___redArg___boxed(
    mut v_a_1912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1913_ = l_Lake_MainM_failure___redArg();
    return v_res_1913_;
}
pub unsafe fn l_Lake_MainM_failure(
    mut v_00_u03b1_1914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1916_ = l_Lake_MainM_failure___redArg___boxed__const__1;
    v___x_1917_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1917_, 0, v___x_1916_);
    return v___x_1917_;
}
pub unsafe fn l_Lake_MainM_failure___boxed(
    mut v_00_u03b1_1918_: *mut leanh::LeanObject,
    mut v_a_1919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1920_ = l_Lake_MainM_failure(v_00_u03b1_1918_);
    return v_res_1920_;
}
pub unsafe fn l_Lake_MainM_orElse___redArg(
    mut v_self_1921_: *mut leanh::LeanObject,
    mut v_other_1922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1928_: u8 = 0;
    let mut v___x_1929_: u32 = 0;
    let mut v___x_1930_: u32 = 0;
    let mut v___x_1931_: u8 = 0;
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1938_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1924_ = leanh::lean_apply_1(v_self_1921_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1924_) == 0 {
                    leanh::lean_dec_ref(v_other_1922_);
                    return v___x_1924_;
                } else {
                    v_a_1925_ = leanh::lean_ctor_get(v___x_1924_, 0);
                    v_isSharedCheck_1938_ = (!leanh::lean_is_exclusive(v___x_1924_)) as u8;
                    if v_isSharedCheck_1938_ == 0 {
                        v___x_1927_ = v___x_1924_;
                        v_isShared_1928_ = v_isSharedCheck_1938_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1925_);
                        leanh::lean_dec(v___x_1924_);
                        v___x_1927_ = leanh::lean_box(0);
                        v_isShared_1928_ = v_isSharedCheck_1938_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1929_ = 0;
                v___x_1930_ = leanh::lean_unbox_uint32(v_a_1925_);
                leanh::lean_dec(v_a_1925_);
                v___x_1931_ = lean_uint32_dec_eq(v___x_1930_, v___x_1929_);
                if v___x_1931_ == 0 {
                    leanh::lean_del_object(v___x_1927_);
                    v___x_1932_ = leanh::lean_box(0);
                    v___x_1933_ = leanh::lean_apply_2(
                        v_other_1922_,
                        v___x_1932_,
                        leanh::lean_box(0),
                    );
                    return v___x_1933_;
                } else {
                    leanh::lean_dec_ref(v_other_1922_);
                    v___x_1934_ = l_Lake_MainM_tryCatchError___redArg___boxed__const__1;
                    if v_isShared_1928_ == 0 {
                        leanh::lean_ctor_set(v___x_1927_, 0, v___x_1934_);
                        v___x_1936_ = v___x_1927_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1937_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1934_);
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
    mut v_self_1939_: *mut leanh::LeanObject,
    mut v_other_1940_: *mut leanh::LeanObject,
    mut v_a_1941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1942_ = l_Lake_MainM_orElse___redArg(v_self_1939_, v_other_1940_);
    return v_res_1942_;
}
pub unsafe fn l_Lake_MainM_orElse(
    mut v_00_u03b1_1943_: *mut leanh::LeanObject,
    mut v_self_1944_: *mut leanh::LeanObject,
    mut v_other_1945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1951_: u8 = 0;
    let mut v___x_1952_: u32 = 0;
    let mut v___x_1953_: u32 = 0;
    let mut v___x_1954_: u8 = 0;
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1961_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1947_ = leanh::lean_apply_1(v_self_1944_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_1947_) == 0 {
                    leanh::lean_dec_ref(v_other_1945_);
                    return v___x_1947_;
                } else {
                    v_a_1948_ = leanh::lean_ctor_get(v___x_1947_, 0);
                    v_isSharedCheck_1961_ = (!leanh::lean_is_exclusive(v___x_1947_)) as u8;
                    if v_isSharedCheck_1961_ == 0 {
                        v___x_1950_ = v___x_1947_;
                        v_isShared_1951_ = v_isSharedCheck_1961_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1948_);
                        leanh::lean_dec(v___x_1947_);
                        v___x_1950_ = leanh::lean_box(0);
                        v_isShared_1951_ = v_isSharedCheck_1961_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1952_ = 0;
                v___x_1953_ = leanh::lean_unbox_uint32(v_a_1948_);
                leanh::lean_dec(v_a_1948_);
                v___x_1954_ = lean_uint32_dec_eq(v___x_1953_, v___x_1952_);
                if v___x_1954_ == 0 {
                    leanh::lean_del_object(v___x_1950_);
                    v___x_1955_ = leanh::lean_box(0);
                    v___x_1956_ = leanh::lean_apply_2(
                        v_other_1945_,
                        v___x_1955_,
                        leanh::lean_box(0),
                    );
                    return v___x_1956_;
                } else {
                    leanh::lean_dec_ref(v_other_1945_);
                    v___x_1957_ = l_Lake_MainM_tryCatchError___redArg___boxed__const__1;
                    if v_isShared_1951_ == 0 {
                        leanh::lean_ctor_set(v___x_1950_, 0, v___x_1957_);
                        v___x_1959_ = v___x_1950_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1960_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1957_);
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
    mut v_00_u03b1_1962_: *mut leanh::LeanObject,
    mut v_self_1963_: *mut leanh::LeanObject,
    mut v_other_1964_: *mut leanh::LeanObject,
    mut v_a_1965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1966_ = l_Lake_MainM_orElse(v_00_u03b1_1962_, v_self_1963_, v_other_1964_);
    return v_res_1966_;
}
pub unsafe fn _init_l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative()
-> *mut leanh::LeanObject {
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1969_ = l_Lake_instMonadMainM;
    v_toApplicative_1970_ = leanh::lean_ctor_get(v___x_1969_, 0);
    v___x_1971_ = l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__0;
    v___x_1972_ = l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__1;
    leanh::lean_inc_ref(v_toApplicative_1970_);
    v___x_1973_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1973_, 0, v_toApplicative_1970_);
    leanh::lean_ctor_set(v___x_1973_, 1, v___x_1971_);
    leanh::lean_ctor_set(v___x_1973_, 2, v___x_1972_);
    return v___x_1973_;
}
pub unsafe fn l_Lake_MainM_instMonadLog___lam__0(
    mut v___x_1974_: *mut leanh::LeanObject,
    mut v___x_1975_: u8,
    mut v___x_1976_: u8,
    mut v_e_1977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1979_ = l_Lake_OutStream_logEntry(v___x_1974_, v_e_1977_, v___x_1975_, v___x_1976_);
    v___x_1980_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1980_, 0, v___x_1979_);
    return v___x_1980_;
}
pub unsafe fn l_Lake_MainM_instMonadLog___lam__0___boxed(
    mut v___x_1981_: *mut leanh::LeanObject,
    mut v___x_1982_: *mut leanh::LeanObject,
    mut v___x_1983_: *mut leanh::LeanObject,
    mut v_e_1984_: *mut leanh::LeanObject,
    mut v___y_1985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_37__boxed_1986_: u8 = 0;
    let mut v___x_38__boxed_1987_: u8 = 0;
    let mut v_res_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_37__boxed_1986_ = (leanh::lean_unbox(v___x_1982_) as u8);
    v___x_38__boxed_1987_ = (leanh::lean_unbox(v___x_1983_) as u8);
    v_res_1988_ = l_Lake_MainM_instMonadLog___lam__0(
        v___x_1981_,
        v___x_37__boxed_1986_,
        v___x_38__boxed_1987_,
        v_e_1984_,
    );
    leanh::lean_dec_ref(v_e_1984_);
    leanh::lean_dec(v___x_1981_);
    return v_res_1988_;
}
pub unsafe fn l_Lake_MainM_error___redArg(
    mut v_msg_1996_: *mut leanh::LeanObject,
    mut v_rc_1997_: u32,
) -> *mut leanh::LeanObject {
    let mut v___x_1999_: u8 = 0;
    let mut v___x_2000_: u8 = 0;
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: u8 = 0;
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1999_ = 1;
    v___x_2000_ = 0;
    v___x_2001_ = leanh::lean_box(1);
    v___x_2002_ = 3;
    v___x_2003_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2003_, 0, v_msg_1996_);
    leanh::lean_ctor_set_uint8(
        v___x_2003_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2002_,
    );
    v___x_2004_ = l_Lake_OutStream_logEntry(v___x_2001_, v___x_2003_, v___x_1999_, v___x_2000_);
    leanh::lean_dec_ref_known(v___x_2003_, 1);
    v___x_2005_ = leanh::lean_box_uint32(v_rc_1997_);
    v___x_2006_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2006_, 0, v___x_2005_);
    return v___x_2006_;
}
pub unsafe fn l_Lake_MainM_error___redArg___boxed(
    mut v_msg_2007_: *mut leanh::LeanObject,
    mut v_rc_2008_: *mut leanh::LeanObject,
    mut v_a_2009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_rc_boxed_2010_: u32 = 0;
    let mut v_res_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_rc_boxed_2010_ = leanh::lean_unbox_uint32(v_rc_2008_);
    leanh::lean_dec(v_rc_2008_);
    v_res_2011_ = l_Lake_MainM_error___redArg(v_msg_2007_, v_rc_boxed_2010_);
    return v_res_2011_;
}
pub unsafe fn l_Lake_MainM_error(
    mut v_00_u03b1_2012_: *mut leanh::LeanObject,
    mut v_msg_2013_: *mut leanh::LeanObject,
    mut v_rc_2014_: u32,
) -> *mut leanh::LeanObject {
    let mut v___x_2016_: u8 = 0;
    let mut v___x_2017_: u8 = 0;
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: u8 = 0;
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2016_ = 1;
    v___x_2017_ = 0;
    v___x_2018_ = leanh::lean_box(1);
    v___x_2019_ = 3;
    v___x_2020_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2020_, 0, v_msg_2013_);
    leanh::lean_ctor_set_uint8(
        v___x_2020_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2019_,
    );
    v___x_2021_ = l_Lake_OutStream_logEntry(v___x_2018_, v___x_2020_, v___x_2016_, v___x_2017_);
    leanh::lean_dec_ref_known(v___x_2020_, 1);
    v___x_2022_ = leanh::lean_box_uint32(v_rc_2014_);
    v___x_2023_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2023_, 0, v___x_2022_);
    return v___x_2023_;
}
pub unsafe fn l_Lake_MainM_error___boxed(
    mut v_00_u03b1_2024_: *mut leanh::LeanObject,
    mut v_msg_2025_: *mut leanh::LeanObject,
    mut v_rc_2026_: *mut leanh::LeanObject,
    mut v_a_2027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_rc_boxed_2028_: u32 = 0;
    let mut v_res_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_rc_boxed_2028_ = leanh::lean_unbox_uint32(v_rc_2026_);
    leanh::lean_dec(v_rc_2026_);
    v_res_2029_ = l_Lake_MainM_error(v_00_u03b1_2024_, v_msg_2025_, v_rc_boxed_2028_);
    return v_res_2029_;
}
pub unsafe fn l_Lake_MainM_instMonadError___lam__0(
    mut v_00_u03b1_2030_: *mut leanh::LeanObject,
    mut v_msg_2031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2033_: u8 = 0;
    let mut v___x_2034_: u8 = 0;
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: u8 = 0;
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2033_ = 1;
    v___x_2034_ = 0;
    v___x_2035_ = leanh::lean_box(1);
    v___x_2036_ = 3;
    v___x_2037_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2037_, 0, v_msg_2031_);
    leanh::lean_ctor_set_uint8(
        v___x_2037_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2036_,
    );
    v___x_2038_ = l_Lake_OutStream_logEntry(v___x_2035_, v___x_2037_, v___x_2033_, v___x_2034_);
    leanh::lean_dec_ref_known(v___x_2037_, 1);
    v___x_2039_ = l_Lake_MainM_failure___redArg___boxed__const__1;
    v___x_2040_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2040_, 0, v___x_2039_);
    return v___x_2040_;
}
pub unsafe fn l_Lake_MainM_instMonadError___lam__0___boxed(
    mut v_00_u03b1_2041_: *mut leanh::LeanObject,
    mut v_msg_2042_: *mut leanh::LeanObject,
    mut v___y_2043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2044_ = l_Lake_MainM_instMonadError___lam__0(v_00_u03b1_2041_, v_msg_2042_);
    return v_res_2044_;
}
pub unsafe fn l_Lake_MainM_instMonadLiftIO___lam__0(
    mut v_00_u03b1_2047_: *mut leanh::LeanObject,
    mut v___y_2048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2054_: u8 = 0;
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut v_a_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2062_: u8 = 0;
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: u8 = 0;
    let mut v___x_2065_: u8 = 0;
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: u8 = 0;
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2074_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2050_ = leanh::lean_apply_1(v___y_2048_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_2050_) == 0 {
                    v_a_2051_ = leanh::lean_ctor_get(v___x_2050_, 0);
                    v_isSharedCheck_2058_ = (!leanh::lean_is_exclusive(v___x_2050_)) as u8;
                    if v_isSharedCheck_2058_ == 0 {
                        v___x_2053_ = v___x_2050_;
                        v_isShared_2054_ = v_isSharedCheck_2058_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2051_);
                        leanh::lean_dec(v___x_2050_);
                        v___x_2053_ = leanh::lean_box(0);
                        v_isShared_2054_ = v_isSharedCheck_2058_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2059_ = leanh::lean_ctor_get(v___x_2050_, 0);
                    v_isSharedCheck_2074_ = (!leanh::lean_is_exclusive(v___x_2050_)) as u8;
                    if v_isSharedCheck_2074_ == 0 {
                        v___x_2061_ = v___x_2050_;
                        v_isShared_2062_ = v_isSharedCheck_2074_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2059_);
                        leanh::lean_dec(v___x_2050_);
                        v___x_2061_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2057_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
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
                v___x_2066_ = leanh::lean_box(1);
                v___x_2067_ = 3;
                v___x_2068_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2068_, 0, v___x_2063_);
                leanh::lean_ctor_set_uint8(
                    v___x_2068_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2067_,
                );
                v___x_2069_ =
                    l_Lake_OutStream_logEntry(v___x_2066_, v___x_2068_, v___x_2064_, v___x_2065_);
                leanh::lean_dec_ref_known(v___x_2068_, 1);
                v___x_2070_ = l_Lake_MainM_failure___redArg___boxed__const__1;
                if v_isShared_2062_ == 0 {
                    leanh::lean_ctor_set(v___x_2061_, 0, v___x_2070_);
                    v___x_2072_ = v___x_2061_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2073_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2070_);
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
    mut v_00_u03b1_2075_: *mut leanh::LeanObject,
    mut v___y_2076_: *mut leanh::LeanObject,
    mut v___y_2077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2078_ = l_Lake_MainM_instMonadLiftIO___lam__0(v_00_u03b1_2075_, v___y_2076_);
    return v_res_2078_;
}
pub unsafe fn l_Lake_MainM_runLogIO___redArg___lam__0(
    mut v_val_2081_: *mut leanh::LeanObject,
    mut v___y_2082_: u8,
    mut v_val_2083_: u8,
    mut v_x_2084_: *mut leanh::LeanObject,
    mut v___y_2085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2087_ = l_Lake_logToStream(v___y_2085_, v_val_2081_, v___y_2082_, v_val_2083_);
    return v___x_2087_;
}
pub unsafe fn l_Lake_MainM_runLogIO___redArg___lam__0___boxed(
    mut v_val_2088_: *mut leanh::LeanObject,
    mut v___y_2089_: *mut leanh::LeanObject,
    mut v_val_2090_: *mut leanh::LeanObject,
    mut v_x_2091_: *mut leanh::LeanObject,
    mut v___y_2092_: *mut leanh::LeanObject,
    mut v___y_2093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_373__boxed_2094_: u8 = 0;
    let mut v_val_374__boxed_2095_: u8 = 0;
    let mut v_res_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_373__boxed_2094_ = (leanh::lean_unbox(v___y_2089_) as u8);
    v_val_374__boxed_2095_ = (leanh::lean_unbox(v_val_2090_) as u8);
    v_res_2096_ = l_Lake_MainM_runLogIO___redArg___lam__0(
        v_val_2088_,
        v___y_373__boxed_2094_,
        v_val_374__boxed_2095_,
        v_x_2091_,
        v___y_2092_,
    );
    leanh::lean_dec_ref(v___y_2092_);
    return v_res_2096_;
}
pub unsafe fn l_Lake_MainM_runLogIO___redArg(
    mut v_x_2099_: *mut leanh::LeanObject,
    mut v_cfg_2100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2107_: u8 = 0;
    let mut v_val_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2111_: u8 = 0;
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2115_: u8 = 0;
    let mut v___y_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2118_: u8 = 0;
    let mut v___y_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2124_: u8 = 0;
    let mut v___y_2125_: u8 = 0;
    let mut v_ansiMode_2126_: u8 = 0;
    let mut v_out_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: u8 = 0;
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: u8 = 0;
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: u8 = 0;
    let mut v___x_2138_: usize = 0;
    let mut v___x_2139_: usize = 0;
    let mut v___x_141__overap_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: usize = 0;
    let mut v___x_2143_: usize = 0;
    let mut v___x_145__overap_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2149_: u8 = 0;
    let mut v___x_2150_: u8 = 0;
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_failLv_2155_: u8 = 0;
    let mut v_outLv_2156_: u8 = 0;
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: u8 = 0;
    let mut v___x_2159_: u8 = 0;
    let mut v___x_2160_: u8 = 0;
    let mut v___x_2161_: u8 = 0;
    let mut v_a_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2120_ = l_instMonadBaseIO;
                v___x_2151_ = l_Lake_MainM_runLogIO___redArg___closed__0;
                v___x_2152_ =
                    leanh::lean_apply_2(v_x_2099_, v___x_2151_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_2152_) == 0 {
                    v_a_2153_ = leanh::lean_ctor_get(v___x_2152_, 0);
                    leanh::lean_inc(v_a_2153_);
                    v_a_2154_ = leanh::lean_ctor_get(v___x_2152_, 1);
                    leanh::lean_inc(v_a_2154_);
                    leanh::lean_dec_ref_known(v___x_2152_, 2);
                    v_failLv_2155_ = leanh::lean_ctor_get_uint8(
                        v_cfg_2100_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    v_outLv_2156_ = leanh::lean_ctor_get_uint8(
                        v_cfg_2100_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                    );
                    v___x_2157_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2157_, 0, v_a_2153_);
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
                    v_a_2162_ = leanh::lean_ctor_get(v___x_2152_, 1);
                    leanh::lean_inc(v_a_2162_);
                    leanh::lean_dec_ref_known(v___x_2152_, 2);
                    v___x_2163_ = leanh::lean_box(0);
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
                v___x_2104_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2104_, 0, v___x_2103_);
                return v___x_2104_;
            }
            2 => {
                if v___y_2107_ == 0 {
                    if leanh::lean_obj_tag(v___y_2106_) == 0 {
                        state = 1;
                        continue;
                    } else {
                        v_val_2108_ = leanh::lean_ctor_get(v___y_2106_, 0);
                        v_isSharedCheck_2115_ =
                            (!leanh::lean_is_exclusive(v___y_2106_)) as u8;
                        if v_isSharedCheck_2115_ == 0 {
                            v___x_2110_ = v___y_2106_;
                            v_isShared_2111_ = v_isSharedCheck_2115_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2108_);
                            leanh::lean_dec(v___y_2106_);
                            v___x_2110_ = leanh::lean_box(0);
                            v_isShared_2111_ = v_isSharedCheck_2115_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_2106_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_2111_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2110_, 0);
                    v___x_2113_ = v___x_2110_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2114_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_val_2108_);
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
                v_ansiMode_2126_ = leanh::lean_ctor_get_uint8(
                    v_cfg_2100_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 2) as u32,
                );
                v_out_2127_ = leanh::lean_ctor_get(v_cfg_2100_, 0);
                v___x_2128_ = l_Lake_OutStream_get(v_out_2127_);
                leanh::lean_inc_ref(v___x_2128_);
                v___x_2129_ = l_Lake_AnsiMode_isEnabled(v___x_2128_, v_ansiMode_2126_);
                v___x_2130_ = leanh::lean_unsigned_to_nat(0);
                v___x_2131_ = lean_array_get_size(v___y_2123_);
                v___x_2132_ = lean_nat_dec_lt(v___x_2130_, v___x_2131_);
                if v___x_2132_ == 0 {
                    leanh::lean_dec_ref(v___x_2128_);
                    leanh::lean_dec_ref(v___y_2123_);
                    v___y_2106_ = v___y_2122_;
                    v___y_2107_ = v___y_2124_;
                    state = 2;
                    continue;
                } else {
                    v___x_2133_ = leanh::lean_box((v___y_2125_) as usize);
                    v___x_2134_ = leanh::lean_box((v___x_2129_) as usize);
                    v___f_2135_ = leanh::lean_alloc_closure(
                        l_Lake_MainM_runLogIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        6,
                        3,
                    );
                    leanh::lean_closure_set(v___f_2135_, 0, v___x_2128_);
                    leanh::lean_closure_set(v___f_2135_, 1, v___x_2133_);
                    leanh::lean_closure_set(v___f_2135_, 2, v___x_2134_);
                    v___x_2136_ = leanh::lean_box(0);
                    v___x_2137_ = lean_nat_dec_le(v___x_2131_, v___x_2131_);
                    if v___x_2137_ == 0 {
                        if v___x_2132_ == 0 {
                            leanh::lean_dec_ref(v___f_2135_);
                            leanh::lean_dec_ref(v___y_2123_);
                            v___y_2106_ = v___y_2122_;
                            v___y_2107_ = v___y_2124_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2138_ = 0usize;
                            v___x_2139_ = lean_usize_of_nat(v___x_2131_);
                            v___x_141__overap_2140_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_2120_,
                                    v___f_2135_,
                                    v___y_2123_,
                                    v___x_2138_,
                                    v___x_2139_,
                                    v___x_2136_,
                                );
                            v___x_2141_ = leanh::lean_apply_1(
                                v___x_141__overap_2140_,
                                leanh::lean_box(0),
                            );
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
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v___x_2120_,
                                v___f_2135_,
                                v___y_2123_,
                                v___x_2142_,
                                v___x_2143_,
                                v___x_2136_,
                            );
                        v___x_2145_ = leanh::lean_apply_1(
                            v___x_145__overap_2144_,
                            leanh::lean_box(0),
                        );
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
    mut v_x_2165_: *mut leanh::LeanObject,
    mut v_cfg_2166_: *mut leanh::LeanObject,
    mut v_a_2167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2168_ = l_Lake_MainM_runLogIO___redArg(v_x_2165_, v_cfg_2166_);
    leanh::lean_dec_ref(v_cfg_2166_);
    return v_res_2168_;
}
pub unsafe fn l_Lake_MainM_runLogIO(
    mut v_00_u03b1_2169_: *mut leanh::LeanObject,
    mut v_x_2170_: *mut leanh::LeanObject,
    mut v_cfg_2171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2178_: u8 = 0;
    let mut v_val_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2182_: u8 = 0;
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2186_: u8 = 0;
    let mut v___y_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2189_: u8 = 0;
    let mut v___y_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2195_: u8 = 0;
    let mut v___y_2196_: u8 = 0;
    let mut v_ansiMode_2197_: u8 = 0;
    let mut v_out_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: u8 = 0;
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: u8 = 0;
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: u8 = 0;
    let mut v___x_2209_: usize = 0;
    let mut v___x_2210_: usize = 0;
    let mut v___x_302__overap_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: usize = 0;
    let mut v___x_2214_: usize = 0;
    let mut v___x_305__overap_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2220_: u8 = 0;
    let mut v___x_2221_: u8 = 0;
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_failLv_2226_: u8 = 0;
    let mut v_outLv_2227_: u8 = 0;
    let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: u8 = 0;
    let mut v___x_2230_: u8 = 0;
    let mut v___x_2231_: u8 = 0;
    let mut v___x_2232_: u8 = 0;
    let mut v_a_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2191_ = l_instMonadBaseIO;
                v___x_2222_ = l_Lake_MainM_runLogIO___redArg___closed__0;
                v___x_2223_ =
                    leanh::lean_apply_2(v_x_2170_, v___x_2222_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_2223_) == 0 {
                    v_a_2224_ = leanh::lean_ctor_get(v___x_2223_, 0);
                    leanh::lean_inc(v_a_2224_);
                    v_a_2225_ = leanh::lean_ctor_get(v___x_2223_, 1);
                    leanh::lean_inc(v_a_2225_);
                    leanh::lean_dec_ref_known(v___x_2223_, 2);
                    v_failLv_2226_ = leanh::lean_ctor_get_uint8(
                        v_cfg_2171_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    v_outLv_2227_ = leanh::lean_ctor_get_uint8(
                        v_cfg_2171_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                    );
                    v___x_2228_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2228_, 0, v_a_2224_);
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
                    v_a_2233_ = leanh::lean_ctor_get(v___x_2223_, 1);
                    leanh::lean_inc(v_a_2233_);
                    leanh::lean_dec_ref_known(v___x_2223_, 2);
                    v___x_2234_ = leanh::lean_box(0);
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
                v___x_2175_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2175_, 0, v___x_2174_);
                return v___x_2175_;
            }
            2 => {
                if v___y_2178_ == 0 {
                    if leanh::lean_obj_tag(v___y_2177_) == 0 {
                        state = 1;
                        continue;
                    } else {
                        v_val_2179_ = leanh::lean_ctor_get(v___y_2177_, 0);
                        v_isSharedCheck_2186_ =
                            (!leanh::lean_is_exclusive(v___y_2177_)) as u8;
                        if v_isSharedCheck_2186_ == 0 {
                            v___x_2181_ = v___y_2177_;
                            v_isShared_2182_ = v_isSharedCheck_2186_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2179_);
                            leanh::lean_dec(v___y_2177_);
                            v___x_2181_ = leanh::lean_box(0);
                            v_isShared_2182_ = v_isSharedCheck_2186_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_2177_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_2182_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2181_, 0);
                    v___x_2184_ = v___x_2181_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2185_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_val_2179_);
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
                v_ansiMode_2197_ = leanh::lean_ctor_get_uint8(
                    v_cfg_2171_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 2) as u32,
                );
                v_out_2198_ = leanh::lean_ctor_get(v_cfg_2171_, 0);
                v___x_2199_ = l_Lake_OutStream_get(v_out_2198_);
                leanh::lean_inc_ref(v___x_2199_);
                v___x_2200_ = l_Lake_AnsiMode_isEnabled(v___x_2199_, v_ansiMode_2197_);
                v___x_2201_ = leanh::lean_unsigned_to_nat(0);
                v___x_2202_ = lean_array_get_size(v___y_2194_);
                v___x_2203_ = lean_nat_dec_lt(v___x_2201_, v___x_2202_);
                if v___x_2203_ == 0 {
                    leanh::lean_dec_ref(v___x_2199_);
                    leanh::lean_dec_ref(v___y_2194_);
                    v___y_2177_ = v___y_2193_;
                    v___y_2178_ = v___y_2195_;
                    state = 2;
                    continue;
                } else {
                    v___x_2204_ = leanh::lean_box((v___y_2196_) as usize);
                    v___x_2205_ = leanh::lean_box((v___x_2200_) as usize);
                    v___f_2206_ = leanh::lean_alloc_closure(
                        l_Lake_MainM_runLogIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        6,
                        3,
                    );
                    leanh::lean_closure_set(v___f_2206_, 0, v___x_2199_);
                    leanh::lean_closure_set(v___f_2206_, 1, v___x_2204_);
                    leanh::lean_closure_set(v___f_2206_, 2, v___x_2205_);
                    v___x_2207_ = leanh::lean_box(0);
                    v___x_2208_ = lean_nat_dec_le(v___x_2202_, v___x_2202_);
                    if v___x_2208_ == 0 {
                        if v___x_2203_ == 0 {
                            leanh::lean_dec_ref(v___f_2206_);
                            leanh::lean_dec_ref(v___y_2194_);
                            v___y_2177_ = v___y_2193_;
                            v___y_2178_ = v___y_2195_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2209_ = 0usize;
                            v___x_2210_ = lean_usize_of_nat(v___x_2202_);
                            v___x_302__overap_2211_ =
                                l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_2191_,
                                    v___f_2206_,
                                    v___y_2194_,
                                    v___x_2209_,
                                    v___x_2210_,
                                    v___x_2207_,
                                );
                            v___x_2212_ = leanh::lean_apply_1(
                                v___x_302__overap_2211_,
                                leanh::lean_box(0),
                            );
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
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v___x_2191_,
                                v___f_2206_,
                                v___y_2194_,
                                v___x_2213_,
                                v___x_2214_,
                                v___x_2207_,
                            );
                        v___x_2216_ = leanh::lean_apply_1(
                            v___x_305__overap_2215_,
                            leanh::lean_box(0),
                        );
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
    mut v_00_u03b1_2236_: *mut leanh::LeanObject,
    mut v_x_2237_: *mut leanh::LeanObject,
    mut v_cfg_2238_: *mut leanh::LeanObject,
    mut v_a_2239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2240_ = l_Lake_MainM_runLogIO(v_00_u03b1_2236_, v_x_2237_, v_cfg_2238_);
    leanh::lean_dec_ref(v_cfg_2238_);
    return v_res_2240_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0(
    mut v_val_2241_: *mut leanh::LeanObject,
    mut v___y_2242_: u8,
    mut v_val_2243_: u8,
    mut v_as_2244_: *mut leanh::LeanObject,
    mut v_i_2245_: usize,
    mut v_stop_2246_: usize,
    mut v_b_2247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2249_: u8 = 0;
    let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: usize = 0;
    let mut v___x_2253_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2249_ = lean_usize_dec_eq(v_i_2245_, v_stop_2246_);
                if v___x_2249_ == 0 {
                    v___x_2250_ = lean_array_uget_borrowed(v_as_2244_, v_i_2245_);
                    leanh::lean_inc_ref(v_val_2241_);
                    v___x_2251_ =
                        l_Lake_logToStream(v___x_2250_, v_val_2241_, v___y_2242_, v_val_2243_);
                    v___x_2252_ = 1usize;
                    v___x_2253_ = lean_usize_add(v_i_2245_, v___x_2252_);
                    v_i_2245_ = v___x_2253_;
                    v_b_2247_ = v___x_2251_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_val_2241_);
                    return v_b_2247_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0___boxed(
    mut v_val_2255_: *mut leanh::LeanObject,
    mut v___y_2256_: *mut leanh::LeanObject,
    mut v_val_2257_: *mut leanh::LeanObject,
    mut v_as_2258_: *mut leanh::LeanObject,
    mut v_i_2259_: *mut leanh::LeanObject,
    mut v_stop_2260_: *mut leanh::LeanObject,
    mut v_b_2261_: *mut leanh::LeanObject,
    mut v___y_2262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_227__boxed_2263_: u8 = 0;
    let mut v_val_228__boxed_2264_: u8 = 0;
    let mut v_i_boxed_2265_: usize = 0;
    let mut v_stop_boxed_2266_: usize = 0;
    let mut v_res_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_227__boxed_2263_ = (leanh::lean_unbox(v___y_2256_) as u8);
    v_val_228__boxed_2264_ = (leanh::lean_unbox(v_val_2257_) as u8);
    v_i_boxed_2265_ = leanh::lean_unbox_usize(v_i_2259_);
    leanh::lean_dec(v_i_2259_);
    v_stop_boxed_2266_ = leanh::lean_unbox_usize(v_stop_2260_);
    leanh::lean_dec(v_stop_2260_);
    v_res_2267_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0(v_val_2255_, v___y_227__boxed_2263_, v_val_228__boxed_2264_, v_as_2258_, v_i_boxed_2265_, v_stop_boxed_2266_, v_b_2261_);
    leanh::lean_dec_ref(v_as_2258_);
    return v_res_2267_;
}
pub unsafe fn l_Lake_MainM_liftLogIO___redArg(
    mut v_x_2268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2275_: u8 = 0;
    let mut v_val_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2279_: u8 = 0;
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2283_: u8 = 0;
    let mut v___y_2285_: u8 = 0;
    let mut v___y_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: u8 = 0;
    let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2295_: u8 = 0;
    let mut v___y_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2297_: u8 = 0;
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: u8 = 0;
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: u8 = 0;
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: u8 = 0;
    let mut v___x_2304_: usize = 0;
    let mut v___x_2305_: usize = 0;
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: usize = 0;
    let mut v___x_2308_: usize = 0;
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2313_: u8 = 0;
    let mut v___x_2314_: u8 = 0;
    let mut v_a_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: u8 = 0;
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: u8 = 0;
    let mut v___x_2320_: u8 = 0;
    let mut v___x_2321_: u8 = 0;
    let mut v___x_2322_: u8 = 0;
    let mut v___x_2323_: u8 = 0;
    let mut v_a_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2288_ = leanh::lean_unsigned_to_nat(0);
                v___x_2289_ = l_Lake_MainM_runLogIO___redArg___closed__0;
                v___x_2290_ =
                    leanh::lean_apply_2(v_x_2268_, v___x_2289_, leanh::lean_box(0));
                v___x_2291_ = 0;
                v___x_2292_ = leanh::lean_box(1);
                if leanh::lean_obj_tag(v___x_2290_) == 0 {
                    v_a_2315_ = leanh::lean_ctor_get(v___x_2290_, 0);
                    leanh::lean_inc(v_a_2315_);
                    v_a_2316_ = leanh::lean_ctor_get(v___x_2290_, 1);
                    leanh::lean_inc(v_a_2316_);
                    leanh::lean_dec_ref_known(v___x_2290_, 2);
                    v___x_2317_ = 3;
                    v___x_2318_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2318_, 0, v_a_2315_);
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
                    v_a_2324_ = leanh::lean_ctor_get(v___x_2290_, 1);
                    leanh::lean_inc(v_a_2324_);
                    leanh::lean_dec_ref_known(v___x_2290_, 2);
                    v___x_2325_ = leanh::lean_box(0);
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
                v___x_2272_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2272_, 0, v___x_2271_);
                return v___x_2272_;
            }
            2 => {
                if v___y_2275_ == 0 {
                    if leanh::lean_obj_tag(v___y_2274_) == 0 {
                        state = 1;
                        continue;
                    } else {
                        v_val_2276_ = leanh::lean_ctor_get(v___y_2274_, 0);
                        v_isSharedCheck_2283_ =
                            (!leanh::lean_is_exclusive(v___y_2274_)) as u8;
                        if v_isSharedCheck_2283_ == 0 {
                            v___x_2278_ = v___y_2274_;
                            v_isShared_2279_ = v_isSharedCheck_2283_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2276_);
                            leanh::lean_dec(v___y_2274_);
                            v___x_2278_ = leanh::lean_box(0);
                            v_isShared_2279_ = v_isSharedCheck_2283_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_2274_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_2279_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2278_, 0);
                    v___x_2281_ = v___x_2278_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2282_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_val_2276_);
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
                leanh::lean_inc_ref(v___x_2298_);
                v___x_2299_ = l_Lake_AnsiMode_isEnabled(v___x_2298_, v___x_2291_);
                v___x_2300_ = lean_array_get_size(v___y_2294_);
                v___x_2301_ = lean_nat_dec_lt(v___x_2288_, v___x_2300_);
                if v___x_2301_ == 0 {
                    leanh::lean_dec_ref(v___x_2298_);
                    leanh::lean_dec_ref(v___y_2294_);
                    v___y_2274_ = v___y_2296_;
                    v___y_2275_ = v___y_2295_;
                    state = 2;
                    continue;
                } else {
                    v___x_2302_ = leanh::lean_box(0);
                    v___x_2303_ = lean_nat_dec_le(v___x_2300_, v___x_2300_);
                    if v___x_2303_ == 0 {
                        if v___x_2301_ == 0 {
                            leanh::lean_dec_ref(v___x_2298_);
                            leanh::lean_dec_ref(v___y_2294_);
                            v___y_2274_ = v___y_2296_;
                            v___y_2275_ = v___y_2295_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2304_ = 0usize;
                            v___x_2305_ = lean_usize_of_nat(v___x_2300_);
                            v___x_2306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0(v___x_2298_, v___y_2297_, v___x_2299_, v___y_2294_, v___x_2304_, v___x_2305_, v___x_2302_);
                            leanh::lean_dec_ref(v___y_2294_);
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
                        leanh::lean_dec_ref(v___y_2294_);
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
    mut v_x_2327_: *mut leanh::LeanObject,
    mut v_a_2328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2329_ = l_Lake_MainM_liftLogIO___redArg(v_x_2327_);
    return v_res_2329_;
}
pub unsafe fn l_Lake_MainM_liftLogIO(
    mut v_00_u03b1_2330_: *mut leanh::LeanObject,
    mut v_x_2331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2333_ = l_Lake_MainM_liftLogIO___redArg(v_x_2331_);
    return v___x_2333_;
}
pub unsafe fn l_Lake_MainM_liftLogIO___boxed(
    mut v_00_u03b1_2334_: *mut leanh::LeanObject,
    mut v_x_2335_: *mut leanh::LeanObject,
    mut v_a_2336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2337_ = l_Lake_MainM_liftLogIO(v_00_u03b1_2334_, v_x_2335_);
    return v_res_2337_;
}
pub unsafe fn l_Lake_MainM_runLoggerIO___redArg___lam__0(
    mut v_val_2340_: *mut leanh::LeanObject,
    mut v_outLv_2341_: u8,
    mut v_val_2342_: u8,
    mut v_e_2343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2345_ = l_Lake_logToStream(v_e_2343_, v_val_2340_, v_outLv_2341_, v_val_2342_);
    return v___x_2345_;
}
pub unsafe fn l_Lake_MainM_runLoggerIO___redArg___lam__0___boxed(
    mut v_val_2346_: *mut leanh::LeanObject,
    mut v_outLv_2347_: *mut leanh::LeanObject,
    mut v_val_2348_: *mut leanh::LeanObject,
    mut v_e_2349_: *mut leanh::LeanObject,
    mut v___y_2350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_outLv_boxed_2351_: u8 = 0;
    let mut v_val_188__boxed_2352_: u8 = 0;
    let mut v_res_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_outLv_boxed_2351_ = (leanh::lean_unbox(v_outLv_2347_) as u8);
    v_val_188__boxed_2352_ = (leanh::lean_unbox(v_val_2348_) as u8);
    v_res_2353_ = l_Lake_MainM_runLoggerIO___redArg___lam__0(
        v_val_2346_,
        v_outLv_boxed_2351_,
        v_val_188__boxed_2352_,
        v_e_2349_,
    );
    leanh::lean_dec_ref(v_e_2349_);
    return v_res_2353_;
}
pub unsafe fn l_Lake_MainM_runLoggerIO___redArg(
    mut v_x_2354_: *mut leanh::LeanObject,
    mut v_cfg_2355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_outLv_2357_: u8 = 0;
    let mut v_ansiMode_2358_: u8 = 0;
    let mut v_out_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: u8 = 0;
    let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2369_: u8 = 0;
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2373_: u8 = 0;
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2376_: u8 = 0;
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2381_: u8 = 0;
    let mut v_unused_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_outLv_2357_ = leanh::lean_ctor_get_uint8(
                    v_cfg_2355_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                );
                v_ansiMode_2358_ = leanh::lean_ctor_get_uint8(
                    v_cfg_2355_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 2) as u32,
                );
                v_out_2359_ = leanh::lean_ctor_get(v_cfg_2355_, 0);
                v___x_2360_ = l_Lake_OutStream_get(v_out_2359_);
                leanh::lean_inc_ref(v___x_2360_);
                v___x_2361_ = l_Lake_AnsiMode_isEnabled(v___x_2360_, v_ansiMode_2358_);
                v___x_2362_ = leanh::lean_box((v_outLv_2357_) as usize);
                v___x_2363_ = leanh::lean_box((v___x_2361_) as usize);
                v___f_2364_ = leanh::lean_alloc_closure(
                    l_Lake_MainM_runLoggerIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                leanh::lean_closure_set(v___f_2364_, 0, v___x_2360_);
                leanh::lean_closure_set(v___f_2364_, 1, v___x_2362_);
                leanh::lean_closure_set(v___f_2364_, 2, v___x_2363_);
                v___x_2365_ =
                    leanh::lean_apply_2(v_x_2354_, v___f_2364_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_2365_) == 0 {
                    v_a_2366_ = leanh::lean_ctor_get(v___x_2365_, 0);
                    v_isSharedCheck_2373_ = (!leanh::lean_is_exclusive(v___x_2365_)) as u8;
                    if v_isSharedCheck_2373_ == 0 {
                        v___x_2368_ = v___x_2365_;
                        v_isShared_2369_ = v_isSharedCheck_2373_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2366_);
                        leanh::lean_dec(v___x_2365_);
                        v___x_2368_ = leanh::lean_box(0);
                        v_isShared_2369_ = v_isSharedCheck_2373_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_2381_ = (!leanh::lean_is_exclusive(v___x_2365_)) as u8;
                    if v_isSharedCheck_2381_ == 0 {
                        v_unused_2382_ = leanh::lean_ctor_get(v___x_2365_, 0);
                        leanh::lean_dec(v_unused_2382_);
                        v___x_2375_ = v___x_2365_;
                        v_isShared_2376_ = v_isSharedCheck_2381_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2365_);
                        v___x_2375_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2372_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
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
                    leanh::lean_ctor_set(v___x_2375_, 0, v___x_2377_);
                    v___x_2379_ = v___x_2375_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2380_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2377_);
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
    mut v_x_2383_: *mut leanh::LeanObject,
    mut v_cfg_2384_: *mut leanh::LeanObject,
    mut v_a_2385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2386_ = l_Lake_MainM_runLoggerIO___redArg(v_x_2383_, v_cfg_2384_);
    leanh::lean_dec_ref(v_cfg_2384_);
    return v_res_2386_;
}
pub unsafe fn l_Lake_MainM_runLoggerIO(
    mut v_00_u03b1_2387_: *mut leanh::LeanObject,
    mut v_x_2388_: *mut leanh::LeanObject,
    mut v_cfg_2389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_outLv_2391_: u8 = 0;
    let mut v_ansiMode_2392_: u8 = 0;
    let mut v_out_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: u8 = 0;
    let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2403_: u8 = 0;
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2407_: u8 = 0;
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2410_: u8 = 0;
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2415_: u8 = 0;
    let mut v_unused_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_outLv_2391_ = leanh::lean_ctor_get_uint8(
                    v_cfg_2389_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                );
                v_ansiMode_2392_ = leanh::lean_ctor_get_uint8(
                    v_cfg_2389_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 2) as u32,
                );
                v_out_2393_ = leanh::lean_ctor_get(v_cfg_2389_, 0);
                v___x_2394_ = l_Lake_OutStream_get(v_out_2393_);
                leanh::lean_inc_ref(v___x_2394_);
                v___x_2395_ = l_Lake_AnsiMode_isEnabled(v___x_2394_, v_ansiMode_2392_);
                v___x_2396_ = leanh::lean_box((v_outLv_2391_) as usize);
                v___x_2397_ = leanh::lean_box((v___x_2395_) as usize);
                v___f_2398_ = leanh::lean_alloc_closure(
                    l_Lake_MainM_runLoggerIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                leanh::lean_closure_set(v___f_2398_, 0, v___x_2394_);
                leanh::lean_closure_set(v___f_2398_, 1, v___x_2396_);
                leanh::lean_closure_set(v___f_2398_, 2, v___x_2397_);
                v___x_2399_ =
                    leanh::lean_apply_2(v_x_2388_, v___f_2398_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_2399_) == 0 {
                    v_a_2400_ = leanh::lean_ctor_get(v___x_2399_, 0);
                    v_isSharedCheck_2407_ = (!leanh::lean_is_exclusive(v___x_2399_)) as u8;
                    if v_isSharedCheck_2407_ == 0 {
                        v___x_2402_ = v___x_2399_;
                        v_isShared_2403_ = v_isSharedCheck_2407_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2400_);
                        leanh::lean_dec(v___x_2399_);
                        v___x_2402_ = leanh::lean_box(0);
                        v_isShared_2403_ = v_isSharedCheck_2407_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_2415_ = (!leanh::lean_is_exclusive(v___x_2399_)) as u8;
                    if v_isSharedCheck_2415_ == 0 {
                        v_unused_2416_ = leanh::lean_ctor_get(v___x_2399_, 0);
                        leanh::lean_dec(v_unused_2416_);
                        v___x_2409_ = v___x_2399_;
                        v_isShared_2410_ = v_isSharedCheck_2415_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2399_);
                        v___x_2409_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2406_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
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
                    leanh::lean_ctor_set(v___x_2409_, 0, v___x_2411_);
                    v___x_2413_ = v___x_2409_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2414_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2411_);
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
    mut v_00_u03b1_2417_: *mut leanh::LeanObject,
    mut v_x_2418_: *mut leanh::LeanObject,
    mut v_cfg_2419_: *mut leanh::LeanObject,
    mut v_a_2420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2421_ = l_Lake_MainM_runLoggerIO(v_00_u03b1_2417_, v_x_2418_, v_cfg_2419_);
    leanh::lean_dec_ref(v_cfg_2419_);
    return v_res_2421_;
}
pub unsafe fn l_Lake_MainM_liftLoggerIO___redArg___lam__0(
    mut v_val_2422_: *mut leanh::LeanObject,
    mut v___x_2423_: u8,
    mut v_val_2424_: u8,
    mut v_e_2425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2427_ = l_Lake_logToStream(v_e_2425_, v_val_2422_, v___x_2423_, v_val_2424_);
    return v___x_2427_;
}
pub unsafe fn l_Lake_MainM_liftLoggerIO___redArg___lam__0___boxed(
    mut v_val_2428_: *mut leanh::LeanObject,
    mut v___x_2429_: *mut leanh::LeanObject,
    mut v_val_2430_: *mut leanh::LeanObject,
    mut v_e_2431_: *mut leanh::LeanObject,
    mut v___y_2432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_38__boxed_2433_: u8 = 0;
    let mut v_val_39__boxed_2434_: u8 = 0;
    let mut v_res_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_38__boxed_2433_ = (leanh::lean_unbox(v___x_2429_) as u8);
    v_val_39__boxed_2434_ = (leanh::lean_unbox(v_val_2430_) as u8);
    v_res_2435_ = l_Lake_MainM_liftLoggerIO___redArg___lam__0(
        v_val_2428_,
        v___x_38__boxed_2433_,
        v_val_39__boxed_2434_,
        v_e_2431_,
    );
    leanh::lean_dec_ref(v_e_2431_);
    return v_res_2435_;
}
pub unsafe fn l_Lake_MainM_liftLoggerIO___redArg(
    mut v_x_2436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: u8 = 0;
    let mut v___x_2441_: u8 = 0;
    let mut v___x_2442_: u8 = 0;
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2450_: u8 = 0;
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2454_: u8 = 0;
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2457_: u8 = 0;
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2462_: u8 = 0;
    let mut v_unused_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2438_ = leanh::lean_box(1);
                v___x_2439_ = l_Lake_OutStream_get(v___x_2438_);
                v___x_2440_ = 0;
                leanh::lean_inc_ref(v___x_2439_);
                v___x_2441_ = l_Lake_AnsiMode_isEnabled(v___x_2439_, v___x_2440_);
                v___x_2442_ = 1;
                v___x_2443_ = leanh::lean_box((v___x_2442_) as usize);
                v___x_2444_ = leanh::lean_box((v___x_2441_) as usize);
                v___f_2445_ = leanh::lean_alloc_closure(
                    l_Lake_MainM_liftLoggerIO___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                leanh::lean_closure_set(v___f_2445_, 0, v___x_2439_);
                leanh::lean_closure_set(v___f_2445_, 1, v___x_2443_);
                leanh::lean_closure_set(v___f_2445_, 2, v___x_2444_);
                v___x_2446_ =
                    leanh::lean_apply_2(v_x_2436_, v___f_2445_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_2446_) == 0 {
                    v_a_2447_ = leanh::lean_ctor_get(v___x_2446_, 0);
                    v_isSharedCheck_2454_ = (!leanh::lean_is_exclusive(v___x_2446_)) as u8;
                    if v_isSharedCheck_2454_ == 0 {
                        v___x_2449_ = v___x_2446_;
                        v_isShared_2450_ = v_isSharedCheck_2454_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2447_);
                        leanh::lean_dec(v___x_2446_);
                        v___x_2449_ = leanh::lean_box(0);
                        v_isShared_2450_ = v_isSharedCheck_2454_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_2462_ = (!leanh::lean_is_exclusive(v___x_2446_)) as u8;
                    if v_isSharedCheck_2462_ == 0 {
                        v_unused_2463_ = leanh::lean_ctor_get(v___x_2446_, 0);
                        leanh::lean_dec(v_unused_2463_);
                        v___x_2456_ = v___x_2446_;
                        v_isShared_2457_ = v_isSharedCheck_2462_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2446_);
                        v___x_2456_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2453_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
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
                    leanh::lean_ctor_set(v___x_2456_, 0, v___x_2458_);
                    v___x_2460_ = v___x_2456_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2461_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2458_);
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
    mut v_x_2464_: *mut leanh::LeanObject,
    mut v_a_2465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2466_ = l_Lake_MainM_liftLoggerIO___redArg(v_x_2464_);
    return v_res_2466_;
}
pub unsafe fn l_Lake_MainM_liftLoggerIO(
    mut v_00_u03b1_2467_: *mut leanh::LeanObject,
    mut v_x_2468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2470_ = l_Lake_MainM_liftLoggerIO___redArg(v_x_2468_);
    return v___x_2470_;
}
pub unsafe fn l_Lake_MainM_liftLoggerIO___boxed(
    mut v_00_u03b1_2471_: *mut leanh::LeanObject,
    mut v_x_2472_: *mut leanh::LeanObject,
    mut v_a_2473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2474_ = l_Lake_MainM_liftLoggerIO(v_00_u03b1_2471_, v_x_2472_);
    return v_res_2474_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_MainM(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Util_Log(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Exit(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lake_MainM_tryCatchError___redArg___boxed__const__1 =
        _init_l_Lake_MainM_tryCatchError___redArg___boxed__const__1();
    leanh::lean_mark_persistent(l_Lake_MainM_tryCatchError___redArg___boxed__const__1);
    l_Lake_MainM_failure___redArg___boxed__const__1 =
        _init_l_Lake_MainM_failure___redArg___boxed__const__1();
    leanh::lean_mark_persistent(l_Lake_MainM_failure___redArg___boxed__const__1);
    l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative =
        _init_l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative();
    leanh::lean_mark_persistent(l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_MainM(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_MainM(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Util_Log(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Exit(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_MainM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_MainM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Util_MainM(builtin);
}
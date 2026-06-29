// Lean compiler output
// Module: Lean.Server.FileWorker.SetupFile
// Imports: Lean.Server.Utils Lean.Util.LakePath Lean.Server.ServerTask
use crate::r#gen::Init::Data::String::Defs::l_String_intercalate;
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_trimAscii;
use crate::r#gen::Init::System::IO::{
    l_IO_FS_Handle_putStrLn, l_IO_FS_Handle_readToEnd, l_System_FilePath_pathExists,
};
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
use crate::r#gen::Init::System::Uri::l_System_Uri_fileUriToPath_x3f;
use crate::r#gen::Lean::Data::Json::Parser::l_Lean_Json_parse;
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_compress;
use crate::r#gen::Lean::LoadDynlib::lean_load_dynlib;
use crate::r#gen::Lean::Server::ServerTask::{
    initialize_Lean_Server_ServerTask, l_Lean_Server_ServerTask_IO_asTask___redArg,
    runtime_initialize_Lean_Server_ServerTask,
};
use crate::r#gen::Lean::Server::Utils::{
    initialize_Lean_Server_Utils, runtime_initialize_Lean_Server_Utils,
};
use crate::r#gen::Lean::Setup::{
    l_Lean_instFromJsonModuleSetup_fromJson, l_Lean_instToJsonModuleHeader_toJson,
};
use crate::r#gen::Lean::Util::LakePath::{
    initialize_Lean_Util_LakePath, l_Lean_determineLakePath, runtime_initialize_Lean_Util_LakePath,
};
use crate::ffi::lean_task_get_own;
use crate::ffi::lean_array_uget_borrowed;
use crate::ffi::lean_string_utf8_extract;
use crate::ffi::lean_string_append;
use crate::ffi::{lean_usize_add, lean_usize_of_nat};
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_dec_le, lean_nat_dec_lt, lean_string_dec_eq, lean_string_utf8_byte_size,
    lean_uint32_dec_eq, lean_usize_dec_eq,
};
use crate::ffi::{
    lean_io_prim_handle_get_line, lean_io_process_child_take_stdin, lean_io_process_child_wait,
    lean_io_process_spawn,
};
pub static l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_runLakeSetupFile___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [0 as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Server_FileWorker_runLakeSetupFile___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_runLakeSetupFile___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_runLakeSetupFile___closed__1_value:
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
static mut l_Lean_Server_FileWorker_runLakeSetupFile___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_runLakeSetupFile___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_runLakeSetupFile___closed__2_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [2 as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Server_FileWorker_runLakeSetupFile___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_runLakeSetupFile___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_runLakeSetupFile___closed__3_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [115, 101, 116, 117, 112, 45, 102, 105, 108, 101, 0],
};
static mut l_Lean_Server_FileWorker_runLakeSetupFile___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_runLakeSetupFile___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_runLakeSetupFile___closed__4_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [45, 0],
};
static mut l_Lean_Server_FileWorker_runLakeSetupFile___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_runLakeSetupFile___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_FileWorker_runLakeSetupFile___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_FileWorker_runLakeSetupFile___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_FileWorker_runLakeSetupFile___closed__6_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [45, 45, 110, 111, 45, 98, 117, 105, 108, 100, 0],
};
static mut l_Lean_Server_FileWorker_runLakeSetupFile___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_runLakeSetupFile___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_runLakeSetupFile___closed__7_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [45, 45, 110, 111, 45, 99, 97, 99, 104, 101, 0],
};
static mut l_Lean_Server_FileWorker_runLakeSetupFile___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_runLakeSetupFile___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_setupFile___closed__0_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [32, 0],
    };
static mut l_Lean_Server_FileWorker_setupFile___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_setupFile___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_setupFile___closed__1_value: crate::leanh::LeanStringObject<
    22,
> = crate::leanh::LeanStringObject {
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
        73, 110, 118, 97, 108, 105, 100, 32, 111, 117, 116, 112, 117, 116, 32, 102, 114, 111, 109,
        32, 96, 0,
    ],
};
static mut l_Lean_Server_FileWorker_setupFile___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_setupFile___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_setupFile___closed__2_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [96, 58, 10, 0],
    };
static mut l_Lean_Server_FileWorker_setupFile___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_setupFile___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_setupFile___closed__3_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [10, 115, 116, 100, 101, 114, 114, 58, 10, 0],
};
static mut l_Lean_Server_FileWorker_setupFile___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_setupFile___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_setupFile___closed__4_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [96, 0],
    };
static mut l_Lean_Server_FileWorker_setupFile___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_setupFile___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_setupFile___closed__5_value: crate::leanh::LeanStringObject<
    11,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [96, 32, 102, 97, 105, 108, 101, 100, 58, 10, 0],
};
static mut l_Lean_Server_FileWorker_setupFile___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_setupFile___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(
    mut v_handleStderr_443_: *mut crate::leanh::LeanObject,
    mut v_lakeProc_444_: *mut crate::leanh::LeanObject,
    mut v_acc_445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_stderr_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_452_: u8 = 0;
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: u8 = 0;
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_461_: u8 = 0;
    let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_465_: u8 = 0;
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_469_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stderr_447_ = crate::leanh::lean_ctor_get(v_lakeProc_444_, 2);
                v___x_448_ = lean_io_prim_handle_get_line(v_stderr_447_);
                if crate::leanh::lean_obj_tag(v___x_448_) == 0 {
                    v_a_449_ = crate::leanh::lean_ctor_get(v___x_448_, 0);
                    v_isSharedCheck_469_ = (!crate::leanh::lean_is_exclusive(v___x_448_)) as u8;
                    if v_isSharedCheck_469_ == 0 {
                        v___x_451_ = v___x_448_;
                        v_isShared_452_ = v_isSharedCheck_469_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_449_);
                        crate::leanh::lean_dec(v___x_448_);
                        v___x_451_ = crate::leanh::lean_box(0);
                        v_isShared_452_ = v_isSharedCheck_469_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_acc_445_);
                    crate::leanh::lean_dec_ref(v_handleStderr_443_);
                    return v___x_448_;
                }
            }
            1 => {
                v___x_453_ = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0;
                v___x_454_ = lean_string_dec_eq(v_a_449_, v___x_453_);
                if v___x_454_ == 0 {
                    crate::leanh::lean_del_object(v___x_451_);
                    crate::leanh::lean_inc_ref(v_handleStderr_443_);
                    crate::leanh::lean_inc(v_a_449_);
                    v___x_455_ = crate::leanh::lean_apply_2(
                        v_handleStderr_443_,
                        v_a_449_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_455_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_455_, 1);
                        v___x_456_ = lean_string_append(v_acc_445_, v_a_449_);
                        crate::leanh::lean_dec(v_a_449_);
                        v_acc_445_ = v___x_456_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_449_);
                        crate::leanh::lean_dec_ref(v_acc_445_);
                        crate::leanh::lean_dec_ref(v_handleStderr_443_);
                        v_a_458_ = crate::leanh::lean_ctor_get(v___x_455_, 0);
                        v_isSharedCheck_465_ = (!crate::leanh::lean_is_exclusive(v___x_455_)) as u8;
                        if v_isSharedCheck_465_ == 0 {
                            v___x_460_ = v___x_455_;
                            v_isShared_461_ = v_isSharedCheck_465_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_458_);
                            crate::leanh::lean_dec(v___x_455_);
                            v___x_460_ = crate::leanh::lean_box(0);
                            v_isShared_461_ = v_isSharedCheck_465_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_449_);
                    crate::leanh::lean_dec_ref(v_handleStderr_443_);
                    if v_isShared_452_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_451_, 0, v_acc_445_);
                        v___x_467_ = v___x_451_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_468_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_468_, 0, v_acc_445_);
                        v___x_467_ = v_reuseFailAlloc_468_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_461_ == 0 {
                    v___x_463_ = v___x_460_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_464_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
                    v___x_463_ = v_reuseFailAlloc_464_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_463_;
            }
            4 => {
                return v___x_467_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___boxed(
    mut v_handleStderr_470_: *mut crate::leanh::LeanObject,
    mut v_lakeProc_471_: *mut crate::leanh::LeanObject,
    mut v_acc_472_: *mut crate::leanh::LeanObject,
    mut v_a_473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_474_ = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(v_handleStderr_470_, v_lakeProc_471_, v_acc_472_);
    crate::leanh::lean_dec_ref(v_lakeProc_471_);
    return v_res_474_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr(
    mut v_lakePath_475_: *mut crate::leanh::LeanObject,
    mut v_handleStderr_476_: *mut crate::leanh::LeanObject,
    mut v_args_477_: *mut crate::leanh::LeanObject,
    mut v_lakeProc_478_: *mut crate::leanh::LeanObject,
    mut v_acc_479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_481_ = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(v_handleStderr_476_, v_lakeProc_478_, v_acc_479_);
    return v___x_481_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed(
    mut v_lakePath_482_: *mut crate::leanh::LeanObject,
    mut v_handleStderr_483_: *mut crate::leanh::LeanObject,
    mut v_args_484_: *mut crate::leanh::LeanObject,
    mut v_lakeProc_485_: *mut crate::leanh::LeanObject,
    mut v_acc_486_: *mut crate::leanh::LeanObject,
    mut v_a_487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_488_ = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr(v_lakePath_482_, v_handleStderr_483_, v_args_484_, v_lakeProc_485_, v_acc_486_);
    crate::leanh::lean_dec_ref(v_lakeProc_485_);
    crate::leanh::lean_dec_ref(v_args_484_);
    crate::leanh::lean_dec_ref(v_lakePath_482_);
    return v_res_488_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(
    mut v_e_489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_494_: u8 = 0;
    let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_500_: u8 = 0;
    let mut v_a_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_504_: u8 = 0;
    let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_508_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_489_) == 0 {
                    v_a_491_ = crate::leanh::lean_ctor_get(v_e_489_, 0);
                    v_isSharedCheck_500_ = (!crate::leanh::lean_is_exclusive(v_e_489_)) as u8;
                    if v_isSharedCheck_500_ == 0 {
                        v___x_493_ = v_e_489_;
                        v_isShared_494_ = v_isSharedCheck_500_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_491_);
                        crate::leanh::lean_dec(v_e_489_);
                        v___x_493_ = crate::leanh::lean_box(0);
                        v_isShared_494_ = v_isSharedCheck_500_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_501_ = crate::leanh::lean_ctor_get(v_e_489_, 0);
                    v_isSharedCheck_508_ = (!crate::leanh::lean_is_exclusive(v_e_489_)) as u8;
                    if v_isSharedCheck_508_ == 0 {
                        v___x_503_ = v_e_489_;
                        v_isShared_504_ = v_isSharedCheck_508_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_501_);
                        crate::leanh::lean_dec(v_e_489_);
                        v___x_503_ = crate::leanh::lean_box(0);
                        v_isShared_504_ = v_isSharedCheck_508_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_495_ = lean_io_error_to_string(v_a_491_);
                v___x_496_ = lean_mk_io_user_error(v___x_495_);
                if v_isShared_494_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_493_, 1);
                    crate::leanh::lean_ctor_set(v___x_493_, 0, v___x_496_);
                    v___x_498_ = v___x_493_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_499_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_496_);
                    v___x_498_ = v_reuseFailAlloc_499_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_498_;
            }
            3 => {
                if v_isShared_504_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_503_, 0);
                    v___x_506_ = v___x_503_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_507_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
                    v___x_506_ = v_reuseFailAlloc_507_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_506_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg___boxed(
    mut v_e_509_: *mut crate::leanh::LeanObject,
    mut v_a_510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_511_ =
        l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(v_e_509_);
    return v_res_511_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0(
    mut v_00_u03b1_512_: *mut crate::leanh::LeanObject,
    mut v_e_513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_515_ =
        l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(v_e_513_);
    return v___x_515_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___boxed(
    mut v_00_u03b1_516_: *mut crate::leanh::LeanObject,
    mut v_e_517_: *mut crate::leanh::LeanObject,
    mut v_a_518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_519_ = l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0(
        v_00_u03b1_516_,
        v_e_517_,
    );
    return v_res_519_;
}
pub unsafe fn _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_529_ = l_Lean_Server_FileWorker_runLakeSetupFile___closed__3;
    v___x_530_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_531_ = lean_mk_empty_array_with_capacity(v___x_530_);
    v___x_532_ = lean_array_push(v___x_531_, v___x_529_);
    return v___x_532_;
}
pub unsafe fn l_Lean_Server_FileWorker_runLakeSetupFile(
    mut v_m_535_: *mut crate::leanh::LeanObject,
    mut v_lakePath_536_: *mut crate::leanh::LeanObject,
    mut v_filePath_537_: *mut crate::leanh::LeanObject,
    mut v_header_538_: *mut crate::leanh::LeanObject,
    mut v_handleStderr_539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_args_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: u8 = 0;
    let mut v___x_548_: u8 = 0;
    let mut v_spawnArgs_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stdout_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_572_: u8 = 0;
    let mut v_a_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_576_: u8 = 0;
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: u32 = 0;
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_591_: u8 = 0;
    let mut v_a_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_595_: u8 = 0;
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_599_: u8 = 0;
    let mut v_isSharedCheck_600_: u8 = 0;
    let mut v_unused_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_607_: u8 = 0;
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_611_: u8 = 0;
    let mut v_a_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_615_: u8 = 0;
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_619_: u8 = 0;
    let mut v_a_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_623_: u8 = 0;
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_627_: u8 = 0;
    let mut v_a_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_631_: u8 = 0;
    let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_635_: u8 = 0;
    let mut v_a_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_639_: u8 = 0;
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_643_: u8 = 0;
    let mut v_dependencyBuildMode_644_: u8 = 0;
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_dependencyBuildMode_644_ = crate::leanh::lean_ctor_get_uint8(
                    v_m_535_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                );
                v___x_645_ = l_Lean_Server_FileWorker_runLakeSetupFile___closed__4;
                v___x_646_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Server_FileWorker_runLakeSetupFile___closed__5),
                    core::ptr::addr_of_mut!(
                        l_Lean_Server_FileWorker_runLakeSetupFile___closed__5_once
                    ),
                    _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__5,
                );
                v___x_647_ = lean_array_push(v___x_646_, v_filePath_537_);
                v_args_648_ = lean_array_push(v___x_647_, v___x_645_);
                if v_dependencyBuildMode_644_ == 2 {
                    v___x_649_ = l_Lean_Server_FileWorker_runLakeSetupFile___closed__6;
                    v___x_650_ = lean_array_push(v_args_648_, v___x_649_);
                    v___x_651_ = l_Lean_Server_FileWorker_runLakeSetupFile___closed__7;
                    v_args_652_ = lean_array_push(v___x_650_, v___x_651_);
                    v_args_542_ = v_args_652_;
                    state = 1;
                    continue;
                } else {
                    v_args_542_ = v_args_648_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_543_ = l_Lean_Server_FileWorker_runLakeSetupFile___closed__0;
                v___x_544_ = crate::leanh::lean_box(0);
                v___x_545_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_546_ = l_Lean_Server_FileWorker_runLakeSetupFile___closed__1;
                v___x_547_ = 1;
                v___x_548_ = 0;
                crate::leanh::lean_inc_ref(v_args_542_);
                crate::leanh::lean_inc_ref(v_lakePath_536_);
                v_spawnArgs_549_ = crate::leanh::lean_alloc_ctor(0, 5, (2) as u32);
                crate::leanh::lean_ctor_set(v_spawnArgs_549_, 0, v___x_543_);
                crate::leanh::lean_ctor_set(v_spawnArgs_549_, 1, v_lakePath_536_);
                crate::leanh::lean_ctor_set(v_spawnArgs_549_, 2, v_args_542_);
                crate::leanh::lean_ctor_set(v_spawnArgs_549_, 3, v___x_544_);
                crate::leanh::lean_ctor_set(v_spawnArgs_549_, 4, v___x_546_);
                crate::leanh::lean_ctor_set_uint8(
                    v_spawnArgs_549_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___x_547_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_spawnArgs_549_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_548_,
                );
                crate::leanh::lean_inc_ref(v_spawnArgs_549_);
                v___x_550_ = lean_io_process_spawn(v_spawnArgs_549_);
                if crate::leanh::lean_obj_tag(v___x_550_) == 0 {
                    v_a_551_ = crate::leanh::lean_ctor_get(v___x_550_, 0);
                    crate::leanh::lean_inc(v_a_551_);
                    crate::leanh::lean_dec_ref_known(v___x_550_, 1);
                    v___x_552_ = lean_io_process_child_take_stdin(v___x_543_, v_a_551_);
                    if crate::leanh::lean_obj_tag(v___x_552_) == 0 {
                        v_a_553_ = crate::leanh::lean_ctor_get(v___x_552_, 0);
                        crate::leanh::lean_inc(v_a_553_);
                        crate::leanh::lean_dec_ref_known(v___x_552_, 1);
                        v_fst_554_ = crate::leanh::lean_ctor_get(v_a_553_, 0);
                        crate::leanh::lean_inc(v_fst_554_);
                        v_snd_555_ = crate::leanh::lean_ctor_get(v_a_553_, 1);
                        crate::leanh::lean_inc(v_snd_555_);
                        crate::leanh::lean_dec(v_a_553_);
                        v___x_556_ = l_Lean_instToJsonModuleHeader_toJson(v_header_538_);
                        v___x_557_ = l_Lean_Json_compress(v___x_556_);
                        v___x_558_ = l_IO_FS_Handle_putStrLn(v_fst_554_, v___x_557_);
                        crate::leanh::lean_dec(v_fst_554_);
                        if crate::leanh::lean_obj_tag(v___x_558_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_558_, 1);
                            v___x_559_ = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0;
                            crate::leanh::lean_inc(v_snd_555_);
                            v___x_560_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed as *mut core::ffi::c_void, 6, 5);
                            crate::leanh::lean_closure_set(v___x_560_, 0, v_lakePath_536_);
                            crate::leanh::lean_closure_set(v___x_560_, 1, v_handleStderr_539_);
                            crate::leanh::lean_closure_set(v___x_560_, 2, v_args_542_);
                            crate::leanh::lean_closure_set(v___x_560_, 3, v_snd_555_);
                            crate::leanh::lean_closure_set(v___x_560_, 4, v___x_559_);
                            v___x_561_ = l_Lean_Server_ServerTask_IO_asTask___redArg(v___x_560_);
                            v_stdout_562_ = crate::leanh::lean_ctor_get(v_snd_555_, 1);
                            v___x_563_ = l_IO_FS_Handle_readToEnd(v_stdout_562_);
                            if crate::leanh::lean_obj_tag(v___x_563_) == 0 {
                                v_a_564_ = crate::leanh::lean_ctor_get(v___x_563_, 0);
                                crate::leanh::lean_inc(v_a_564_);
                                crate::leanh::lean_dec_ref_known(v___x_563_, 1);
                                v___x_565_ = lean_task_get_own(v___x_561_);
                                v___x_566_ = l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(v___x_565_);
                                if crate::leanh::lean_obj_tag(v___x_566_) == 0 {
                                    v_a_567_ = crate::leanh::lean_ctor_get(v___x_566_, 0);
                                    crate::leanh::lean_inc(v_a_567_);
                                    crate::leanh::lean_dec_ref_known(v___x_566_, 1);
                                    v___x_568_ =
                                        l_Lean_Server_FileWorker_runLakeSetupFile___closed__2;
                                    v___x_569_ = lean_io_process_child_wait(v___x_568_, v_snd_555_);
                                    v_isSharedCheck_600_ =
                                        (!crate::leanh::lean_is_exclusive(v_snd_555_)) as u8;
                                    if v_isSharedCheck_600_ == 0 {
                                        v_unused_601_ = crate::leanh::lean_ctor_get(v_snd_555_, 2);
                                        crate::leanh::lean_dec(v_unused_601_);
                                        v_unused_602_ = crate::leanh::lean_ctor_get(v_snd_555_, 1);
                                        crate::leanh::lean_dec(v_unused_602_);
                                        v_unused_603_ = crate::leanh::lean_ctor_get(v_snd_555_, 0);
                                        crate::leanh::lean_dec(v_unused_603_);
                                        v___x_571_ = v_snd_555_;
                                        v_isShared_572_ = v_isSharedCheck_600_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_snd_555_);
                                        v___x_571_ = crate::leanh::lean_box(0);
                                        v_isShared_572_ = v_isSharedCheck_600_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_564_);
                                    crate::leanh::lean_dec(v_snd_555_);
                                    crate::leanh::lean_dec_ref_known(v_spawnArgs_549_, 5);
                                    v_a_604_ = crate::leanh::lean_ctor_get(v___x_566_, 0);
                                    v_isSharedCheck_611_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_566_)) as u8;
                                    if v_isSharedCheck_611_ == 0 {
                                        v___x_606_ = v___x_566_;
                                        v_isShared_607_ = v_isSharedCheck_611_;
                                        state = 8;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_604_);
                                        crate::leanh::lean_dec(v___x_566_);
                                        v___x_606_ = crate::leanh::lean_box(0);
                                        v_isShared_607_ = v_isSharedCheck_611_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_561_);
                                crate::leanh::lean_dec(v_snd_555_);
                                crate::leanh::lean_dec_ref_known(v_spawnArgs_549_, 5);
                                v_a_612_ = crate::leanh::lean_ctor_get(v___x_563_, 0);
                                v_isSharedCheck_619_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_563_)) as u8;
                                if v_isSharedCheck_619_ == 0 {
                                    v___x_614_ = v___x_563_;
                                    v_isShared_615_ = v_isSharedCheck_619_;
                                    state = 10;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_612_);
                                    crate::leanh::lean_dec(v___x_563_);
                                    v___x_614_ = crate::leanh::lean_box(0);
                                    v_isShared_615_ = v_isSharedCheck_619_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_snd_555_);
                            crate::leanh::lean_dec_ref_known(v_spawnArgs_549_, 5);
                            crate::leanh::lean_dec_ref(v_args_542_);
                            crate::leanh::lean_dec_ref(v_handleStderr_539_);
                            crate::leanh::lean_dec_ref(v_lakePath_536_);
                            v_a_620_ = crate::leanh::lean_ctor_get(v___x_558_, 0);
                            v_isSharedCheck_627_ =
                                (!crate::leanh::lean_is_exclusive(v___x_558_)) as u8;
                            if v_isSharedCheck_627_ == 0 {
                                v___x_622_ = v___x_558_;
                                v_isShared_623_ = v_isSharedCheck_627_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_620_);
                                crate::leanh::lean_dec(v___x_558_);
                                v___x_622_ = crate::leanh::lean_box(0);
                                v_isShared_623_ = v_isSharedCheck_627_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_spawnArgs_549_, 5);
                        crate::leanh::lean_dec_ref(v_args_542_);
                        crate::leanh::lean_dec_ref(v_handleStderr_539_);
                        crate::leanh::lean_dec_ref(v_header_538_);
                        crate::leanh::lean_dec_ref(v_lakePath_536_);
                        v_a_628_ = crate::leanh::lean_ctor_get(v___x_552_, 0);
                        v_isSharedCheck_635_ = (!crate::leanh::lean_is_exclusive(v___x_552_)) as u8;
                        if v_isSharedCheck_635_ == 0 {
                            v___x_630_ = v___x_552_;
                            v_isShared_631_ = v_isSharedCheck_635_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_628_);
                            crate::leanh::lean_dec(v___x_552_);
                            v___x_630_ = crate::leanh::lean_box(0);
                            v_isShared_631_ = v_isSharedCheck_635_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_spawnArgs_549_, 5);
                    crate::leanh::lean_dec_ref(v_args_542_);
                    crate::leanh::lean_dec_ref(v_handleStderr_539_);
                    crate::leanh::lean_dec_ref(v_header_538_);
                    crate::leanh::lean_dec_ref(v_lakePath_536_);
                    v_a_636_ = crate::leanh::lean_ctor_get(v___x_550_, 0);
                    v_isSharedCheck_643_ = (!crate::leanh::lean_is_exclusive(v___x_550_)) as u8;
                    if v_isSharedCheck_643_ == 0 {
                        v___x_638_ = v___x_550_;
                        v_isShared_639_ = v_isSharedCheck_643_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_636_);
                        crate::leanh::lean_dec(v___x_550_);
                        v___x_638_ = crate::leanh::lean_box(0);
                        v_isShared_639_ = v_isSharedCheck_643_;
                        state = 16;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___x_569_) == 0 {
                    v_a_573_ = crate::leanh::lean_ctor_get(v___x_569_, 0);
                    v_isSharedCheck_591_ = (!crate::leanh::lean_is_exclusive(v___x_569_)) as u8;
                    if v_isSharedCheck_591_ == 0 {
                        v___x_575_ = v___x_569_;
                        v_isShared_576_ = v_isSharedCheck_591_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_573_);
                        crate::leanh::lean_dec(v___x_569_);
                        v___x_575_ = crate::leanh::lean_box(0);
                        v_isShared_576_ = v_isSharedCheck_591_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_571_);
                    crate::leanh::lean_dec(v_a_567_);
                    crate::leanh::lean_dec(v_a_564_);
                    crate::leanh::lean_dec_ref_known(v_spawnArgs_549_, 5);
                    v_a_592_ = crate::leanh::lean_ctor_get(v___x_569_, 0);
                    v_isSharedCheck_599_ = (!crate::leanh::lean_is_exclusive(v___x_569_)) as u8;
                    if v_isSharedCheck_599_ == 0 {
                        v___x_594_ = v___x_569_;
                        v_isShared_595_ = v_isSharedCheck_599_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_592_);
                        crate::leanh::lean_dec(v___x_569_);
                        v___x_594_ = crate::leanh::lean_box(0);
                        v_isShared_595_ = v_isSharedCheck_599_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_577_ = lean_string_utf8_byte_size(v_a_564_);
                if v_isShared_572_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_571_, 2, v___x_577_);
                    crate::leanh::lean_ctor_set(v___x_571_, 1, v___x_545_);
                    crate::leanh::lean_ctor_set(v___x_571_, 0, v_a_564_);
                    v___x_579_ = v___x_571_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_590_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_564_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_590_, 1, v___x_545_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_590_, 2, v___x_577_);
                    v___x_579_ = v_reuseFailAlloc_590_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_580_ = l_String_Slice_trimAscii(v___x_579_);
                v_str_581_ = crate::leanh::lean_ctor_get(v___x_580_, 0);
                crate::leanh::lean_inc_ref(v_str_581_);
                v_startInclusive_582_ = crate::leanh::lean_ctor_get(v___x_580_, 1);
                crate::leanh::lean_inc(v_startInclusive_582_);
                v_endExclusive_583_ = crate::leanh::lean_ctor_get(v___x_580_, 2);
                crate::leanh::lean_inc(v_endExclusive_583_);
                crate::leanh::lean_dec_ref(v___x_580_);
                v___x_584_ = lean_string_utf8_extract(
                    v_str_581_,
                    v_startInclusive_582_,
                    v_endExclusive_583_,
                );
                crate::leanh::lean_dec(v_endExclusive_583_);
                crate::leanh::lean_dec(v_startInclusive_582_);
                crate::leanh::lean_dec_ref(v_str_581_);
                v___x_585_ = crate::leanh::lean_alloc_ctor(0, 3, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_585_, 0, v_spawnArgs_549_);
                crate::leanh::lean_ctor_set(v___x_585_, 1, v___x_584_);
                crate::leanh::lean_ctor_set(v___x_585_, 2, v_a_567_);
                v___x_586_ = crate::leanh::lean_unbox_uint32(v_a_573_);
                crate::leanh::lean_dec(v_a_573_);
                crate::leanh::lean_ctor_set_uint32(
                    v___x_585_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_586_,
                );
                if v_isShared_576_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_575_, 0, v___x_585_);
                    v___x_588_ = v___x_575_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_589_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_585_);
                    v___x_588_ = v_reuseFailAlloc_589_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_588_;
            }
            6 => {
                if v_isShared_595_ == 0 {
                    v___x_597_ = v___x_594_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_598_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
                    v___x_597_ = v_reuseFailAlloc_598_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_597_;
            }
            8 => {
                if v_isShared_607_ == 0 {
                    v___x_609_ = v___x_606_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_610_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
                    v___x_609_ = v_reuseFailAlloc_610_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_609_;
            }
            10 => {
                if v_isShared_615_ == 0 {
                    v___x_617_ = v___x_614_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_618_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
                    v___x_617_ = v_reuseFailAlloc_618_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_617_;
            }
            12 => {
                if v_isShared_623_ == 0 {
                    v___x_625_ = v___x_622_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_626_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
                    v___x_625_ = v_reuseFailAlloc_626_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_625_;
            }
            14 => {
                if v_isShared_631_ == 0 {
                    v___x_633_ = v___x_630_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_634_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
                    v___x_633_ = v_reuseFailAlloc_634_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_633_;
            }
            16 => {
                if v_isShared_639_ == 0 {
                    v___x_641_ = v___x_638_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_642_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
                    v___x_641_ = v_reuseFailAlloc_642_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_641_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_runLakeSetupFile___boxed(
    mut v_m_653_: *mut crate::leanh::LeanObject,
    mut v_lakePath_654_: *mut crate::leanh::LeanObject,
    mut v_filePath_655_: *mut crate::leanh::LeanObject,
    mut v_header_656_: *mut crate::leanh::LeanObject,
    mut v_handleStderr_657_: *mut crate::leanh::LeanObject,
    mut v_a_658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_659_ = l_Lean_Server_FileWorker_runLakeSetupFile(
        v_m_653_,
        v_lakePath_654_,
        v_filePath_655_,
        v_header_656_,
        v_handleStderr_657_,
    );
    crate::leanh::lean_dec_ref(v_m_653_);
    return v_res_659_;
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_ctorIdx(
    mut v_x_660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_660_) {
        0 => {
            let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_661_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_661_;
        }
        1 => {
            let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_662_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_662_;
        }
        2 => {
            let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_663_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_663_;
        }
        _ => {
            let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_664_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_664_;
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_ctorIdx___boxed(
    mut v_x_665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_666_ = l_Lean_Server_FileWorker_FileSetupResult_ctorIdx(v_x_665_);
    crate::leanh::lean_dec(v_x_665_);
    return v_res_666_;
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(
    mut v_t_667_: *mut crate::leanh::LeanObject,
    mut v_k_668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_667_) {
        0 => {
            let mut v_setup_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_setup_669_ = crate::leanh::lean_ctor_get(v_t_667_, 0);
            crate::leanh::lean_inc_ref(v_setup_669_);
            crate::leanh::lean_dec_ref_known(v_t_667_, 1);
            v___x_670_ = crate::leanh::lean_apply_1(v_k_668_, v_setup_669_);
            return v___x_670_;
        }
        3 => {
            let mut v_msg_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_msg_671_ = crate::leanh::lean_ctor_get(v_t_667_, 0);
            crate::leanh::lean_inc_ref(v_msg_671_);
            crate::leanh::lean_dec_ref_known(v_t_667_, 1);
            v___x_672_ = crate::leanh::lean_apply_1(v_k_668_, v_msg_671_);
            return v___x_672_;
        }
        _ => {
            crate::leanh::lean_dec(v_t_667_);
            return v_k_668_;
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_ctorElim(
    mut v_motive_673_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_674_: *mut crate::leanh::LeanObject,
    mut v_t_675_: *mut crate::leanh::LeanObject,
    mut v_h_676_: *mut crate::leanh::LeanObject,
    mut v_k_677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_678_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_675_, v_k_677_);
    return v___x_678_;
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_ctorElim___boxed(
    mut v_motive_679_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_680_: *mut crate::leanh::LeanObject,
    mut v_t_681_: *mut crate::leanh::LeanObject,
    mut v_h_682_: *mut crate::leanh::LeanObject,
    mut v_k_683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_684_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim(
        v_motive_679_,
        v_ctorIdx_680_,
        v_t_681_,
        v_h_682_,
        v_k_683_,
    );
    crate::leanh::lean_dec(v_ctorIdx_680_);
    return v_res_684_;
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_success_elim___redArg(
    mut v_t_685_: *mut crate::leanh::LeanObject,
    mut v_success_686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_687_ =
        l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_685_, v_success_686_);
    return v___x_687_;
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_success_elim(
    mut v_motive_688_: *mut crate::leanh::LeanObject,
    mut v_t_689_: *mut crate::leanh::LeanObject,
    mut v_h_690_: *mut crate::leanh::LeanObject,
    mut v_success_691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_692_ =
        l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_689_, v_success_691_);
    return v___x_692_;
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_noLakefile_elim___redArg(
    mut v_t_693_: *mut crate::leanh::LeanObject,
    mut v_noLakefile_694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_695_ =
        l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_693_, v_noLakefile_694_);
    return v___x_695_;
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_noLakefile_elim(
    mut v_motive_696_: *mut crate::leanh::LeanObject,
    mut v_t_697_: *mut crate::leanh::LeanObject,
    mut v_h_698_: *mut crate::leanh::LeanObject,
    mut v_noLakefile_699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_700_ =
        l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_697_, v_noLakefile_699_);
    return v___x_700_;
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_importsOutOfDate_elim___redArg(
    mut v_t_701_: *mut crate::leanh::LeanObject,
    mut v_importsOutOfDate_702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_703_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(
        v_t_701_,
        v_importsOutOfDate_702_,
    );
    return v___x_703_;
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_importsOutOfDate_elim(
    mut v_motive_704_: *mut crate::leanh::LeanObject,
    mut v_t_705_: *mut crate::leanh::LeanObject,
    mut v_h_706_: *mut crate::leanh::LeanObject,
    mut v_importsOutOfDate_707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_708_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(
        v_t_705_,
        v_importsOutOfDate_707_,
    );
    return v___x_708_;
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_error_elim___redArg(
    mut v_t_709_: *mut crate::leanh::LeanObject,
    mut v_error_710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_711_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_709_, v_error_710_);
    return v___x_711_;
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_error_elim(
    mut v_motive_712_: *mut crate::leanh::LeanObject,
    mut v_t_713_: *mut crate::leanh::LeanObject,
    mut v_h_714_: *mut crate::leanh::LeanObject,
    mut v_error_715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_716_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_713_, v_error_715_);
    return v___x_716_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(
    mut v_as_717_: *mut crate::leanh::LeanObject,
    mut v_i_718_: usize,
    mut v_stop_719_: usize,
    mut v_b_720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_722_: u8 = 0;
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: usize = 0;
    let mut v___x_727_: usize = 0;
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_722_ = lean_usize_dec_eq(v_i_718_, v_stop_719_);
                if v___x_722_ == 0 {
                    v___x_723_ = lean_array_uget_borrowed(v_as_717_, v_i_718_);
                    crate::leanh::lean_inc(v___x_723_);
                    v___x_724_ = lean_load_dynlib(v___x_723_);
                    if crate::leanh::lean_obj_tag(v___x_724_) == 0 {
                        v_a_725_ = crate::leanh::lean_ctor_get(v___x_724_, 0);
                        crate::leanh::lean_inc(v_a_725_);
                        crate::leanh::lean_dec_ref_known(v___x_724_, 1);
                        v___x_726_ = 1usize;
                        v___x_727_ = lean_usize_add(v_i_718_, v___x_726_);
                        v_i_718_ = v___x_727_;
                        v_b_720_ = v_a_725_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_724_;
                    }
                } else {
                    v___x_729_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_729_, 0, v_b_720_);
                    return v___x_729_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0___boxed(
    mut v_as_730_: *mut crate::leanh::LeanObject,
    mut v_i_731_: *mut crate::leanh::LeanObject,
    mut v_stop_732_: *mut crate::leanh::LeanObject,
    mut v_b_733_: *mut crate::leanh::LeanObject,
    mut v___y_734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_735_: usize = 0;
    let mut v_stop_boxed_736_: usize = 0;
    let mut v_res_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_735_ = crate::leanh::lean_unbox_usize(v_i_731_);
    crate::leanh::lean_dec(v_i_731_);
    v_stop_boxed_736_ = crate::leanh::lean_unbox_usize(v_stop_732_);
    crate::leanh::lean_dec(v_stop_732_);
    v_res_737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(v_as_730_, v_i_boxed_735_, v_stop_boxed_736_, v_b_733_);
    crate::leanh::lean_dec_ref(v_as_730_);
    return v_res_737_;
}
pub unsafe fn l_Lean_Server_FileWorker_setupFile(
    mut v_m_744_: *mut crate::leanh::LeanObject,
    mut v_header_745_: *mut crate::leanh::LeanObject,
    mut v_handleStderr_746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_uri_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_753_: u8 = 0;
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_758_: u8 = 0;
    let mut v___x_759_: u8 = 0;
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_768_: u8 = 0;
    let mut v_spawnArgs_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exitCode_770_: u32 = 0;
    let mut v_stdout_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stderr_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmd_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: u32 = 0;
    let mut v___x_795_: u8 = 0;
    let mut v___x_796_: u32 = 0;
    let mut v___x_797_: u8 = 0;
    let mut v___x_798_: u32 = 0;
    let mut v___x_799_: u8 = 0;
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_826_: u8 = 0;
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_839_: u8 = 0;
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_843_: u8 = 0;
    let mut v_dynlibs_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: u8 = 0;
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: u8 = 0;
    let mut v___x_850_: usize = 0;
    let mut v___x_851_: usize = 0;
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: usize = 0;
    let mut v___x_854_: usize = 0;
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_856_: u8 = 0;
    let mut v_isSharedCheck_857_: u8 = 0;
    let mut v_a_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_861_: u8 = 0;
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_865_: u8 = 0;
    let mut v_isSharedCheck_866_: u8 = 0;
    let mut v_a_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_870_: u8 = 0;
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_874_: u8 = 0;
    let mut v_isSharedCheck_875_: u8 = 0;
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_uri_748_ = crate::leanh::lean_ctor_get(v_m_744_, 0);
                v___x_749_ = l_System_Uri_fileUriToPath_x3f(v_uri_748_);
                if crate::leanh::lean_obj_tag(v___x_749_) == 1 {
                    v_val_750_ = crate::leanh::lean_ctor_get(v___x_749_, 0);
                    v_isSharedCheck_875_ = (!crate::leanh::lean_is_exclusive(v___x_749_)) as u8;
                    if v_isSharedCheck_875_ == 0 {
                        v___x_752_ = v___x_749_;
                        v_isShared_753_ = v_isSharedCheck_875_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_750_);
                        crate::leanh::lean_dec(v___x_749_);
                        v___x_752_ = crate::leanh::lean_box(0);
                        v_isShared_753_ = v_isSharedCheck_875_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_749_);
                    crate::leanh::lean_dec_ref(v_handleStderr_746_);
                    crate::leanh::lean_dec_ref(v_header_745_);
                    v___x_876_ = crate::leanh::lean_box(1);
                    v___x_877_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_877_, 0, v___x_876_);
                    return v___x_877_;
                }
            }
            1 => {
                v___x_754_ = l_Lean_determineLakePath();
                if crate::leanh::lean_obj_tag(v___x_754_) == 0 {
                    v_a_755_ = crate::leanh::lean_ctor_get(v___x_754_, 0);
                    v_isSharedCheck_866_ = (!crate::leanh::lean_is_exclusive(v___x_754_)) as u8;
                    if v_isSharedCheck_866_ == 0 {
                        v___x_757_ = v___x_754_;
                        v_isShared_758_ = v_isSharedCheck_866_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_755_);
                        crate::leanh::lean_dec(v___x_754_);
                        v___x_757_ = crate::leanh::lean_box(0);
                        v_isShared_758_ = v_isSharedCheck_866_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_752_);
                    crate::leanh::lean_dec(v_val_750_);
                    crate::leanh::lean_dec_ref(v_handleStderr_746_);
                    crate::leanh::lean_dec_ref(v_header_745_);
                    v_a_867_ = crate::leanh::lean_ctor_get(v___x_754_, 0);
                    v_isSharedCheck_874_ = (!crate::leanh::lean_is_exclusive(v___x_754_)) as u8;
                    if v_isSharedCheck_874_ == 0 {
                        v___x_869_ = v___x_754_;
                        v_isShared_870_ = v_isSharedCheck_874_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_867_);
                        crate::leanh::lean_dec(v___x_754_);
                        v___x_869_ = crate::leanh::lean_box(0);
                        v_isShared_870_ = v_isSharedCheck_874_;
                        state = 20;
                        continue;
                    }
                }
            }
            2 => {
                v___x_759_ = l_System_FilePath_pathExists(v_a_755_);
                if v___x_759_ == 0 {
                    crate::leanh::lean_dec(v_a_755_);
                    crate::leanh::lean_del_object(v___x_752_);
                    crate::leanh::lean_dec(v_val_750_);
                    crate::leanh::lean_dec_ref(v_handleStderr_746_);
                    crate::leanh::lean_dec_ref(v_header_745_);
                    v___x_760_ = crate::leanh::lean_box(1);
                    if v_isShared_758_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_757_, 0, v___x_760_);
                        v___x_762_ = v___x_757_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_763_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
                        v___x_762_ = v_reuseFailAlloc_763_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_764_ = l_Lean_Server_FileWorker_runLakeSetupFile(
                        v_m_744_,
                        v_a_755_,
                        v_val_750_,
                        v_header_745_,
                        v_handleStderr_746_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_764_) == 0 {
                        v_a_765_ = crate::leanh::lean_ctor_get(v___x_764_, 0);
                        v_isSharedCheck_857_ = (!crate::leanh::lean_is_exclusive(v___x_764_)) as u8;
                        if v_isSharedCheck_857_ == 0 {
                            v___x_767_ = v___x_764_;
                            v_isShared_768_ = v_isSharedCheck_857_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_765_);
                            crate::leanh::lean_dec(v___x_764_);
                            v___x_767_ = crate::leanh::lean_box(0);
                            v_isShared_768_ = v_isSharedCheck_857_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_757_);
                        crate::leanh::lean_del_object(v___x_752_);
                        v_a_858_ = crate::leanh::lean_ctor_get(v___x_764_, 0);
                        v_isSharedCheck_865_ = (!crate::leanh::lean_is_exclusive(v___x_764_)) as u8;
                        if v_isSharedCheck_865_ == 0 {
                            v___x_860_ = v___x_764_;
                            v_isShared_861_ = v_isSharedCheck_865_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_858_);
                            crate::leanh::lean_dec(v___x_764_);
                            v___x_860_ = crate::leanh::lean_box(0);
                            v_isShared_861_ = v_isSharedCheck_865_;
                            state = 18;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_762_;
            }
            4 => {
                v_spawnArgs_769_ = crate::leanh::lean_ctor_get(v_a_765_, 0);
                crate::leanh::lean_inc_ref(v_spawnArgs_769_);
                v_exitCode_770_ = crate::leanh::lean_ctor_get_uint32(
                    v_a_765_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_stdout_771_ = crate::leanh::lean_ctor_get(v_a_765_, 1);
                crate::leanh::lean_inc_ref(v_stdout_771_);
                v_stderr_772_ = crate::leanh::lean_ctor_get(v_a_765_, 2);
                crate::leanh::lean_inc_ref(v_stderr_772_);
                crate::leanh::lean_dec(v_a_765_);
                v_cmd_773_ = crate::leanh::lean_ctor_get(v_spawnArgs_769_, 1);
                crate::leanh::lean_inc_ref(v_cmd_773_);
                v_args_774_ = crate::leanh::lean_ctor_get(v_spawnArgs_769_, 2);
                crate::leanh::lean_inc_ref(v_args_774_);
                crate::leanh::lean_dec_ref(v_spawnArgs_769_);
                v___x_775_ = l_Lean_Server_FileWorker_setupFile___closed__0;
                v___x_776_ = lean_array_to_list(v_args_774_);
                v___x_777_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_777_, 0, v_cmd_773_);
                crate::leanh::lean_ctor_set(v___x_777_, 1, v___x_776_);
                v___x_778_ = l_String_intercalate(v___x_775_, v___x_777_);
                v___x_794_ = 0;
                v___x_795_ = lean_uint32_dec_eq(v_exitCode_770_, v___x_794_);
                if v___x_795_ == 0 {
                    crate::leanh::lean_del_object(v___x_767_);
                    crate::leanh::lean_del_object(v___x_752_);
                    v___x_796_ = 2;
                    v___x_797_ = lean_uint32_dec_eq(v_exitCode_770_, v___x_796_);
                    if v___x_797_ == 0 {
                        v___x_798_ = 3;
                        v___x_799_ = lean_uint32_dec_eq(v_exitCode_770_, v___x_798_);
                        if v___x_799_ == 0 {
                            v___x_800_ = l_Lean_Server_FileWorker_setupFile___closed__4;
                            v___x_801_ = lean_string_append(v___x_800_, v___x_778_);
                            crate::leanh::lean_dec_ref(v___x_778_);
                            v___x_802_ = l_Lean_Server_FileWorker_setupFile___closed__5;
                            v___x_803_ = lean_string_append(v___x_801_, v___x_802_);
                            v___x_804_ = lean_string_append(v___x_803_, v_stdout_771_);
                            crate::leanh::lean_dec_ref(v_stdout_771_);
                            v___x_805_ = l_Lean_Server_FileWorker_setupFile___closed__3;
                            v___x_806_ = lean_string_append(v___x_804_, v___x_805_);
                            v___x_807_ = lean_string_append(v___x_806_, v_stderr_772_);
                            crate::leanh::lean_dec_ref(v_stderr_772_);
                            v___x_808_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_808_, 0, v___x_807_);
                            if v_isShared_758_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_757_, 0, v___x_808_);
                                v___x_810_ = v___x_757_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_811_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
                                v___x_810_ = v_reuseFailAlloc_811_;
                                state = 8;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_778_);
                            crate::leanh::lean_dec_ref(v_stderr_772_);
                            crate::leanh::lean_dec_ref(v_stdout_771_);
                            v___x_812_ = crate::leanh::lean_box(2);
                            if v_isShared_758_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_757_, 0, v___x_812_);
                                v___x_814_ = v___x_757_;
                                state = 9;
                                continue;
                            } else {
                                v_reuseFailAlloc_815_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_812_);
                                v___x_814_ = v_reuseFailAlloc_815_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_778_);
                        crate::leanh::lean_dec_ref(v_stderr_772_);
                        crate::leanh::lean_dec_ref(v_stdout_771_);
                        v___x_816_ = crate::leanh::lean_box(1);
                        if v_isShared_758_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_757_, 0, v___x_816_);
                            v___x_818_ = v___x_757_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_819_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
                            v___x_818_ = v_reuseFailAlloc_819_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_stdout_771_);
                    v___x_820_ = l_Lean_Json_parse(v_stdout_771_);
                    if crate::leanh::lean_obj_tag(v___x_820_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_820_, 1);
                        crate::leanh::lean_del_object(v___x_757_);
                        state = 5;
                        continue;
                    } else {
                        v_a_821_ = crate::leanh::lean_ctor_get(v___x_820_, 0);
                        crate::leanh::lean_inc(v_a_821_);
                        crate::leanh::lean_dec_ref_known(v___x_820_, 1);
                        v___x_822_ = l_Lean_instFromJsonModuleSetup_fromJson(v_a_821_);
                        if crate::leanh::lean_obj_tag(v___x_822_) == 1 {
                            crate::leanh::lean_dec_ref(v___x_778_);
                            crate::leanh::lean_dec_ref(v_stderr_772_);
                            crate::leanh::lean_dec_ref(v_stdout_771_);
                            crate::leanh::lean_del_object(v___x_767_);
                            crate::leanh::lean_del_object(v___x_752_);
                            v_a_823_ = crate::leanh::lean_ctor_get(v___x_822_, 0);
                            v_isSharedCheck_856_ =
                                (!crate::leanh::lean_is_exclusive(v___x_822_)) as u8;
                            if v_isSharedCheck_856_ == 0 {
                                v___x_825_ = v___x_822_;
                                v_isShared_826_ = v_isSharedCheck_856_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_823_);
                                crate::leanh::lean_dec(v___x_822_);
                                v___x_825_ = crate::leanh::lean_box(0);
                                v_isShared_826_ = v_isSharedCheck_856_;
                                state = 11;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_822_);
                            crate::leanh::lean_del_object(v___x_757_);
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            5 => {
                v___x_780_ = l_Lean_Server_FileWorker_setupFile___closed__1;
                v___x_781_ = lean_string_append(v___x_780_, v___x_778_);
                crate::leanh::lean_dec_ref(v___x_778_);
                v___x_782_ = l_Lean_Server_FileWorker_setupFile___closed__2;
                v___x_783_ = lean_string_append(v___x_781_, v___x_782_);
                v___x_784_ = lean_string_append(v___x_783_, v_stdout_771_);
                crate::leanh::lean_dec_ref(v_stdout_771_);
                v___x_785_ = l_Lean_Server_FileWorker_setupFile___closed__3;
                v___x_786_ = lean_string_append(v___x_784_, v___x_785_);
                v___x_787_ = lean_string_append(v___x_786_, v_stderr_772_);
                crate::leanh::lean_dec_ref(v_stderr_772_);
                if v_isShared_753_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_752_, 3);
                    crate::leanh::lean_ctor_set(v___x_752_, 0, v___x_787_);
                    v___x_789_ = v___x_752_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_793_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_787_);
                    v___x_789_ = v_reuseFailAlloc_793_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_768_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_767_, 0, v___x_789_);
                    v___x_791_ = v___x_767_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_792_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_789_);
                    v___x_791_ = v_reuseFailAlloc_792_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_791_;
            }
            8 => {
                return v___x_810_;
            }
            9 => {
                return v___x_814_;
            }
            10 => {
                return v___x_818_;
            }
            11 => {
                v_dynlibs_844_ = crate::leanh::lean_ctor_get(v_a_823_, 4);
                v___x_845_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_846_ = lean_array_get_size(v_dynlibs_844_);
                v___x_847_ = lean_nat_dec_lt(v___x_845_, v___x_846_);
                if v___x_847_ == 0 {
                    state = 12;
                    continue;
                } else {
                    v___x_848_ = crate::leanh::lean_box(0);
                    v___x_849_ = lean_nat_dec_le(v___x_846_, v___x_846_);
                    if v___x_849_ == 0 {
                        if v___x_847_ == 0 {
                            state = 12;
                            continue;
                        } else {
                            v___x_850_ = 0usize;
                            v___x_851_ = lean_usize_of_nat(v___x_846_);
                            v___x_852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(v_dynlibs_844_, v___x_850_, v___x_851_, v___x_848_);
                            v___y_835_ = v___x_852_;
                            state = 15;
                            continue;
                        }
                    } else {
                        v___x_853_ = 0usize;
                        v___x_854_ = lean_usize_of_nat(v___x_846_);
                        v___x_855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(v_dynlibs_844_, v___x_853_, v___x_854_, v___x_848_);
                        v___y_835_ = v___x_855_;
                        state = 15;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_826_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_825_, 0);
                    v___x_829_ = v___x_825_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_833_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_823_);
                    v___x_829_ = v_reuseFailAlloc_833_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_758_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_757_, 0, v___x_829_);
                    v___x_831_ = v___x_757_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_832_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_829_);
                    v___x_831_ = v_reuseFailAlloc_832_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_831_;
            }
            15 => {
                if crate::leanh::lean_obj_tag(v___y_835_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_835_, 1);
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_825_);
                    crate::leanh::lean_dec(v_a_823_);
                    crate::leanh::lean_del_object(v___x_757_);
                    v_a_836_ = crate::leanh::lean_ctor_get(v___y_835_, 0);
                    v_isSharedCheck_843_ = (!crate::leanh::lean_is_exclusive(v___y_835_)) as u8;
                    if v_isSharedCheck_843_ == 0 {
                        v___x_838_ = v___y_835_;
                        v_isShared_839_ = v_isSharedCheck_843_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_836_);
                        crate::leanh::lean_dec(v___y_835_);
                        v___x_838_ = crate::leanh::lean_box(0);
                        v_isShared_839_ = v_isSharedCheck_843_;
                        state = 16;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_839_ == 0 {
                    v___x_841_ = v___x_838_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_842_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
                    v___x_841_ = v_reuseFailAlloc_842_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_841_;
            }
            18 => {
                if v_isShared_861_ == 0 {
                    v___x_863_ = v___x_860_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_864_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
                    v___x_863_ = v_reuseFailAlloc_864_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_863_;
            }
            20 => {
                if v_isShared_870_ == 0 {
                    v___x_872_ = v___x_869_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_873_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
                    v___x_872_ = v_reuseFailAlloc_873_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_872_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_setupFile___boxed(
    mut v_m_878_: *mut crate::leanh::LeanObject,
    mut v_header_879_: *mut crate::leanh::LeanObject,
    mut v_handleStderr_880_: *mut crate::leanh::LeanObject,
    mut v_a_881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_882_ = l_Lean_Server_FileWorker_setupFile(v_m_878_, v_header_879_, v_handleStderr_880_);
    crate::leanh::lean_dec_ref(v_m_878_);
    return v_res_882_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_FileWorker_SetupFile(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_Utils(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_LakePath(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_ServerTask(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_FileWorker_SetupFile(
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
pub unsafe fn initialize_Lean_Server_FileWorker_SetupFile(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_Utils(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_LakePath(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Server_ServerTask(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_FileWorker_SetupFile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_FileWorker_SetupFile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Server_FileWorker_SetupFile(builtin);
}

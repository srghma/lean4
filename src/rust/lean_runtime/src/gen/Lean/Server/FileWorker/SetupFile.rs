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
use crate::lean_imports_rs::Init::Core::lean_task_get_own;
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_utf8_extract;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_dec_le, lean_nat_dec_lt, lean_string_dec_eq, lean_string_utf8_byte_size,
    lean_uint32_dec_eq, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::{
    lean_io_prim_handle_get_line, lean_io_process_child_take_stdin, lean_io_process_child_wait,
    lean_io_process_spawn,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint32, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_ctor_set_uint32, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once,
    lean_obj_tag, lean_unbox_uint32, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Server_FileWorker_runLakeSetupFile___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [0 as *mut LeanObject],
    };
static mut l_Lean_Server_FileWorker_runLakeSetupFile___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_runLakeSetupFile___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Server_FileWorker_runLakeSetupFile___closed__1_value: LeanArrayObject<0> =
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
static mut l_Lean_Server_FileWorker_runLakeSetupFile___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_runLakeSetupFile___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Server_FileWorker_runLakeSetupFile___closed__2_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [2 as *mut LeanObject],
    };
static mut l_Lean_Server_FileWorker_runLakeSetupFile___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_runLakeSetupFile___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Server_FileWorker_runLakeSetupFile___closed__3_value: LeanStringObject<11> =
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
        m_data: [115, 101, 116, 117, 112, 45, 102, 105, 108, 101, 0],
    };
static mut l_Lean_Server_FileWorker_runLakeSetupFile___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_runLakeSetupFile___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Server_FileWorker_runLakeSetupFile___closed__4_value: LeanStringObject<2> =
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
        m_data: [45, 0],
    };
static mut l_Lean_Server_FileWorker_runLakeSetupFile___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_runLakeSetupFile___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Server_FileWorker_runLakeSetupFile___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Server_FileWorker_runLakeSetupFile___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_FileWorker_runLakeSetupFile___closed__6_value: LeanStringObject<11> =
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
        m_data: [45, 45, 110, 111, 45, 98, 117, 105, 108, 100, 0],
    };
static mut l_Lean_Server_FileWorker_runLakeSetupFile___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_runLakeSetupFile___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Server_FileWorker_runLakeSetupFile___closed__7_value: LeanStringObject<11> =
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
        m_data: [45, 45, 110, 111, 45, 99, 97, 99, 104, 101, 0],
    };
static mut l_Lean_Server_FileWorker_runLakeSetupFile___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_runLakeSetupFile___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Server_FileWorker_setupFile___closed__0_value: LeanStringObject<2> =
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
        m_data: [32, 0],
    };
static mut l_Lean_Server_FileWorker_setupFile___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_setupFile___closed__0_value) as *mut LeanObject;
pub static l_Lean_Server_FileWorker_setupFile___closed__1_value: LeanStringObject<22> =
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
            73, 110, 118, 97, 108, 105, 100, 32, 111, 117, 116, 112, 117, 116, 32, 102, 114, 111,
            109, 32, 96, 0,
        ],
    };
static mut l_Lean_Server_FileWorker_setupFile___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_setupFile___closed__1_value) as *mut LeanObject;
pub static l_Lean_Server_FileWorker_setupFile___closed__2_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Server_FileWorker_setupFile___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_setupFile___closed__2_value) as *mut LeanObject;
pub static l_Lean_Server_FileWorker_setupFile___closed__3_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Server_FileWorker_setupFile___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_setupFile___closed__3_value) as *mut LeanObject;
pub static l_Lean_Server_FileWorker_setupFile___closed__4_value: LeanStringObject<2> =
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
        m_data: [96, 0],
    };
static mut l_Lean_Server_FileWorker_setupFile___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_setupFile___closed__4_value) as *mut LeanObject;
pub static l_Lean_Server_FileWorker_setupFile___closed__5_value: LeanStringObject<11> =
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
        m_data: [96, 32, 102, 97, 105, 108, 101, 100, 58, 10, 0],
    };
static mut l_Lean_Server_FileWorker_setupFile___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Server_FileWorker_setupFile___closed__5_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(
    mut v_handleStderr_443_: *mut LeanObject,
    mut v_lakeProc_444_: *mut LeanObject,
    mut v_acc_445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stderr_447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_452_: u8 = 0;
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_454_: u8 = 0;
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_461_: u8 = 0;
    let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_465_: u8 = 0;
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_469_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stderr_447_ = lean_ctor_get(v_lakeProc_444_, 2);
                v___x_448_ = lean_io_prim_handle_get_line(v_stderr_447_);
                if lean_obj_tag(v___x_448_) == 0 {
                    v_a_449_ = lean_ctor_get(v___x_448_, 0);
                    v_isSharedCheck_469_ = (!lean_is_exclusive(v___x_448_)) as u8;
                    if v_isSharedCheck_469_ == 0 {
                        v___x_451_ = v___x_448_;
                        v_isShared_452_ = v_isSharedCheck_469_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_449_);
                        lean_dec(v___x_448_);
                        v___x_451_ = lean_box(0);
                        v_isShared_452_ = v_isSharedCheck_469_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_acc_445_);
                    lean_dec_ref(v_handleStderr_443_);
                    return v___x_448_;
                }
            }
            1 => {
                v___x_453_ = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0;
                v___x_454_ = lean_string_dec_eq(v_a_449_, v___x_453_);
                if v___x_454_ == 0 {
                    lean_del_object(v___x_451_);
                    lean_inc_ref(v_handleStderr_443_);
                    lean_inc(v_a_449_);
                    v___x_455_ = lean_apply_2(v_handleStderr_443_, v_a_449_, lean_box(0));
                    if lean_obj_tag(v___x_455_) == 0 {
                        lean_dec_ref_known(v___x_455_, 1);
                        v___x_456_ = lean_string_append(v_acc_445_, v_a_449_);
                        lean_dec(v_a_449_);
                        v_acc_445_ = v___x_456_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_a_449_);
                        lean_dec_ref(v_acc_445_);
                        lean_dec_ref(v_handleStderr_443_);
                        v_a_458_ = lean_ctor_get(v___x_455_, 0);
                        v_isSharedCheck_465_ = (!lean_is_exclusive(v___x_455_)) as u8;
                        if v_isSharedCheck_465_ == 0 {
                            v___x_460_ = v___x_455_;
                            v_isShared_461_ = v_isSharedCheck_465_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_458_);
                            lean_dec(v___x_455_);
                            v___x_460_ = lean_box(0);
                            v_isShared_461_ = v_isSharedCheck_465_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_449_);
                    lean_dec_ref(v_handleStderr_443_);
                    if v_isShared_452_ == 0 {
                        lean_ctor_set(v___x_451_, 0, v_acc_445_);
                        v___x_467_ = v___x_451_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_468_, 0, v_acc_445_);
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
                    v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
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
    mut v_handleStderr_470_: *mut LeanObject,
    mut v_lakeProc_471_: *mut LeanObject,
    mut v_acc_472_: *mut LeanObject,
    mut v_a_473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_474_: *mut LeanObject = core::ptr::null_mut();
    v_res_474_ = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(v_handleStderr_470_, v_lakeProc_471_, v_acc_472_);
    lean_dec_ref(v_lakeProc_471_);
    return v_res_474_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr(
    mut v_lakePath_475_: *mut LeanObject,
    mut v_handleStderr_476_: *mut LeanObject,
    mut v_args_477_: *mut LeanObject,
    mut v_lakeProc_478_: *mut LeanObject,
    mut v_acc_479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    v___x_481_ = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(v_handleStderr_476_, v_lakeProc_478_, v_acc_479_);
    return v___x_481_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed(
    mut v_lakePath_482_: *mut LeanObject,
    mut v_handleStderr_483_: *mut LeanObject,
    mut v_args_484_: *mut LeanObject,
    mut v_lakeProc_485_: *mut LeanObject,
    mut v_acc_486_: *mut LeanObject,
    mut v_a_487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_488_: *mut LeanObject = core::ptr::null_mut();
    v_res_488_ = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr(v_lakePath_482_, v_handleStderr_483_, v_args_484_, v_lakeProc_485_, v_acc_486_);
    lean_dec_ref(v_lakeProc_485_);
    lean_dec_ref(v_args_484_);
    lean_dec_ref(v_lakePath_482_);
    return v_res_488_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(
    mut v_e_489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_494_: u8 = 0;
    let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_500_: u8 = 0;
    let mut v_a_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_504_: u8 = 0;
    let mut v___x_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_508_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_489_) == 0 {
                    v_a_491_ = lean_ctor_get(v_e_489_, 0);
                    v_isSharedCheck_500_ = (!lean_is_exclusive(v_e_489_)) as u8;
                    if v_isSharedCheck_500_ == 0 {
                        v___x_493_ = v_e_489_;
                        v_isShared_494_ = v_isSharedCheck_500_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_491_);
                        lean_dec(v_e_489_);
                        v___x_493_ = lean_box(0);
                        v_isShared_494_ = v_isSharedCheck_500_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_501_ = lean_ctor_get(v_e_489_, 0);
                    v_isSharedCheck_508_ = (!lean_is_exclusive(v_e_489_)) as u8;
                    if v_isSharedCheck_508_ == 0 {
                        v___x_503_ = v_e_489_;
                        v_isShared_504_ = v_isSharedCheck_508_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_501_);
                        lean_dec(v_e_489_);
                        v___x_503_ = lean_box(0);
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
                    lean_ctor_set_tag(v___x_493_, 1);
                    lean_ctor_set(v___x_493_, 0, v___x_496_);
                    v___x_498_ = v___x_493_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_496_);
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
                    lean_ctor_set_tag(v___x_503_, 0);
                    v___x_506_ = v___x_503_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
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
    mut v_e_509_: *mut LeanObject,
    mut v_a_510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_511_: *mut LeanObject = core::ptr::null_mut();
    v_res_511_ =
        l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(v_e_509_);
    return v_res_511_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0(
    mut v_00_u03b1_512_: *mut LeanObject,
    mut v_e_513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
    v___x_515_ =
        l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(v_e_513_);
    return v___x_515_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___boxed(
    mut v_00_u03b1_516_: *mut LeanObject,
    mut v_e_517_: *mut LeanObject,
    mut v_a_518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_519_: *mut LeanObject = core::ptr::null_mut();
    v_res_519_ = l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0(
        v_00_u03b1_516_,
        v_e_517_,
    );
    return v_res_519_;
}
pub unsafe fn _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__5() -> *mut LeanObject {
    let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
    v___x_529_ = l_Lean_Server_FileWorker_runLakeSetupFile___closed__3;
    v___x_530_ = lean_unsigned_to_nat(3);
    v___x_531_ = lean_mk_empty_array_with_capacity(v___x_530_);
    v___x_532_ = lean_array_push(v___x_531_, v___x_529_);
    return v___x_532_;
}
pub unsafe fn l_Lean_Server_FileWorker_runLakeSetupFile(
    mut v_m_535_: *mut LeanObject,
    mut v_lakePath_536_: *mut LeanObject,
    mut v_filePath_537_: *mut LeanObject,
    mut v_header_538_: *mut LeanObject,
    mut v_handleStderr_539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_args_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_547_: u8 = 0;
    let mut v___x_548_: u8 = 0;
    let mut v_spawnArgs_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stdout_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_572_: u8 = 0;
    let mut v_a_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_576_: u8 = 0;
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: u32 = 0;
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_591_: u8 = 0;
    let mut v_a_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_595_: u8 = 0;
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_599_: u8 = 0;
    let mut v_isSharedCheck_600_: u8 = 0;
    let mut v_unused_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_607_: u8 = 0;
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_611_: u8 = 0;
    let mut v_a_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_615_: u8 = 0;
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_619_: u8 = 0;
    let mut v_a_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_623_: u8 = 0;
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_627_: u8 = 0;
    let mut v_a_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_631_: u8 = 0;
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_635_: u8 = 0;
    let mut v_a_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_639_: u8 = 0;
    let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_643_: u8 = 0;
    let mut v_dependencyBuildMode_644_: u8 = 0;
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_652_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_dependencyBuildMode_644_ = lean_ctor_get_uint8(
                    v_m_535_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                );
                v___x_645_ = l_Lean_Server_FileWorker_runLakeSetupFile___closed__4;
                v___x_646_ = lean_obj_once(
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
                v___x_544_ = lean_box(0);
                v___x_545_ = lean_unsigned_to_nat(0);
                v___x_546_ = l_Lean_Server_FileWorker_runLakeSetupFile___closed__1;
                v___x_547_ = 1;
                v___x_548_ = 0;
                lean_inc_ref(v_args_542_);
                lean_inc_ref(v_lakePath_536_);
                v_spawnArgs_549_ = lean_alloc_ctor(0, 5, (2) as u32);
                lean_ctor_set(v_spawnArgs_549_, 0, v___x_543_);
                lean_ctor_set(v_spawnArgs_549_, 1, v_lakePath_536_);
                lean_ctor_set(v_spawnArgs_549_, 2, v_args_542_);
                lean_ctor_set(v_spawnArgs_549_, 3, v___x_544_);
                lean_ctor_set(v_spawnArgs_549_, 4, v___x_546_);
                lean_ctor_set_uint8(
                    v_spawnArgs_549_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___x_547_,
                );
                lean_ctor_set_uint8(
                    v_spawnArgs_549_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___x_548_,
                );
                lean_inc_ref(v_spawnArgs_549_);
                v___x_550_ = lean_io_process_spawn(v_spawnArgs_549_);
                if lean_obj_tag(v___x_550_) == 0 {
                    v_a_551_ = lean_ctor_get(v___x_550_, 0);
                    lean_inc(v_a_551_);
                    lean_dec_ref_known(v___x_550_, 1);
                    v___x_552_ = lean_io_process_child_take_stdin(v___x_543_, v_a_551_);
                    if lean_obj_tag(v___x_552_) == 0 {
                        v_a_553_ = lean_ctor_get(v___x_552_, 0);
                        lean_inc(v_a_553_);
                        lean_dec_ref_known(v___x_552_, 1);
                        v_fst_554_ = lean_ctor_get(v_a_553_, 0);
                        lean_inc(v_fst_554_);
                        v_snd_555_ = lean_ctor_get(v_a_553_, 1);
                        lean_inc(v_snd_555_);
                        lean_dec(v_a_553_);
                        v___x_556_ = l_Lean_instToJsonModuleHeader_toJson(v_header_538_);
                        v___x_557_ = l_Lean_Json_compress(v___x_556_);
                        v___x_558_ = l_IO_FS_Handle_putStrLn(v_fst_554_, v___x_557_);
                        lean_dec(v_fst_554_);
                        if lean_obj_tag(v___x_558_) == 0 {
                            lean_dec_ref_known(v___x_558_, 1);
                            v___x_559_ = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0;
                            lean_inc(v_snd_555_);
                            v___x_560_ = lean_alloc_closure(l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed as *mut core::ffi::c_void, 6, 5);
                            lean_closure_set(v___x_560_, 0, v_lakePath_536_);
                            lean_closure_set(v___x_560_, 1, v_handleStderr_539_);
                            lean_closure_set(v___x_560_, 2, v_args_542_);
                            lean_closure_set(v___x_560_, 3, v_snd_555_);
                            lean_closure_set(v___x_560_, 4, v___x_559_);
                            v___x_561_ = l_Lean_Server_ServerTask_IO_asTask___redArg(v___x_560_);
                            v_stdout_562_ = lean_ctor_get(v_snd_555_, 1);
                            v___x_563_ = l_IO_FS_Handle_readToEnd(v_stdout_562_);
                            if lean_obj_tag(v___x_563_) == 0 {
                                v_a_564_ = lean_ctor_get(v___x_563_, 0);
                                lean_inc(v_a_564_);
                                lean_dec_ref_known(v___x_563_, 1);
                                v___x_565_ = lean_task_get_own(v___x_561_);
                                v___x_566_ = l_IO_ofExcept___at___00Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(v___x_565_);
                                if lean_obj_tag(v___x_566_) == 0 {
                                    v_a_567_ = lean_ctor_get(v___x_566_, 0);
                                    lean_inc(v_a_567_);
                                    lean_dec_ref_known(v___x_566_, 1);
                                    v___x_568_ =
                                        l_Lean_Server_FileWorker_runLakeSetupFile___closed__2;
                                    v___x_569_ = lean_io_process_child_wait(v___x_568_, v_snd_555_);
                                    v_isSharedCheck_600_ = (!lean_is_exclusive(v_snd_555_)) as u8;
                                    if v_isSharedCheck_600_ == 0 {
                                        v_unused_601_ = lean_ctor_get(v_snd_555_, 2);
                                        lean_dec(v_unused_601_);
                                        v_unused_602_ = lean_ctor_get(v_snd_555_, 1);
                                        lean_dec(v_unused_602_);
                                        v_unused_603_ = lean_ctor_get(v_snd_555_, 0);
                                        lean_dec(v_unused_603_);
                                        v___x_571_ = v_snd_555_;
                                        v_isShared_572_ = v_isSharedCheck_600_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_dec(v_snd_555_);
                                        v___x_571_ = lean_box(0);
                                        v_isShared_572_ = v_isSharedCheck_600_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_564_);
                                    lean_dec(v_snd_555_);
                                    lean_dec_ref_known(v_spawnArgs_549_, 5);
                                    v_a_604_ = lean_ctor_get(v___x_566_, 0);
                                    v_isSharedCheck_611_ = (!lean_is_exclusive(v___x_566_)) as u8;
                                    if v_isSharedCheck_611_ == 0 {
                                        v___x_606_ = v___x_566_;
                                        v_isShared_607_ = v_isSharedCheck_611_;
                                        state = 8;
                                        continue;
                                    } else {
                                        lean_inc(v_a_604_);
                                        lean_dec(v___x_566_);
                                        v___x_606_ = lean_box(0);
                                        v_isShared_607_ = v_isSharedCheck_611_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v___x_561_);
                                lean_dec(v_snd_555_);
                                lean_dec_ref_known(v_spawnArgs_549_, 5);
                                v_a_612_ = lean_ctor_get(v___x_563_, 0);
                                v_isSharedCheck_619_ = (!lean_is_exclusive(v___x_563_)) as u8;
                                if v_isSharedCheck_619_ == 0 {
                                    v___x_614_ = v___x_563_;
                                    v_isShared_615_ = v_isSharedCheck_619_;
                                    state = 10;
                                    continue;
                                } else {
                                    lean_inc(v_a_612_);
                                    lean_dec(v___x_563_);
                                    v___x_614_ = lean_box(0);
                                    v_isShared_615_ = v_isSharedCheck_619_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_snd_555_);
                            lean_dec_ref_known(v_spawnArgs_549_, 5);
                            lean_dec_ref(v_args_542_);
                            lean_dec_ref(v_handleStderr_539_);
                            lean_dec_ref(v_lakePath_536_);
                            v_a_620_ = lean_ctor_get(v___x_558_, 0);
                            v_isSharedCheck_627_ = (!lean_is_exclusive(v___x_558_)) as u8;
                            if v_isSharedCheck_627_ == 0 {
                                v___x_622_ = v___x_558_;
                                v_isShared_623_ = v_isSharedCheck_627_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_620_);
                                lean_dec(v___x_558_);
                                v___x_622_ = lean_box(0);
                                v_isShared_623_ = v_isSharedCheck_627_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_spawnArgs_549_, 5);
                        lean_dec_ref(v_args_542_);
                        lean_dec_ref(v_handleStderr_539_);
                        lean_dec_ref(v_header_538_);
                        lean_dec_ref(v_lakePath_536_);
                        v_a_628_ = lean_ctor_get(v___x_552_, 0);
                        v_isSharedCheck_635_ = (!lean_is_exclusive(v___x_552_)) as u8;
                        if v_isSharedCheck_635_ == 0 {
                            v___x_630_ = v___x_552_;
                            v_isShared_631_ = v_isSharedCheck_635_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_628_);
                            lean_dec(v___x_552_);
                            v___x_630_ = lean_box(0);
                            v_isShared_631_ = v_isSharedCheck_635_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v_spawnArgs_549_, 5);
                    lean_dec_ref(v_args_542_);
                    lean_dec_ref(v_handleStderr_539_);
                    lean_dec_ref(v_header_538_);
                    lean_dec_ref(v_lakePath_536_);
                    v_a_636_ = lean_ctor_get(v___x_550_, 0);
                    v_isSharedCheck_643_ = (!lean_is_exclusive(v___x_550_)) as u8;
                    if v_isSharedCheck_643_ == 0 {
                        v___x_638_ = v___x_550_;
                        v_isShared_639_ = v_isSharedCheck_643_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_636_);
                        lean_dec(v___x_550_);
                        v___x_638_ = lean_box(0);
                        v_isShared_639_ = v_isSharedCheck_643_;
                        state = 16;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v___x_569_) == 0 {
                    v_a_573_ = lean_ctor_get(v___x_569_, 0);
                    v_isSharedCheck_591_ = (!lean_is_exclusive(v___x_569_)) as u8;
                    if v_isSharedCheck_591_ == 0 {
                        v___x_575_ = v___x_569_;
                        v_isShared_576_ = v_isSharedCheck_591_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_573_);
                        lean_dec(v___x_569_);
                        v___x_575_ = lean_box(0);
                        v_isShared_576_ = v_isSharedCheck_591_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_571_);
                    lean_dec(v_a_567_);
                    lean_dec(v_a_564_);
                    lean_dec_ref_known(v_spawnArgs_549_, 5);
                    v_a_592_ = lean_ctor_get(v___x_569_, 0);
                    v_isSharedCheck_599_ = (!lean_is_exclusive(v___x_569_)) as u8;
                    if v_isSharedCheck_599_ == 0 {
                        v___x_594_ = v___x_569_;
                        v_isShared_595_ = v_isSharedCheck_599_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_592_);
                        lean_dec(v___x_569_);
                        v___x_594_ = lean_box(0);
                        v_isShared_595_ = v_isSharedCheck_599_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_577_ = lean_string_utf8_byte_size(v_a_564_);
                if v_isShared_572_ == 0 {
                    lean_ctor_set(v___x_571_, 2, v___x_577_);
                    lean_ctor_set(v___x_571_, 1, v___x_545_);
                    lean_ctor_set(v___x_571_, 0, v_a_564_);
                    v___x_579_ = v___x_571_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_564_);
                    lean_ctor_set(v_reuseFailAlloc_590_, 1, v___x_545_);
                    lean_ctor_set(v_reuseFailAlloc_590_, 2, v___x_577_);
                    v___x_579_ = v_reuseFailAlloc_590_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_580_ = l_String_Slice_trimAscii(v___x_579_);
                v_str_581_ = lean_ctor_get(v___x_580_, 0);
                lean_inc_ref(v_str_581_);
                v_startInclusive_582_ = lean_ctor_get(v___x_580_, 1);
                lean_inc(v_startInclusive_582_);
                v_endExclusive_583_ = lean_ctor_get(v___x_580_, 2);
                lean_inc(v_endExclusive_583_);
                lean_dec_ref(v___x_580_);
                v___x_584_ = lean_string_utf8_extract(
                    v_str_581_,
                    v_startInclusive_582_,
                    v_endExclusive_583_,
                );
                lean_dec(v_endExclusive_583_);
                lean_dec(v_startInclusive_582_);
                lean_dec_ref(v_str_581_);
                v___x_585_ = lean_alloc_ctor(0, 3, (4) as u32);
                lean_ctor_set(v___x_585_, 0, v_spawnArgs_549_);
                lean_ctor_set(v___x_585_, 1, v___x_584_);
                lean_ctor_set(v___x_585_, 2, v_a_567_);
                v___x_586_ = lean_unbox_uint32(v_a_573_);
                lean_dec(v_a_573_);
                lean_ctor_set_uint32(
                    v___x_585_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_586_,
                );
                if v_isShared_576_ == 0 {
                    lean_ctor_set(v___x_575_, 0, v___x_585_);
                    v___x_588_ = v___x_575_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_585_);
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
                    v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
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
                    v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
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
                    v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
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
                    v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
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
                    v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
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
                    v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
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
    mut v_m_653_: *mut LeanObject,
    mut v_lakePath_654_: *mut LeanObject,
    mut v_filePath_655_: *mut LeanObject,
    mut v_header_656_: *mut LeanObject,
    mut v_handleStderr_657_: *mut LeanObject,
    mut v_a_658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_659_: *mut LeanObject = core::ptr::null_mut();
    v_res_659_ = l_Lean_Server_FileWorker_runLakeSetupFile(
        v_m_653_,
        v_lakePath_654_,
        v_filePath_655_,
        v_header_656_,
        v_handleStderr_657_,
    );
    lean_dec_ref(v_m_653_);
    return v_res_659_;
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_ctorIdx(
    mut v_x_660_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_660_) {
        0 => {
            let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
            v___x_661_ = lean_unsigned_to_nat(0);
            return v___x_661_;
        }
        1 => {
            let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
            v___x_662_ = lean_unsigned_to_nat(1);
            return v___x_662_;
        }
        2 => {
            let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
            v___x_663_ = lean_unsigned_to_nat(2);
            return v___x_663_;
        }
        _ => {
            let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
            v___x_664_ = lean_unsigned_to_nat(3);
            return v___x_664_;
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_ctorIdx___boxed(
    mut v_x_665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_666_: *mut LeanObject = core::ptr::null_mut();
    v_res_666_ = l_Lean_Server_FileWorker_FileSetupResult_ctorIdx(v_x_665_);
    lean_dec(v_x_665_);
    return v_res_666_;
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(
    mut v_t_667_: *mut LeanObject,
    mut v_k_668_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_667_) {
        0 => {
            let mut v_setup_669_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
            v_setup_669_ = lean_ctor_get(v_t_667_, 0);
            lean_inc_ref(v_setup_669_);
            lean_dec_ref_known(v_t_667_, 1);
            v___x_670_ = lean_apply_1(v_k_668_, v_setup_669_);
            return v___x_670_;
        }
        3 => {
            let mut v_msg_671_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
            v_msg_671_ = lean_ctor_get(v_t_667_, 0);
            lean_inc_ref(v_msg_671_);
            lean_dec_ref_known(v_t_667_, 1);
            v___x_672_ = lean_apply_1(v_k_668_, v_msg_671_);
            return v___x_672_;
        }
        _ => {
            lean_dec(v_t_667_);
            return v_k_668_;
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_ctorElim(
    mut v_motive_673_: *mut LeanObject,
    mut v_ctorIdx_674_: *mut LeanObject,
    mut v_t_675_: *mut LeanObject,
    mut v_h_676_: *mut LeanObject,
    mut v_k_677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    v___x_678_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_675_, v_k_677_);
    return v___x_678_;
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_ctorElim___boxed(
    mut v_motive_679_: *mut LeanObject,
    mut v_ctorIdx_680_: *mut LeanObject,
    mut v_t_681_: *mut LeanObject,
    mut v_h_682_: *mut LeanObject,
    mut v_k_683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_684_: *mut LeanObject = core::ptr::null_mut();
    v_res_684_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim(
        v_motive_679_,
        v_ctorIdx_680_,
        v_t_681_,
        v_h_682_,
        v_k_683_,
    );
    lean_dec(v_ctorIdx_680_);
    return v_res_684_;
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_success_elim___redArg(
    mut v_t_685_: *mut LeanObject,
    mut v_success_686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    v___x_687_ =
        l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_685_, v_success_686_);
    return v___x_687_;
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_success_elim(
    mut v_motive_688_: *mut LeanObject,
    mut v_t_689_: *mut LeanObject,
    mut v_h_690_: *mut LeanObject,
    mut v_success_691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    v___x_692_ =
        l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_689_, v_success_691_);
    return v___x_692_;
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_noLakefile_elim___redArg(
    mut v_t_693_: *mut LeanObject,
    mut v_noLakefile_694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    v___x_695_ =
        l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_693_, v_noLakefile_694_);
    return v___x_695_;
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_noLakefile_elim(
    mut v_motive_696_: *mut LeanObject,
    mut v_t_697_: *mut LeanObject,
    mut v_h_698_: *mut LeanObject,
    mut v_noLakefile_699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    v___x_700_ =
        l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_697_, v_noLakefile_699_);
    return v___x_700_;
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_importsOutOfDate_elim___redArg(
    mut v_t_701_: *mut LeanObject,
    mut v_importsOutOfDate_702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    v___x_703_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(
        v_t_701_,
        v_importsOutOfDate_702_,
    );
    return v___x_703_;
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_importsOutOfDate_elim(
    mut v_motive_704_: *mut LeanObject,
    mut v_t_705_: *mut LeanObject,
    mut v_h_706_: *mut LeanObject,
    mut v_importsOutOfDate_707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    v___x_708_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(
        v_t_705_,
        v_importsOutOfDate_707_,
    );
    return v___x_708_;
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_error_elim___redArg(
    mut v_t_709_: *mut LeanObject,
    mut v_error_710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    v___x_711_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_709_, v_error_710_);
    return v___x_711_;
}
pub unsafe fn l_Lean_Server_FileWorker_FileSetupResult_error_elim(
    mut v_motive_712_: *mut LeanObject,
    mut v_t_713_: *mut LeanObject,
    mut v_h_714_: *mut LeanObject,
    mut v_error_715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    v___x_716_ = l_Lean_Server_FileWorker_FileSetupResult_ctorElim___redArg(v_t_713_, v_error_715_);
    return v___x_716_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(
    mut v_as_717_: *mut LeanObject,
    mut v_i_718_: usize,
    mut v_stop_719_: usize,
    mut v_b_720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_722_: u8 = 0;
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: usize = 0;
    let mut v___x_727_: usize = 0;
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_722_ = lean_usize_dec_eq(v_i_718_, v_stop_719_);
                if v___x_722_ == 0 {
                    v___x_723_ = lean_array_uget_borrowed(v_as_717_, v_i_718_);
                    lean_inc(v___x_723_);
                    v___x_724_ = lean_load_dynlib(v___x_723_);
                    if lean_obj_tag(v___x_724_) == 0 {
                        v_a_725_ = lean_ctor_get(v___x_724_, 0);
                        lean_inc(v_a_725_);
                        lean_dec_ref_known(v___x_724_, 1);
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
                    v___x_729_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_729_, 0, v_b_720_);
                    return v___x_729_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0___boxed(
    mut v_as_730_: *mut LeanObject,
    mut v_i_731_: *mut LeanObject,
    mut v_stop_732_: *mut LeanObject,
    mut v_b_733_: *mut LeanObject,
    mut v___y_734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_735_: usize = 0;
    let mut v_stop_boxed_736_: usize = 0;
    let mut v_res_737_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_735_ = lean_unbox_usize(v_i_731_);
    lean_dec(v_i_731_);
    v_stop_boxed_736_ = lean_unbox_usize(v_stop_732_);
    lean_dec(v_stop_732_);
    v_res_737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_setupFile_spec__0(v_as_730_, v_i_boxed_735_, v_stop_boxed_736_, v_b_733_);
    lean_dec_ref(v_as_730_);
    return v_res_737_;
}
pub unsafe fn l_Lean_Server_FileWorker_setupFile(
    mut v_m_744_: *mut LeanObject,
    mut v_header_745_: *mut LeanObject,
    mut v_handleStderr_746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_uri_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_753_: u8 = 0;
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_758_: u8 = 0;
    let mut v___x_759_: u8 = 0;
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_768_: u8 = 0;
    let mut v_spawnArgs_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exitCode_770_: u32 = 0;
    let mut v_stdout_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stderr_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmd_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: u32 = 0;
    let mut v___x_795_: u8 = 0;
    let mut v___x_796_: u32 = 0;
    let mut v___x_797_: u8 = 0;
    let mut v___x_798_: u32 = 0;
    let mut v___x_799_: u8 = 0;
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_826_: u8 = 0;
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_839_: u8 = 0;
    let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_843_: u8 = 0;
    let mut v_dynlibs_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: u8 = 0;
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: u8 = 0;
    let mut v___x_850_: usize = 0;
    let mut v___x_851_: usize = 0;
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_853_: usize = 0;
    let mut v___x_854_: usize = 0;
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_856_: u8 = 0;
    let mut v_isSharedCheck_857_: u8 = 0;
    let mut v_a_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_861_: u8 = 0;
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_865_: u8 = 0;
    let mut v_isSharedCheck_866_: u8 = 0;
    let mut v_a_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_870_: u8 = 0;
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_874_: u8 = 0;
    let mut v_isSharedCheck_875_: u8 = 0;
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_uri_748_ = lean_ctor_get(v_m_744_, 0);
                v___x_749_ = l_System_Uri_fileUriToPath_x3f(v_uri_748_);
                if lean_obj_tag(v___x_749_) == 1 {
                    v_val_750_ = lean_ctor_get(v___x_749_, 0);
                    v_isSharedCheck_875_ = (!lean_is_exclusive(v___x_749_)) as u8;
                    if v_isSharedCheck_875_ == 0 {
                        v___x_752_ = v___x_749_;
                        v_isShared_753_ = v_isSharedCheck_875_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_750_);
                        lean_dec(v___x_749_);
                        v___x_752_ = lean_box(0);
                        v_isShared_753_ = v_isSharedCheck_875_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_749_);
                    lean_dec_ref(v_handleStderr_746_);
                    lean_dec_ref(v_header_745_);
                    v___x_876_ = lean_box(1);
                    v___x_877_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_877_, 0, v___x_876_);
                    return v___x_877_;
                }
            }
            1 => {
                v___x_754_ = l_Lean_determineLakePath();
                if lean_obj_tag(v___x_754_) == 0 {
                    v_a_755_ = lean_ctor_get(v___x_754_, 0);
                    v_isSharedCheck_866_ = (!lean_is_exclusive(v___x_754_)) as u8;
                    if v_isSharedCheck_866_ == 0 {
                        v___x_757_ = v___x_754_;
                        v_isShared_758_ = v_isSharedCheck_866_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_755_);
                        lean_dec(v___x_754_);
                        v___x_757_ = lean_box(0);
                        v_isShared_758_ = v_isSharedCheck_866_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_752_);
                    lean_dec(v_val_750_);
                    lean_dec_ref(v_handleStderr_746_);
                    lean_dec_ref(v_header_745_);
                    v_a_867_ = lean_ctor_get(v___x_754_, 0);
                    v_isSharedCheck_874_ = (!lean_is_exclusive(v___x_754_)) as u8;
                    if v_isSharedCheck_874_ == 0 {
                        v___x_869_ = v___x_754_;
                        v_isShared_870_ = v_isSharedCheck_874_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_a_867_);
                        lean_dec(v___x_754_);
                        v___x_869_ = lean_box(0);
                        v_isShared_870_ = v_isSharedCheck_874_;
                        state = 20;
                        continue;
                    }
                }
            }
            2 => {
                v___x_759_ = l_System_FilePath_pathExists(v_a_755_);
                if v___x_759_ == 0 {
                    lean_dec(v_a_755_);
                    lean_del_object(v___x_752_);
                    lean_dec(v_val_750_);
                    lean_dec_ref(v_handleStderr_746_);
                    lean_dec_ref(v_header_745_);
                    v___x_760_ = lean_box(1);
                    if v_isShared_758_ == 0 {
                        lean_ctor_set(v___x_757_, 0, v___x_760_);
                        v___x_762_ = v___x_757_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
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
                    if lean_obj_tag(v___x_764_) == 0 {
                        v_a_765_ = lean_ctor_get(v___x_764_, 0);
                        v_isSharedCheck_857_ = (!lean_is_exclusive(v___x_764_)) as u8;
                        if v_isSharedCheck_857_ == 0 {
                            v___x_767_ = v___x_764_;
                            v_isShared_768_ = v_isSharedCheck_857_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_765_);
                            lean_dec(v___x_764_);
                            v___x_767_ = lean_box(0);
                            v_isShared_768_ = v_isSharedCheck_857_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_757_);
                        lean_del_object(v___x_752_);
                        v_a_858_ = lean_ctor_get(v___x_764_, 0);
                        v_isSharedCheck_865_ = (!lean_is_exclusive(v___x_764_)) as u8;
                        if v_isSharedCheck_865_ == 0 {
                            v___x_860_ = v___x_764_;
                            v_isShared_861_ = v_isSharedCheck_865_;
                            state = 18;
                            continue;
                        } else {
                            lean_inc(v_a_858_);
                            lean_dec(v___x_764_);
                            v___x_860_ = lean_box(0);
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
                v_spawnArgs_769_ = lean_ctor_get(v_a_765_, 0);
                lean_inc_ref(v_spawnArgs_769_);
                v_exitCode_770_ = lean_ctor_get_uint32(
                    v_a_765_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_stdout_771_ = lean_ctor_get(v_a_765_, 1);
                lean_inc_ref(v_stdout_771_);
                v_stderr_772_ = lean_ctor_get(v_a_765_, 2);
                lean_inc_ref(v_stderr_772_);
                lean_dec(v_a_765_);
                v_cmd_773_ = lean_ctor_get(v_spawnArgs_769_, 1);
                lean_inc_ref(v_cmd_773_);
                v_args_774_ = lean_ctor_get(v_spawnArgs_769_, 2);
                lean_inc_ref(v_args_774_);
                lean_dec_ref(v_spawnArgs_769_);
                v___x_775_ = l_Lean_Server_FileWorker_setupFile___closed__0;
                v___x_776_ = lean_array_to_list(v_args_774_);
                v___x_777_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_777_, 0, v_cmd_773_);
                lean_ctor_set(v___x_777_, 1, v___x_776_);
                v___x_778_ = l_String_intercalate(v___x_775_, v___x_777_);
                v___x_794_ = 0;
                v___x_795_ = lean_uint32_dec_eq(v_exitCode_770_, v___x_794_);
                if v___x_795_ == 0 {
                    lean_del_object(v___x_767_);
                    lean_del_object(v___x_752_);
                    v___x_796_ = 2;
                    v___x_797_ = lean_uint32_dec_eq(v_exitCode_770_, v___x_796_);
                    if v___x_797_ == 0 {
                        v___x_798_ = 3;
                        v___x_799_ = lean_uint32_dec_eq(v_exitCode_770_, v___x_798_);
                        if v___x_799_ == 0 {
                            v___x_800_ = l_Lean_Server_FileWorker_setupFile___closed__4;
                            v___x_801_ = lean_string_append(v___x_800_, v___x_778_);
                            lean_dec_ref(v___x_778_);
                            v___x_802_ = l_Lean_Server_FileWorker_setupFile___closed__5;
                            v___x_803_ = lean_string_append(v___x_801_, v___x_802_);
                            v___x_804_ = lean_string_append(v___x_803_, v_stdout_771_);
                            lean_dec_ref(v_stdout_771_);
                            v___x_805_ = l_Lean_Server_FileWorker_setupFile___closed__3;
                            v___x_806_ = lean_string_append(v___x_804_, v___x_805_);
                            v___x_807_ = lean_string_append(v___x_806_, v_stderr_772_);
                            lean_dec_ref(v_stderr_772_);
                            v___x_808_ = lean_alloc_ctor(3, 1, (0) as u32);
                            lean_ctor_set(v___x_808_, 0, v___x_807_);
                            if v_isShared_758_ == 0 {
                                lean_ctor_set(v___x_757_, 0, v___x_808_);
                                v___x_810_ = v___x_757_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
                                v___x_810_ = v_reuseFailAlloc_811_;
                                state = 8;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_778_);
                            lean_dec_ref(v_stderr_772_);
                            lean_dec_ref(v_stdout_771_);
                            v___x_812_ = lean_box(2);
                            if v_isShared_758_ == 0 {
                                lean_ctor_set(v___x_757_, 0, v___x_812_);
                                v___x_814_ = v___x_757_;
                                state = 9;
                                continue;
                            } else {
                                v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_812_);
                                v___x_814_ = v_reuseFailAlloc_815_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_778_);
                        lean_dec_ref(v_stderr_772_);
                        lean_dec_ref(v_stdout_771_);
                        v___x_816_ = lean_box(1);
                        if v_isShared_758_ == 0 {
                            lean_ctor_set(v___x_757_, 0, v___x_816_);
                            v___x_818_ = v___x_757_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
                            v___x_818_ = v_reuseFailAlloc_819_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_inc_ref(v_stdout_771_);
                    v___x_820_ = l_Lean_Json_parse(v_stdout_771_);
                    if lean_obj_tag(v___x_820_) == 0 {
                        lean_dec_ref_known(v___x_820_, 1);
                        lean_del_object(v___x_757_);
                        state = 5;
                        continue;
                    } else {
                        v_a_821_ = lean_ctor_get(v___x_820_, 0);
                        lean_inc(v_a_821_);
                        lean_dec_ref_known(v___x_820_, 1);
                        v___x_822_ = l_Lean_instFromJsonModuleSetup_fromJson(v_a_821_);
                        if lean_obj_tag(v___x_822_) == 1 {
                            lean_dec_ref(v___x_778_);
                            lean_dec_ref(v_stderr_772_);
                            lean_dec_ref(v_stdout_771_);
                            lean_del_object(v___x_767_);
                            lean_del_object(v___x_752_);
                            v_a_823_ = lean_ctor_get(v___x_822_, 0);
                            v_isSharedCheck_856_ = (!lean_is_exclusive(v___x_822_)) as u8;
                            if v_isSharedCheck_856_ == 0 {
                                v___x_825_ = v___x_822_;
                                v_isShared_826_ = v_isSharedCheck_856_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_823_);
                                lean_dec(v___x_822_);
                                v___x_825_ = lean_box(0);
                                v_isShared_826_ = v_isSharedCheck_856_;
                                state = 11;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_822_);
                            lean_del_object(v___x_757_);
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            5 => {
                v___x_780_ = l_Lean_Server_FileWorker_setupFile___closed__1;
                v___x_781_ = lean_string_append(v___x_780_, v___x_778_);
                lean_dec_ref(v___x_778_);
                v___x_782_ = l_Lean_Server_FileWorker_setupFile___closed__2;
                v___x_783_ = lean_string_append(v___x_781_, v___x_782_);
                v___x_784_ = lean_string_append(v___x_783_, v_stdout_771_);
                lean_dec_ref(v_stdout_771_);
                v___x_785_ = l_Lean_Server_FileWorker_setupFile___closed__3;
                v___x_786_ = lean_string_append(v___x_784_, v___x_785_);
                v___x_787_ = lean_string_append(v___x_786_, v_stderr_772_);
                lean_dec_ref(v_stderr_772_);
                if v_isShared_753_ == 0 {
                    lean_ctor_set_tag(v___x_752_, 3);
                    lean_ctor_set(v___x_752_, 0, v___x_787_);
                    v___x_789_ = v___x_752_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_793_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_787_);
                    v___x_789_ = v_reuseFailAlloc_793_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_768_ == 0 {
                    lean_ctor_set(v___x_767_, 0, v___x_789_);
                    v___x_791_ = v___x_767_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_789_);
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
                v_dynlibs_844_ = lean_ctor_get(v_a_823_, 4);
                v___x_845_ = lean_unsigned_to_nat(0);
                v___x_846_ = lean_array_get_size(v_dynlibs_844_);
                v___x_847_ = lean_nat_dec_lt(v___x_845_, v___x_846_);
                if v___x_847_ == 0 {
                    state = 12;
                    continue;
                } else {
                    v___x_848_ = lean_box(0);
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
                    lean_ctor_set_tag(v___x_825_, 0);
                    v___x_829_ = v___x_825_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_823_);
                    v___x_829_ = v_reuseFailAlloc_833_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_758_ == 0 {
                    lean_ctor_set(v___x_757_, 0, v___x_829_);
                    v___x_831_ = v___x_757_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_829_);
                    v___x_831_ = v_reuseFailAlloc_832_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_831_;
            }
            15 => {
                if lean_obj_tag(v___y_835_) == 0 {
                    lean_dec_ref_known(v___y_835_, 1);
                    state = 12;
                    continue;
                } else {
                    lean_del_object(v___x_825_);
                    lean_dec(v_a_823_);
                    lean_del_object(v___x_757_);
                    v_a_836_ = lean_ctor_get(v___y_835_, 0);
                    v_isSharedCheck_843_ = (!lean_is_exclusive(v___y_835_)) as u8;
                    if v_isSharedCheck_843_ == 0 {
                        v___x_838_ = v___y_835_;
                        v_isShared_839_ = v_isSharedCheck_843_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_836_);
                        lean_dec(v___y_835_);
                        v___x_838_ = lean_box(0);
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
                    v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
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
                    v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
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
                    v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
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
    mut v_m_878_: *mut LeanObject,
    mut v_header_879_: *mut LeanObject,
    mut v_handleStderr_880_: *mut LeanObject,
    mut v_a_881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_882_: *mut LeanObject = core::ptr::null_mut();
    v_res_882_ = l_Lean_Server_FileWorker_setupFile(v_m_878_, v_header_879_, v_handleStderr_880_);
    lean_dec_ref(v_m_878_);
    return v_res_882_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_FileWorker_SetupFile(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_Utils(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_LakePath(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_ServerTask(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_FileWorker_SetupFile(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_FileWorker_SetupFile(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_Utils(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_LakePath(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Server_ServerTask(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_FileWorker_SetupFile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Server_FileWorker_SetupFile(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Server_FileWorker_SetupFile(builtin);
}

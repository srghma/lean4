// Lean compiler output
// Module: Lean.Server.Utils
// Imports: Init.System.Uri Lean.Data.Lsp.Communication Lean.Data.Lsp.Diagnostics Lean.Data.Lsp.Extra Lean.Server.InfoUtils
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_pos_x21;
use crate::r#gen::Init::Data::String::Extra::l_String_crlfToLf;
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_toString;
use crate::r#gen::Init::Prelude::l_Lean_Name_str___override;
use crate::r#gen::Init::System::FilePath::l_System_FilePath_extension;
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Init::System::Uri::{
    initialize_Init_System_Uri, l_System_Uri_fileUriToPath_x3f, l_System_Uri_pathToUri,
    runtime_initialize_Init_System_Uri,
};
use crate::r#gen::Lean::Data::Lsp::Communication::{
    initialize_Lean_Data_Lsp_Communication, runtime_initialize_Lean_Data_Lsp_Communication,
};
use crate::r#gen::Lean::Data::Lsp::Diagnostics::{
    initialize_Lean_Data_Lsp_Diagnostics, runtime_initialize_Lean_Data_Lsp_Diagnostics,
};
use crate::r#gen::Lean::Data::Lsp::Extra::{
    initialize_Lean_Data_Lsp_Extra, runtime_initialize_Lean_Data_Lsp_Extra,
};
use crate::r#gen::Lean::Data::Lsp::Utf16::{
    l_Lean_FileMap_lspPosToUtf8Pos, l_Lean_FileMap_utf8PosToLspPos,
};
use crate::r#gen::Lean::Data::Position::{l_Lean_instInhabitedFileMap_default, l_String_toFileMap};
use crate::r#gen::Lean::Server::InfoUtils::{
    initialize_Lean_Server_InfoUtils, runtime_initialize_Lean_Server_InfoUtils,
};
use crate::r#gen::Lean::Util::Path::{
    l_Lean_SearchPath_findModuleWithExt, l_Lean_getSrcSearchPath, l_Lean_searchModuleNameOfFileName,
};
use crate::ffi::lean_array_uget_borrowed;
use crate::ffi::lean_nat_to_int;
use crate::ffi::lean_string_utf8_extract;
use crate::ffi::lean_string_append;
use crate::ffi::lean_string_memcmp;
use crate::ffi::{lean_usize_add, lean_usize_of_nat};
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_dec_le,
    lean_nat_dec_lt, lean_string_dec_eq, lean_string_utf8_byte_size, lean_usize_dec_eq,
};
use crate::ffi::lean_io_realpath;
pub static l_Lean_Server_instInhabitedDocumentMeta_default___closed__0_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Server_instInhabitedDocumentMeta_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instInhabitedDocumentMeta_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Server_instInhabitedDocumentMeta_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instInhabitedDocumentMeta_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Server_instInhabitedDocumentMeta_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Server_instInhabitedDocumentMeta: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_mkPublishDiagnosticsNotification___closed__0_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        116, 101, 120, 116, 68, 111, 99, 117, 109, 101, 110, 116, 47, 112, 117, 98, 108, 105, 115,
        104, 68, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 0,
    ],
};
static mut l_Lean_Server_mkPublishDiagnosticsNotification___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_mkPublishDiagnosticsNotification___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_mkFileProgressNotification___closed__0_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
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
        36, 47, 108, 101, 97, 110, 47, 102, 105, 108, 101, 80, 114, 111, 103, 114, 101, 115, 115, 0,
    ],
};
static mut l_Lean_Server_mkFileProgressNotification___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_mkFileProgressNotification___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_mkFileProgressDoneNotification___closed__0_value:
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
static mut l_Lean_Server_mkFileProgressDoneNotification___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_mkFileProgressDoneNotification___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
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
        119, 111, 114, 107, 115, 112, 97, 99, 101, 47, 97, 112, 112, 108, 121, 69, 100, 105, 116, 0,
    ],
};
static mut l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_mkApplyWorkspaceEditRequest___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Server_mkApplyWorkspaceEditRequest___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_mkApplyWorkspaceEditRequest___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [101, 120, 116, 101, 114, 110, 97, 108, 58, 0],
};
static mut l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_documentUriFromModule_x3f___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [108, 101, 97, 110, 0],
};
static mut l_Lean_Server_documentUriFromModule_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_documentUriFromModule_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_moduleFromDocumentUri___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Server_documentUriFromModule_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Server_moduleFromDocumentUri___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_moduleFromDocumentUri___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_IO_throwServerError___redArg(
    mut v_err_595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_597_ = lean_mk_io_user_error(v_err_595_);
    v___x_598_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_598_, 0, v___x_597_);
    return v___x_598_;
}
pub unsafe fn l_IO_throwServerError___redArg___boxed(
    mut v_err_599_: *mut crate::leanh::LeanObject,
    mut v_a_600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_601_ = l_IO_throwServerError___redArg(v_err_599_);
    return v_res_601_;
}
pub unsafe fn l_IO_throwServerError(
    mut v_00_u03b1_602_: *mut crate::leanh::LeanObject,
    mut v_err_603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_605_ = l_IO_throwServerError___redArg(v_err_603_);
    return v___x_605_;
}
pub unsafe fn l_IO_throwServerError___boxed(
    mut v_00_u03b1_606_: *mut crate::leanh::LeanObject,
    mut v_err_607_: *mut crate::leanh::LeanObject,
    mut v_a_608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_609_ = l_IO_throwServerError(v_00_u03b1_606_, v_err_607_);
    return v_res_609_;
}
pub unsafe fn l_IO_FS_Stream_chainRight___lam__0(
    mut v_read_610_: *mut crate::leanh::LeanObject,
    mut v_b_611_: *mut crate::leanh::LeanObject,
    mut v_flushEagerly_612_: u8,
    mut v_sz_613_: usize,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_flush_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_write_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_623_: u8 = 0;
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_630_: u8 = 0;
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_634_: u8 = 0;
    let mut v_unused_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_639_: u8 = 0;
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_643_: u8 = 0;
    let mut v_isSharedCheck_644_: u8 = 0;
    let mut v_unused_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_649_: u8 = 0;
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_653_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_615_ = crate::leanh::lean_box_usize(v_sz_613_);
                v___x_616_ =
                    crate::leanh::lean_apply_2(v_read_610_, v___x_615_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_616_) == 0 {
                    v_a_617_ = crate::leanh::lean_ctor_get(v___x_616_, 0);
                    crate::leanh::lean_inc_n(v_a_617_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_616_, 1);
                    v_flush_618_ = crate::leanh::lean_ctor_get(v_b_611_, 0);
                    crate::leanh::lean_inc_ref(v_flush_618_);
                    v_write_619_ = crate::leanh::lean_ctor_get(v_b_611_, 2);
                    crate::leanh::lean_inc_ref(v_write_619_);
                    crate::leanh::lean_dec_ref(v_b_611_);
                    v___x_620_ = crate::leanh::lean_apply_2(
                        v_write_619_,
                        v_a_617_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_620_) == 0 {
                        v_isSharedCheck_644_ = (!crate::leanh::lean_is_exclusive(v___x_620_)) as u8;
                        if v_isSharedCheck_644_ == 0 {
                            v_unused_645_ = crate::leanh::lean_ctor_get(v___x_620_, 0);
                            crate::leanh::lean_dec(v_unused_645_);
                            v___x_622_ = v___x_620_;
                            v_isShared_623_ = v_isSharedCheck_644_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_620_);
                            v___x_622_ = crate::leanh::lean_box(0);
                            v_isShared_623_ = v_isSharedCheck_644_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_flush_618_);
                        crate::leanh::lean_dec(v_a_617_);
                        v_a_646_ = crate::leanh::lean_ctor_get(v___x_620_, 0);
                        v_isSharedCheck_653_ = (!crate::leanh::lean_is_exclusive(v___x_620_)) as u8;
                        if v_isSharedCheck_653_ == 0 {
                            v___x_648_ = v___x_620_;
                            v_isShared_649_ = v_isSharedCheck_653_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_646_);
                            crate::leanh::lean_dec(v___x_620_);
                            v___x_648_ = crate::leanh::lean_box(0);
                            v_isShared_649_ = v_isSharedCheck_653_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_611_);
                    return v___x_616_;
                }
            }
            1 => {
                if v_flushEagerly_612_ == 0 {
                    crate::leanh::lean_dec_ref(v_flush_618_);
                    if v_isShared_623_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_622_, 0, v_a_617_);
                        v___x_625_ = v___x_622_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_626_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_617_);
                        v___x_625_ = v_reuseFailAlloc_626_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_622_);
                    v___x_627_ =
                        crate::leanh::lean_apply_1(v_flush_618_, crate::leanh::lean_box(0));
                    if crate::leanh::lean_obj_tag(v___x_627_) == 0 {
                        v_isSharedCheck_634_ = (!crate::leanh::lean_is_exclusive(v___x_627_)) as u8;
                        if v_isSharedCheck_634_ == 0 {
                            v_unused_635_ = crate::leanh::lean_ctor_get(v___x_627_, 0);
                            crate::leanh::lean_dec(v_unused_635_);
                            v___x_629_ = v___x_627_;
                            v_isShared_630_ = v_isSharedCheck_634_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_627_);
                            v___x_629_ = crate::leanh::lean_box(0);
                            v_isShared_630_ = v_isSharedCheck_634_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_617_);
                        v_a_636_ = crate::leanh::lean_ctor_get(v___x_627_, 0);
                        v_isSharedCheck_643_ = (!crate::leanh::lean_is_exclusive(v___x_627_)) as u8;
                        if v_isSharedCheck_643_ == 0 {
                            v___x_638_ = v___x_627_;
                            v_isShared_639_ = v_isSharedCheck_643_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_636_);
                            crate::leanh::lean_dec(v___x_627_);
                            v___x_638_ = crate::leanh::lean_box(0);
                            v_isShared_639_ = v_isSharedCheck_643_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_625_;
            }
            3 => {
                if v_isShared_630_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_629_, 0, v_a_617_);
                    v___x_632_ = v___x_629_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_633_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_617_);
                    v___x_632_ = v_reuseFailAlloc_633_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_632_;
            }
            5 => {
                if v_isShared_639_ == 0 {
                    v___x_641_ = v___x_638_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_642_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
                    v___x_641_ = v_reuseFailAlloc_642_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_641_;
            }
            7 => {
                if v_isShared_649_ == 0 {
                    v___x_651_ = v___x_648_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_652_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
                    v___x_651_ = v_reuseFailAlloc_652_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_651_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_chainRight___lam__0___boxed(
    mut v_read_654_: *mut crate::leanh::LeanObject,
    mut v_b_655_: *mut crate::leanh::LeanObject,
    mut v_flushEagerly_656_: *mut crate::leanh::LeanObject,
    mut v_sz_657_: *mut crate::leanh::LeanObject,
    mut v___y_658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_flushEagerly_boxed_659_: u8 = 0;
    let mut v_sz_boxed_660_: usize = 0;
    let mut v_res_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_flushEagerly_boxed_659_ = (crate::leanh::lean_unbox(v_flushEagerly_656_) as u8);
    v_sz_boxed_660_ = crate::leanh::lean_unbox_usize(v_sz_657_);
    crate::leanh::lean_dec(v_sz_657_);
    v_res_661_ = l_IO_FS_Stream_chainRight___lam__0(
        v_read_654_,
        v_b_655_,
        v_flushEagerly_boxed_659_,
        v_sz_boxed_660_,
    );
    return v_res_661_;
}
pub unsafe fn l_IO_FS_Stream_chainRight___lam__1(
    mut v_getLine_662_: *mut crate::leanh::LeanObject,
    mut v_b_663_: *mut crate::leanh::LeanObject,
    mut v_flushEagerly_664_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_flush_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_673_: u8 = 0;
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_680_: u8 = 0;
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_684_: u8 = 0;
    let mut v_unused_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_689_: u8 = 0;
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_693_: u8 = 0;
    let mut v_isSharedCheck_694_: u8 = 0;
    let mut v_unused_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_699_: u8 = 0;
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_703_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_666_ = crate::leanh::lean_apply_1(v_getLine_662_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_666_) == 0 {
                    v_a_667_ = crate::leanh::lean_ctor_get(v___x_666_, 0);
                    crate::leanh::lean_inc_n(v_a_667_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_666_, 1);
                    v_flush_668_ = crate::leanh::lean_ctor_get(v_b_663_, 0);
                    crate::leanh::lean_inc_ref(v_flush_668_);
                    v_putStr_669_ = crate::leanh::lean_ctor_get(v_b_663_, 4);
                    crate::leanh::lean_inc_ref(v_putStr_669_);
                    crate::leanh::lean_dec_ref(v_b_663_);
                    v___x_670_ = crate::leanh::lean_apply_2(
                        v_putStr_669_,
                        v_a_667_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_670_) == 0 {
                        v_isSharedCheck_694_ = (!crate::leanh::lean_is_exclusive(v___x_670_)) as u8;
                        if v_isSharedCheck_694_ == 0 {
                            v_unused_695_ = crate::leanh::lean_ctor_get(v___x_670_, 0);
                            crate::leanh::lean_dec(v_unused_695_);
                            v___x_672_ = v___x_670_;
                            v_isShared_673_ = v_isSharedCheck_694_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_670_);
                            v___x_672_ = crate::leanh::lean_box(0);
                            v_isShared_673_ = v_isSharedCheck_694_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_flush_668_);
                        crate::leanh::lean_dec(v_a_667_);
                        v_a_696_ = crate::leanh::lean_ctor_get(v___x_670_, 0);
                        v_isSharedCheck_703_ = (!crate::leanh::lean_is_exclusive(v___x_670_)) as u8;
                        if v_isSharedCheck_703_ == 0 {
                            v___x_698_ = v___x_670_;
                            v_isShared_699_ = v_isSharedCheck_703_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_696_);
                            crate::leanh::lean_dec(v___x_670_);
                            v___x_698_ = crate::leanh::lean_box(0);
                            v_isShared_699_ = v_isSharedCheck_703_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_663_);
                    return v___x_666_;
                }
            }
            1 => {
                if v_flushEagerly_664_ == 0 {
                    crate::leanh::lean_dec_ref(v_flush_668_);
                    if v_isShared_673_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_672_, 0, v_a_667_);
                        v___x_675_ = v___x_672_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_676_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_667_);
                        v___x_675_ = v_reuseFailAlloc_676_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_672_);
                    v___x_677_ =
                        crate::leanh::lean_apply_1(v_flush_668_, crate::leanh::lean_box(0));
                    if crate::leanh::lean_obj_tag(v___x_677_) == 0 {
                        v_isSharedCheck_684_ = (!crate::leanh::lean_is_exclusive(v___x_677_)) as u8;
                        if v_isSharedCheck_684_ == 0 {
                            v_unused_685_ = crate::leanh::lean_ctor_get(v___x_677_, 0);
                            crate::leanh::lean_dec(v_unused_685_);
                            v___x_679_ = v___x_677_;
                            v_isShared_680_ = v_isSharedCheck_684_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_677_);
                            v___x_679_ = crate::leanh::lean_box(0);
                            v_isShared_680_ = v_isSharedCheck_684_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_667_);
                        v_a_686_ = crate::leanh::lean_ctor_get(v___x_677_, 0);
                        v_isSharedCheck_693_ = (!crate::leanh::lean_is_exclusive(v___x_677_)) as u8;
                        if v_isSharedCheck_693_ == 0 {
                            v___x_688_ = v___x_677_;
                            v_isShared_689_ = v_isSharedCheck_693_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_686_);
                            crate::leanh::lean_dec(v___x_677_);
                            v___x_688_ = crate::leanh::lean_box(0);
                            v_isShared_689_ = v_isSharedCheck_693_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_675_;
            }
            3 => {
                if v_isShared_680_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_679_, 0, v_a_667_);
                    v___x_682_ = v___x_679_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_683_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_667_);
                    v___x_682_ = v_reuseFailAlloc_683_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_682_;
            }
            5 => {
                if v_isShared_689_ == 0 {
                    v___x_691_ = v___x_688_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_692_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
                    v___x_691_ = v_reuseFailAlloc_692_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_691_;
            }
            7 => {
                if v_isShared_699_ == 0 {
                    v___x_701_ = v___x_698_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_702_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
                    v___x_701_ = v_reuseFailAlloc_702_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_701_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_chainRight___lam__1___boxed(
    mut v_getLine_704_: *mut crate::leanh::LeanObject,
    mut v_b_705_: *mut crate::leanh::LeanObject,
    mut v_flushEagerly_706_: *mut crate::leanh::LeanObject,
    mut v___y_707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_flushEagerly_boxed_708_: u8 = 0;
    let mut v_res_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_flushEagerly_boxed_708_ = (crate::leanh::lean_unbox(v_flushEagerly_706_) as u8);
    v_res_709_ =
        l_IO_FS_Stream_chainRight___lam__1(v_getLine_704_, v_b_705_, v_flushEagerly_boxed_708_);
    return v_res_709_;
}
pub unsafe fn l_IO_FS_Stream_chainRight___lam__2(
    mut v_flush_710_: *mut crate::leanh::LeanObject,
    mut v_b_711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_713_ = crate::leanh::lean_apply_1(v_flush_710_, crate::leanh::lean_box(0));
    if crate::leanh::lean_obj_tag(v___x_713_) == 0 {
        let mut v_flush_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_713_, 1);
        v_flush_714_ = crate::leanh::lean_ctor_get(v_b_711_, 0);
        crate::leanh::lean_inc_ref(v_flush_714_);
        crate::leanh::lean_dec_ref(v_b_711_);
        v___x_715_ = crate::leanh::lean_apply_1(v_flush_714_, crate::leanh::lean_box(0));
        return v___x_715_;
    } else {
        crate::leanh::lean_dec_ref(v_b_711_);
        return v___x_713_;
    }
}
pub unsafe fn l_IO_FS_Stream_chainRight___lam__2___boxed(
    mut v_flush_716_: *mut crate::leanh::LeanObject,
    mut v_b_717_: *mut crate::leanh::LeanObject,
    mut v___y_718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_719_ = l_IO_FS_Stream_chainRight___lam__2(v_flush_716_, v_b_717_);
    return v_res_719_;
}
pub unsafe fn l_IO_FS_Stream_chainRight(
    mut v_a_720_: *mut crate::leanh::LeanObject,
    mut v_b_721_: *mut crate::leanh::LeanObject,
    mut v_flushEagerly_722_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_flush_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_read_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_write_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLine_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isTty_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_731_: u8 = 0;
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_740_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_flush_723_ = crate::leanh::lean_ctor_get(v_a_720_, 0);
                v_read_724_ = crate::leanh::lean_ctor_get(v_a_720_, 1);
                v_write_725_ = crate::leanh::lean_ctor_get(v_a_720_, 2);
                v_getLine_726_ = crate::leanh::lean_ctor_get(v_a_720_, 3);
                v_putStr_727_ = crate::leanh::lean_ctor_get(v_a_720_, 4);
                v_isTty_728_ = crate::leanh::lean_ctor_get(v_a_720_, 5);
                v_isSharedCheck_740_ = (!crate::leanh::lean_is_exclusive(v_a_720_)) as u8;
                if v_isSharedCheck_740_ == 0 {
                    v___x_730_ = v_a_720_;
                    v_isShared_731_ = v_isSharedCheck_740_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_isTty_728_);
                    crate::leanh::lean_inc(v_putStr_727_);
                    crate::leanh::lean_inc(v_getLine_726_);
                    crate::leanh::lean_inc(v_write_725_);
                    crate::leanh::lean_inc(v_read_724_);
                    crate::leanh::lean_inc(v_flush_723_);
                    crate::leanh::lean_dec(v_a_720_);
                    v___x_730_ = crate::leanh::lean_box(0);
                    v_isShared_731_ = v_isSharedCheck_740_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_732_ = crate::leanh::lean_box((v_flushEagerly_722_) as usize);
                crate::leanh::lean_inc_ref_n(v_b_721_, 2);
                v___f_733_ = crate::leanh::lean_alloc_closure(
                    l_IO_FS_Stream_chainRight___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_733_, 0, v_read_724_);
                crate::leanh::lean_closure_set(v___f_733_, 1, v_b_721_);
                crate::leanh::lean_closure_set(v___f_733_, 2, v___x_732_);
                v___x_734_ = crate::leanh::lean_box((v_flushEagerly_722_) as usize);
                v___f_735_ = crate::leanh::lean_alloc_closure(
                    l_IO_FS_Stream_chainRight___lam__1___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_735_, 0, v_getLine_726_);
                crate::leanh::lean_closure_set(v___f_735_, 1, v_b_721_);
                crate::leanh::lean_closure_set(v___f_735_, 2, v___x_734_);
                v___f_736_ = crate::leanh::lean_alloc_closure(
                    l_IO_FS_Stream_chainRight___lam__2___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_736_, 0, v_flush_723_);
                crate::leanh::lean_closure_set(v___f_736_, 1, v_b_721_);
                if v_isShared_731_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_730_, 3, v___f_735_);
                    crate::leanh::lean_ctor_set(v___x_730_, 1, v___f_733_);
                    crate::leanh::lean_ctor_set(v___x_730_, 0, v___f_736_);
                    v___x_738_ = v___x_730_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_739_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_739_, 0, v___f_736_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_739_, 1, v___f_733_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_739_, 2, v_write_725_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_739_, 3, v___f_735_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_739_, 4, v_putStr_727_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_739_, 5, v_isTty_728_);
                    v___x_738_ = v_reuseFailAlloc_739_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_738_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_chainRight___boxed(
    mut v_a_741_: *mut crate::leanh::LeanObject,
    mut v_b_742_: *mut crate::leanh::LeanObject,
    mut v_flushEagerly_743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_flushEagerly_boxed_744_: u8 = 0;
    let mut v_res_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_flushEagerly_boxed_744_ = (crate::leanh::lean_unbox(v_flushEagerly_743_) as u8);
    v_res_745_ = l_IO_FS_Stream_chainRight(v_a_741_, v_b_742_, v_flushEagerly_boxed_744_);
    return v_res_745_;
}
pub unsafe fn l_IO_FS_Stream_chainLeft___lam__0(
    mut v_flush_746_: *mut crate::leanh::LeanObject,
    mut v_flush_747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_749_ = crate::leanh::lean_apply_1(v_flush_746_, crate::leanh::lean_box(0));
    if crate::leanh::lean_obj_tag(v___x_749_) == 0 {
        let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_749_, 1);
        v___x_750_ = crate::leanh::lean_apply_1(v_flush_747_, crate::leanh::lean_box(0));
        return v___x_750_;
    } else {
        crate::leanh::lean_dec_ref(v_flush_747_);
        return v___x_749_;
    }
}
pub unsafe fn l_IO_FS_Stream_chainLeft___lam__0___boxed(
    mut v_flush_751_: *mut crate::leanh::LeanObject,
    mut v_flush_752_: *mut crate::leanh::LeanObject,
    mut v___y_753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_754_ = l_IO_FS_Stream_chainLeft___lam__0(v_flush_751_, v_flush_752_);
    return v_res_754_;
}
pub unsafe fn l_IO_FS_Stream_chainLeft___lam__1(
    mut v_write_755_: *mut crate::leanh::LeanObject,
    mut v_flushEagerly_756_: u8,
    mut v_write_757_: *mut crate::leanh::LeanObject,
    mut v_flush_758_: *mut crate::leanh::LeanObject,
    mut v_bs_759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_bs_759_);
    v___x_761_ = crate::leanh::lean_apply_2(v_write_755_, v_bs_759_, crate::leanh::lean_box(0));
    if crate::leanh::lean_obj_tag(v___x_761_) == 0 {
        crate::leanh::lean_dec_ref_known(v___x_761_, 1);
        if v_flushEagerly_756_ == 0 {
            let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_flush_758_);
            v___x_762_ =
                crate::leanh::lean_apply_2(v_write_757_, v_bs_759_, crate::leanh::lean_box(0));
            return v___x_762_;
        } else {
            let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_763_ = crate::leanh::lean_apply_1(v_flush_758_, crate::leanh::lean_box(0));
            if crate::leanh::lean_obj_tag(v___x_763_) == 0 {
                let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref_known(v___x_763_, 1);
                v___x_764_ =
                    crate::leanh::lean_apply_2(v_write_757_, v_bs_759_, crate::leanh::lean_box(0));
                return v___x_764_;
            } else {
                crate::leanh::lean_dec_ref(v_bs_759_);
                crate::leanh::lean_dec_ref(v_write_757_);
                return v___x_763_;
            }
        }
    } else {
        crate::leanh::lean_dec_ref(v_bs_759_);
        crate::leanh::lean_dec_ref(v_flush_758_);
        crate::leanh::lean_dec_ref(v_write_757_);
        return v___x_761_;
    }
}
pub unsafe fn l_IO_FS_Stream_chainLeft___lam__1___boxed(
    mut v_write_765_: *mut crate::leanh::LeanObject,
    mut v_flushEagerly_766_: *mut crate::leanh::LeanObject,
    mut v_write_767_: *mut crate::leanh::LeanObject,
    mut v_flush_768_: *mut crate::leanh::LeanObject,
    mut v_bs_769_: *mut crate::leanh::LeanObject,
    mut v___y_770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_flushEagerly_boxed_771_: u8 = 0;
    let mut v_res_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_flushEagerly_boxed_771_ = (crate::leanh::lean_unbox(v_flushEagerly_766_) as u8);
    v_res_772_ = l_IO_FS_Stream_chainLeft___lam__1(
        v_write_765_,
        v_flushEagerly_boxed_771_,
        v_write_767_,
        v_flush_768_,
        v_bs_769_,
    );
    return v_res_772_;
}
pub unsafe fn l_IO_FS_Stream_chainLeft___lam__2(
    mut v_putStr_773_: *mut crate::leanh::LeanObject,
    mut v_flushEagerly_774_: u8,
    mut v_putStr_775_: *mut crate::leanh::LeanObject,
    mut v_flush_776_: *mut crate::leanh::LeanObject,
    mut v_s_777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_s_777_);
    v___x_779_ = crate::leanh::lean_apply_2(v_putStr_773_, v_s_777_, crate::leanh::lean_box(0));
    if crate::leanh::lean_obj_tag(v___x_779_) == 0 {
        crate::leanh::lean_dec_ref_known(v___x_779_, 1);
        if v_flushEagerly_774_ == 0 {
            let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_flush_776_);
            v___x_780_ =
                crate::leanh::lean_apply_2(v_putStr_775_, v_s_777_, crate::leanh::lean_box(0));
            return v___x_780_;
        } else {
            let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_781_ = crate::leanh::lean_apply_1(v_flush_776_, crate::leanh::lean_box(0));
            if crate::leanh::lean_obj_tag(v___x_781_) == 0 {
                let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref_known(v___x_781_, 1);
                v___x_782_ =
                    crate::leanh::lean_apply_2(v_putStr_775_, v_s_777_, crate::leanh::lean_box(0));
                return v___x_782_;
            } else {
                crate::leanh::lean_dec_ref(v_s_777_);
                crate::leanh::lean_dec_ref(v_putStr_775_);
                return v___x_781_;
            }
        }
    } else {
        crate::leanh::lean_dec_ref(v_s_777_);
        crate::leanh::lean_dec_ref(v_flush_776_);
        crate::leanh::lean_dec_ref(v_putStr_775_);
        return v___x_779_;
    }
}
pub unsafe fn l_IO_FS_Stream_chainLeft___lam__2___boxed(
    mut v_putStr_783_: *mut crate::leanh::LeanObject,
    mut v_flushEagerly_784_: *mut crate::leanh::LeanObject,
    mut v_putStr_785_: *mut crate::leanh::LeanObject,
    mut v_flush_786_: *mut crate::leanh::LeanObject,
    mut v_s_787_: *mut crate::leanh::LeanObject,
    mut v___y_788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_flushEagerly_boxed_789_: u8 = 0;
    let mut v_res_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_flushEagerly_boxed_789_ = (crate::leanh::lean_unbox(v_flushEagerly_784_) as u8);
    v_res_790_ = l_IO_FS_Stream_chainLeft___lam__2(
        v_putStr_783_,
        v_flushEagerly_boxed_789_,
        v_putStr_785_,
        v_flush_786_,
        v_s_787_,
    );
    return v_res_790_;
}
pub unsafe fn l_IO_FS_Stream_chainLeft(
    mut v_a_791_: *mut crate::leanh::LeanObject,
    mut v_b_792_: *mut crate::leanh::LeanObject,
    mut v_flushEagerly_793_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_flush_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_write_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_flush_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_read_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_write_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLine_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isTty_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_805_: u8 = 0;
    let mut v___f_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_814_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_flush_794_ = crate::leanh::lean_ctor_get(v_a_791_, 0);
                crate::leanh::lean_inc_ref(v_flush_794_);
                v_write_795_ = crate::leanh::lean_ctor_get(v_a_791_, 2);
                crate::leanh::lean_inc_ref(v_write_795_);
                v_putStr_796_ = crate::leanh::lean_ctor_get(v_a_791_, 4);
                crate::leanh::lean_inc_ref(v_putStr_796_);
                crate::leanh::lean_dec_ref(v_a_791_);
                v_flush_797_ = crate::leanh::lean_ctor_get(v_b_792_, 0);
                v_read_798_ = crate::leanh::lean_ctor_get(v_b_792_, 1);
                v_write_799_ = crate::leanh::lean_ctor_get(v_b_792_, 2);
                v_getLine_800_ = crate::leanh::lean_ctor_get(v_b_792_, 3);
                v_putStr_801_ = crate::leanh::lean_ctor_get(v_b_792_, 4);
                v_isTty_802_ = crate::leanh::lean_ctor_get(v_b_792_, 5);
                v_isSharedCheck_814_ = (!crate::leanh::lean_is_exclusive(v_b_792_)) as u8;
                if v_isSharedCheck_814_ == 0 {
                    v___x_804_ = v_b_792_;
                    v_isShared_805_ = v_isSharedCheck_814_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_isTty_802_);
                    crate::leanh::lean_inc(v_putStr_801_);
                    crate::leanh::lean_inc(v_getLine_800_);
                    crate::leanh::lean_inc(v_write_799_);
                    crate::leanh::lean_inc(v_read_798_);
                    crate::leanh::lean_inc(v_flush_797_);
                    crate::leanh::lean_dec(v_b_792_);
                    v___x_804_ = crate::leanh::lean_box(0);
                    v_isShared_805_ = v_isSharedCheck_814_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref_n(v_flush_794_, 2);
                v___f_806_ = crate::leanh::lean_alloc_closure(
                    l_IO_FS_Stream_chainLeft___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_806_, 0, v_flush_794_);
                crate::leanh::lean_closure_set(v___f_806_, 1, v_flush_797_);
                v___x_807_ = crate::leanh::lean_box((v_flushEagerly_793_) as usize);
                v___f_808_ = crate::leanh::lean_alloc_closure(
                    l_IO_FS_Stream_chainLeft___lam__1___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_808_, 0, v_write_795_);
                crate::leanh::lean_closure_set(v___f_808_, 1, v___x_807_);
                crate::leanh::lean_closure_set(v___f_808_, 2, v_write_799_);
                crate::leanh::lean_closure_set(v___f_808_, 3, v_flush_794_);
                v___x_809_ = crate::leanh::lean_box((v_flushEagerly_793_) as usize);
                v___f_810_ = crate::leanh::lean_alloc_closure(
                    l_IO_FS_Stream_chainLeft___lam__2___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_810_, 0, v_putStr_796_);
                crate::leanh::lean_closure_set(v___f_810_, 1, v___x_809_);
                crate::leanh::lean_closure_set(v___f_810_, 2, v_putStr_801_);
                crate::leanh::lean_closure_set(v___f_810_, 3, v_flush_794_);
                if v_isShared_805_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_804_, 4, v___f_810_);
                    crate::leanh::lean_ctor_set(v___x_804_, 2, v___f_808_);
                    crate::leanh::lean_ctor_set(v___x_804_, 0, v___f_806_);
                    v___x_812_ = v___x_804_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_813_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_813_, 0, v___f_806_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_813_, 1, v_read_798_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_813_, 2, v___f_808_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_813_, 3, v_getLine_800_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_813_, 4, v___f_810_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_813_, 5, v_isTty_802_);
                    v___x_812_ = v_reuseFailAlloc_813_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_812_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_chainLeft___boxed(
    mut v_a_815_: *mut crate::leanh::LeanObject,
    mut v_b_816_: *mut crate::leanh::LeanObject,
    mut v_flushEagerly_817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_flushEagerly_boxed_818_: u8 = 0;
    let mut v_res_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_flushEagerly_boxed_818_ = (crate::leanh::lean_unbox(v_flushEagerly_817_) as u8);
    v_res_819_ = l_IO_FS_Stream_chainLeft(v_a_815_, v_b_816_, v_flushEagerly_boxed_818_);
    return v_res_819_;
}
pub unsafe fn l_IO_FS_Stream_withPrefix___lam__0(
    mut v_putStr_820_: *mut crate::leanh::LeanObject,
    mut v_pre_821_: *mut crate::leanh::LeanObject,
    mut v_write_822_: *mut crate::leanh::LeanObject,
    mut v_bs_823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_825_ = crate::leanh::lean_apply_2(v_putStr_820_, v_pre_821_, crate::leanh::lean_box(0));
    if crate::leanh::lean_obj_tag(v___x_825_) == 0 {
        let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_825_, 1);
        v___x_826_ = crate::leanh::lean_apply_2(v_write_822_, v_bs_823_, crate::leanh::lean_box(0));
        return v___x_826_;
    } else {
        crate::leanh::lean_dec_ref(v_bs_823_);
        crate::leanh::lean_dec_ref(v_write_822_);
        return v___x_825_;
    }
}
pub unsafe fn l_IO_FS_Stream_withPrefix___lam__0___boxed(
    mut v_putStr_827_: *mut crate::leanh::LeanObject,
    mut v_pre_828_: *mut crate::leanh::LeanObject,
    mut v_write_829_: *mut crate::leanh::LeanObject,
    mut v_bs_830_: *mut crate::leanh::LeanObject,
    mut v___y_831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_832_ =
        l_IO_FS_Stream_withPrefix___lam__0(v_putStr_827_, v_pre_828_, v_write_829_, v_bs_830_);
    return v_res_832_;
}
pub unsafe fn l_IO_FS_Stream_withPrefix___lam__1(
    mut v_pre_833_: *mut crate::leanh::LeanObject,
    mut v_putStr_834_: *mut crate::leanh::LeanObject,
    mut v_s_835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_837_ = lean_string_append(v_pre_833_, v_s_835_);
    v___x_838_ = crate::leanh::lean_apply_2(v_putStr_834_, v___x_837_, crate::leanh::lean_box(0));
    return v___x_838_;
}
pub unsafe fn l_IO_FS_Stream_withPrefix___lam__1___boxed(
    mut v_pre_839_: *mut crate::leanh::LeanObject,
    mut v_putStr_840_: *mut crate::leanh::LeanObject,
    mut v_s_841_: *mut crate::leanh::LeanObject,
    mut v___y_842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_843_ = l_IO_FS_Stream_withPrefix___lam__1(v_pre_839_, v_putStr_840_, v_s_841_);
    crate::leanh::lean_dec_ref(v_s_841_);
    return v_res_843_;
}
pub unsafe fn l_IO_FS_Stream_withPrefix(
    mut v_a_844_: *mut crate::leanh::LeanObject,
    mut v_pre_845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_flush_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_read_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_write_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLine_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isTty_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_854_: u8 = 0;
    let mut v___f_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_860_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_flush_846_ = crate::leanh::lean_ctor_get(v_a_844_, 0);
                v_read_847_ = crate::leanh::lean_ctor_get(v_a_844_, 1);
                v_write_848_ = crate::leanh::lean_ctor_get(v_a_844_, 2);
                v_getLine_849_ = crate::leanh::lean_ctor_get(v_a_844_, 3);
                v_putStr_850_ = crate::leanh::lean_ctor_get(v_a_844_, 4);
                v_isTty_851_ = crate::leanh::lean_ctor_get(v_a_844_, 5);
                v_isSharedCheck_860_ = (!crate::leanh::lean_is_exclusive(v_a_844_)) as u8;
                if v_isSharedCheck_860_ == 0 {
                    v___x_853_ = v_a_844_;
                    v_isShared_854_ = v_isSharedCheck_860_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_isTty_851_);
                    crate::leanh::lean_inc(v_putStr_850_);
                    crate::leanh::lean_inc(v_getLine_849_);
                    crate::leanh::lean_inc(v_write_848_);
                    crate::leanh::lean_inc(v_read_847_);
                    crate::leanh::lean_inc(v_flush_846_);
                    crate::leanh::lean_dec(v_a_844_);
                    v___x_853_ = crate::leanh::lean_box(0);
                    v_isShared_854_ = v_isSharedCheck_860_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_pre_845_);
                crate::leanh::lean_inc_ref(v_putStr_850_);
                v___f_855_ = crate::leanh::lean_alloc_closure(
                    l_IO_FS_Stream_withPrefix___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_855_, 0, v_putStr_850_);
                crate::leanh::lean_closure_set(v___f_855_, 1, v_pre_845_);
                crate::leanh::lean_closure_set(v___f_855_, 2, v_write_848_);
                v___f_856_ = crate::leanh::lean_alloc_closure(
                    l_IO_FS_Stream_withPrefix___lam__1___boxed as *mut core::ffi::c_void,
                    4,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_856_, 0, v_pre_845_);
                crate::leanh::lean_closure_set(v___f_856_, 1, v_putStr_850_);
                if v_isShared_854_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_853_, 4, v___f_856_);
                    crate::leanh::lean_ctor_set(v___x_853_, 2, v___f_855_);
                    v___x_858_ = v___x_853_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_859_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_859_, 0, v_flush_846_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_859_, 1, v_read_847_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_859_, 2, v___f_855_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_859_, 3, v_getLine_849_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_859_, 4, v___f_856_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_859_, 5, v_isTty_851_);
                    v___x_858_ = v_reuseFailAlloc_859_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_858_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Server_instInhabitedDocumentMeta_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_862_: u8 = 0;
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_862_ = 0;
    v___x_863_ = l_Lean_instInhabitedFileMap_default;
    v___x_864_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_865_ = crate::leanh::lean_box(0);
    v___x_866_ = l_Lean_Server_instInhabitedDocumentMeta_default___closed__0;
    v___x_867_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_867_, 0, v___x_866_);
    crate::leanh::lean_ctor_set(v___x_867_, 1, v___x_865_);
    crate::leanh::lean_ctor_set(v___x_867_, 2, v___x_864_);
    crate::leanh::lean_ctor_set(v___x_867_, 3, v___x_863_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_867_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
        v___x_862_,
    );
    return v___x_867_;
}
pub unsafe fn _init_l_Lean_Server_instInhabitedDocumentMeta_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_868_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_instInhabitedDocumentMeta_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Server_instInhabitedDocumentMeta_default___closed__1_once),
        _init_l_Lean_Server_instInhabitedDocumentMeta_default___closed__1,
    );
    return v___x_868_;
}
pub unsafe fn _init_l_Lean_Server_instInhabitedDocumentMeta() -> *mut crate::leanh::LeanObject {
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_869_ = l_Lean_Server_instInhabitedDocumentMeta_default;
    return v___x_869_;
}
pub unsafe fn l_Lean_Server_DocumentMeta_mkInputContext(
    mut v_doc_870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_text_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uri_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_text_871_ = crate::leanh::lean_ctor_get(v_doc_870_, 3);
                crate::leanh::lean_inc_ref(v_text_871_);
                v_uri_872_ = crate::leanh::lean_ctor_get(v_doc_870_, 0);
                crate::leanh::lean_inc_ref(v_uri_872_);
                crate::leanh::lean_dec_ref(v_doc_870_);
                v_source_873_ = crate::leanh::lean_ctor_get(v_text_871_, 0);
                crate::leanh::lean_inc_ref(v_source_873_);
                v___x_878_ = l_System_Uri_fileUriToPath_x3f(v_uri_872_);
                if crate::leanh::lean_obj_tag(v___x_878_) == 0 {
                    v___y_875_ = v_uri_872_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_uri_872_);
                    v_val_879_ = crate::leanh::lean_ctor_get(v___x_878_, 0);
                    crate::leanh::lean_inc(v_val_879_);
                    crate::leanh::lean_dec_ref_known(v___x_878_, 1);
                    v___y_875_ = v_val_879_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_876_ = lean_string_utf8_byte_size(v_source_873_);
                v___x_877_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_877_, 0, v_source_873_);
                crate::leanh::lean_ctor_set(v___x_877_, 1, v___y_875_);
                crate::leanh::lean_ctor_set(v___x_877_, 2, v_text_871_);
                crate::leanh::lean_ctor_set(v___x_877_, 3, v___x_876_);
                return v___x_877_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_replaceLspRange(
    mut v_text_880_: *mut crate::leanh::LeanObject,
    mut v_r_881_: *mut crate::leanh::LeanObject,
    mut v_newText_882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_end_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_end_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_post_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_start_883_ = crate::leanh::lean_ctor_get(v_r_881_, 0);
    crate::leanh::lean_inc_ref(v_start_883_);
    v_end_884_ = crate::leanh::lean_ctor_get(v_r_881_, 1);
    crate::leanh::lean_inc_ref(v_end_884_);
    crate::leanh::lean_dec_ref(v_r_881_);
    v_source_885_ = crate::leanh::lean_ctor_get(v_text_880_, 0);
    v_start_886_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_880_, v_start_883_);
    v_end_887_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_880_, v_end_884_);
    v___x_888_ = crate::leanh::lean_unsigned_to_nat(0);
    v_pre_889_ = lean_string_utf8_extract(v_source_885_, v___x_888_, v_start_886_);
    crate::leanh::lean_dec(v_start_886_);
    v___x_890_ = lean_string_utf8_byte_size(v_source_885_);
    v_post_891_ = lean_string_utf8_extract(v_source_885_, v_end_887_, v___x_890_);
    crate::leanh::lean_dec(v_end_887_);
    v___x_892_ = l_String_crlfToLf(v_newText_882_);
    v___x_893_ = lean_string_append(v_pre_889_, v___x_892_);
    crate::leanh::lean_dec_ref(v___x_892_);
    v___x_894_ = lean_string_append(v___x_893_, v_post_891_);
    crate::leanh::lean_dec_ref(v_post_891_);
    v___x_895_ = l_String_toFileMap(v___x_894_);
    return v___x_895_;
}
pub unsafe fn l_Lean_Server_replaceLspRange___boxed(
    mut v_text_896_: *mut crate::leanh::LeanObject,
    mut v_r_897_: *mut crate::leanh::LeanObject,
    mut v_newText_898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_899_ = l_Lean_Server_replaceLspRange(v_text_896_, v_r_897_, v_newText_898_);
    crate::leanh::lean_dec_ref(v_newText_898_);
    crate::leanh::lean_dec_ref(v_text_896_);
    return v_res_899_;
}
pub unsafe fn l_Lean_Server_applyDocumentChange(
    mut v_oldText_900_: *mut crate::leanh::LeanObject,
    mut v_x_901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_901_) == 0 {
        let mut v_range_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_text_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_range_902_ = crate::leanh::lean_ctor_get(v_x_901_, 0);
        crate::leanh::lean_inc_ref(v_range_902_);
        v_text_903_ = crate::leanh::lean_ctor_get(v_x_901_, 1);
        crate::leanh::lean_inc_ref(v_text_903_);
        crate::leanh::lean_dec_ref_known(v_x_901_, 2);
        v___x_904_ = l_Lean_Server_replaceLspRange(v_oldText_900_, v_range_902_, v_text_903_);
        crate::leanh::lean_dec_ref(v_text_903_);
        return v___x_904_;
    } else {
        let mut v_text_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_text_905_ = crate::leanh::lean_ctor_get(v_x_901_, 0);
        crate::leanh::lean_inc_ref(v_text_905_);
        crate::leanh::lean_dec_ref_known(v_x_901_, 1);
        v___x_906_ = l_String_crlfToLf(v_text_905_);
        crate::leanh::lean_dec_ref(v_text_905_);
        v___x_907_ = l_String_toFileMap(v___x_906_);
        return v___x_907_;
    }
}
pub unsafe fn l_Lean_Server_applyDocumentChange___boxed(
    mut v_oldText_908_: *mut crate::leanh::LeanObject,
    mut v_x_909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_910_ = l_Lean_Server_applyDocumentChange(v_oldText_908_, v_x_909_);
    crate::leanh::lean_dec_ref(v_oldText_908_);
    return v_res_910_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0(
    mut v_as_911_: *mut crate::leanh::LeanObject,
    mut v_i_912_: usize,
    mut v_stop_913_: usize,
    mut v_b_914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_915_: u8 = 0;
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: usize = 0;
    let mut v___x_919_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_915_ = lean_usize_dec_eq(v_i_912_, v_stop_913_);
                if v___x_915_ == 0 {
                    v___x_916_ = lean_array_uget_borrowed(v_as_911_, v_i_912_);
                    crate::leanh::lean_inc(v___x_916_);
                    v___x_917_ = l_Lean_Server_applyDocumentChange(v_b_914_, v___x_916_);
                    crate::leanh::lean_dec_ref(v_b_914_);
                    v___x_918_ = 1usize;
                    v___x_919_ = lean_usize_add(v_i_912_, v___x_918_);
                    v_i_912_ = v___x_919_;
                    v_b_914_ = v___x_917_;
                    state = 0;
                    continue;
                } else {
                    return v_b_914_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0___boxed(
    mut v_as_921_: *mut crate::leanh::LeanObject,
    mut v_i_922_: *mut crate::leanh::LeanObject,
    mut v_stop_923_: *mut crate::leanh::LeanObject,
    mut v_b_924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_925_: usize = 0;
    let mut v_stop_boxed_926_: usize = 0;
    let mut v_res_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_925_ = crate::leanh::lean_unbox_usize(v_i_922_);
    crate::leanh::lean_dec(v_i_922_);
    v_stop_boxed_926_ = crate::leanh::lean_unbox_usize(v_stop_923_);
    crate::leanh::lean_dec(v_stop_923_);
    v_res_927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0(v_as_921_, v_i_boxed_925_, v_stop_boxed_926_, v_b_924_);
    crate::leanh::lean_dec_ref(v_as_921_);
    return v_res_927_;
}
pub unsafe fn l_Lean_Server_foldDocumentChanges(
    mut v_changes_928_: *mut crate::leanh::LeanObject,
    mut v_oldText_929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: u8 = 0;
    v___x_930_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_931_ = lean_array_get_size(v_changes_928_);
    v___x_932_ = lean_nat_dec_lt(v___x_930_, v___x_931_);
    if v___x_932_ == 0 {
        return v_oldText_929_;
    } else {
        let mut v___x_933_: u8 = 0;
        v___x_933_ = lean_nat_dec_le(v___x_931_, v___x_931_);
        if v___x_933_ == 0 {
            if v___x_932_ == 0 {
                return v_oldText_929_;
            } else {
                let mut v___x_934_: usize = 0;
                let mut v___x_935_: usize = 0;
                let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_934_ = 0usize;
                v___x_935_ = lean_usize_of_nat(v___x_931_);
                v___x_936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0(v_changes_928_, v___x_934_, v___x_935_, v_oldText_929_);
                return v___x_936_;
            }
        } else {
            let mut v___x_937_: usize = 0;
            let mut v___x_938_: usize = 0;
            let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_937_ = 0usize;
            v___x_938_ = lean_usize_of_nat(v___x_931_);
            v___x_939_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0(v_changes_928_, v___x_937_, v___x_938_, v_oldText_929_);
            return v___x_939_;
        }
    }
}
pub unsafe fn l_Lean_Server_foldDocumentChanges___boxed(
    mut v_changes_940_: *mut crate::leanh::LeanObject,
    mut v_oldText_941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_942_ = l_Lean_Server_foldDocumentChanges(v_changes_940_, v_oldText_941_);
    crate::leanh::lean_dec_ref(v_changes_940_);
    return v_res_942_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Server_mkPublishDiagnosticsNotification_spec__0(
    mut v_a_943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_944_ = lean_nat_to_int(v_a_943_);
    return v___x_944_;
}
pub unsafe fn l_Lean_Server_mkPublishDiagnosticsNotification(
    mut v_m_946_: *mut crate::leanh::LeanObject,
    mut v_diagnostics_947_: *mut crate::leanh::LeanObject,
    mut v_isIncremental_948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_uri_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_uri_949_ = crate::leanh::lean_ctor_get(v_m_946_, 0);
    crate::leanh::lean_inc_ref(v_uri_949_);
    v_version_950_ = crate::leanh::lean_ctor_get(v_m_946_, 2);
    crate::leanh::lean_inc(v_version_950_);
    crate::leanh::lean_dec_ref(v_m_946_);
    v___x_951_ = l_Lean_Server_mkPublishDiagnosticsNotification___closed__0;
    v___x_952_ = lean_nat_to_int(v_version_950_);
    v___x_953_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_953_, 0, v___x_952_);
    v___x_954_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_954_, 0, v_uri_949_);
    crate::leanh::lean_ctor_set(v___x_954_, 1, v___x_953_);
    crate::leanh::lean_ctor_set(v___x_954_, 2, v_isIncremental_948_);
    crate::leanh::lean_ctor_set(v___x_954_, 3, v_diagnostics_947_);
    v___x_955_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_955_, 0, v___x_951_);
    crate::leanh::lean_ctor_set(v___x_955_, 1, v___x_954_);
    return v___x_955_;
}
pub unsafe fn l_Lean_Server_mkFileProgressNotification(
    mut v_m_957_: *mut crate::leanh::LeanObject,
    mut v_processing_958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_uri_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_uri_959_ = crate::leanh::lean_ctor_get(v_m_957_, 0);
    v_version_960_ = crate::leanh::lean_ctor_get(v_m_957_, 2);
    v___x_961_ = l_Lean_Server_mkFileProgressNotification___closed__0;
    crate::leanh::lean_inc(v_version_960_);
    v___x_962_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_962_, 0, v_version_960_);
    crate::leanh::lean_inc_ref(v_uri_959_);
    v___x_963_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_963_, 0, v_uri_959_);
    crate::leanh::lean_ctor_set(v___x_963_, 1, v___x_962_);
    v___x_964_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_964_, 0, v___x_963_);
    crate::leanh::lean_ctor_set(v___x_964_, 1, v_processing_958_);
    v___x_965_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_965_, 0, v___x_961_);
    crate::leanh::lean_ctor_set(v___x_965_, 1, v___x_964_);
    return v___x_965_;
}
pub unsafe fn l_Lean_Server_mkFileProgressNotification___boxed(
    mut v_m_966_: *mut crate::leanh::LeanObject,
    mut v_processing_967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_968_ = l_Lean_Server_mkFileProgressNotification(v_m_966_, v_processing_967_);
    crate::leanh::lean_dec_ref(v_m_966_);
    return v_res_968_;
}
pub unsafe fn l_Lean_Server_mkFileProgressAtPosNotification(
    mut v_m_969_: *mut crate::leanh::LeanObject,
    mut v_pos_970_: *mut crate::leanh::LeanObject,
    mut v_kind_971_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_text_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_text_972_ = crate::leanh::lean_ctor_get(v_m_969_, 3);
    v_source_973_ = crate::leanh::lean_ctor_get(v_text_972_, 0);
    crate::leanh::lean_inc_ref_n(v_text_972_, 2);
    v___x_974_ = l_Lean_FileMap_utf8PosToLspPos(v_text_972_, v_pos_970_);
    v___x_975_ = lean_string_utf8_byte_size(v_source_973_);
    v___x_976_ = l_Lean_FileMap_utf8PosToLspPos(v_text_972_, v___x_975_);
    v___x_977_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_977_, 0, v___x_974_);
    crate::leanh::lean_ctor_set(v___x_977_, 1, v___x_976_);
    v___x_978_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_978_, 0, v___x_977_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_978_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v_kind_971_,
    );
    v___x_979_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_980_ = lean_mk_empty_array_with_capacity(v___x_979_);
    v___x_981_ = lean_array_push(v___x_980_, v___x_978_);
    v___x_982_ = l_Lean_Server_mkFileProgressNotification(v_m_969_, v___x_981_);
    crate::leanh::lean_dec_ref(v_m_969_);
    return v___x_982_;
}
pub unsafe fn l_Lean_Server_mkFileProgressAtPosNotification___boxed(
    mut v_m_983_: *mut crate::leanh::LeanObject,
    mut v_pos_984_: *mut crate::leanh::LeanObject,
    mut v_kind_985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_986_: u8 = 0;
    let mut v_res_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_986_ = (crate::leanh::lean_unbox(v_kind_985_) as u8);
    v_res_987_ =
        l_Lean_Server_mkFileProgressAtPosNotification(v_m_983_, v_pos_984_, v_kind_boxed_986_);
    crate::leanh::lean_dec(v_pos_984_);
    return v_res_987_;
}
pub unsafe fn l_Lean_Server_mkFileProgressDoneNotification(
    mut v_m_990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_991_ = l_Lean_Server_mkFileProgressDoneNotification___closed__0;
    v___x_992_ = l_Lean_Server_mkFileProgressNotification(v_m_990_, v___x_991_);
    return v___x_992_;
}
pub unsafe fn l_Lean_Server_mkFileProgressDoneNotification___boxed(
    mut v_m_993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_994_ = l_Lean_Server_mkFileProgressDoneNotification(v_m_993_);
    crate::leanh::lean_dec_ref(v_m_993_);
    return v_res_994_;
}
pub unsafe fn l_Lean_Server_mkApplyWorkspaceEditRequest(
    mut v_params_998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_999_ = l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0;
    v___x_1000_ = l_Lean_Server_mkApplyWorkspaceEditRequest___closed__1;
    v___x_1001_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1001_, 0, v___x_1000_);
    crate::leanh::lean_ctor_set(v___x_1001_, 1, v___x_999_);
    crate::leanh::lean_ctor_set(v___x_1001_, 2, v_params_998_);
    return v___x_1001_;
}
pub unsafe fn l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(
    mut v_uri_1003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1004_ = crate::leanh::lean_box(0);
    v___x_1005_ = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0;
    v___x_1006_ = lean_string_append(v___x_1005_, v_uri_1003_);
    v___x_1007_ = l_Lean_Name_str___override(v___x_1004_, v___x_1006_);
    return v___x_1007_;
}
pub unsafe fn l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___boxed(
    mut v_uri_1008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1009_ = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(v_uri_1008_);
    crate::leanh::lean_dec_ref(v_uri_1008_);
    return v_res_1009_;
}
pub unsafe fn _init_l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1010_ = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0;
    v___x_1011_ = lean_string_utf8_byte_size(v___x_1010_);
    return v___x_1011_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg(
    mut v_s_1012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: u8 = 0;
    v___x_1013_ = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0;
    v___x_1014_ = lean_string_utf8_byte_size(v_s_1012_);
    v___x_1015_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg___closed__0_once), _init_l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg___closed__0);
    v___x_1016_ = lean_nat_dec_le(v___x_1015_, v___x_1014_);
    if v___x_1016_ == 0 {
        let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_s_1012_);
        v___x_1017_ = crate::leanh::lean_box(0);
        return v___x_1017_;
    } else {
        let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1019_: u8 = 0;
        v___x_1018_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1019_ = lean_string_memcmp(
            v_s_1012_,
            v___x_1013_,
            v___x_1018_,
            v___x_1018_,
            v___x_1015_,
        );
        if v___x_1019_ == 0 {
            let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_s_1012_);
            v___x_1020_ = crate::leanh::lean_box(0);
            return v___x_1020_;
        } else {
            let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc_ref(v_s_1012_);
            v___x_1021_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1021_, 0, v_s_1012_);
            crate::leanh::lean_ctor_set(v___x_1021_, 1, v___x_1018_);
            crate::leanh::lean_ctor_set(v___x_1021_, 2, v___x_1014_);
            v___x_1022_ = l_String_Slice_pos_x21(v___x_1021_, v___x_1015_);
            crate::leanh::lean_dec_ref_known(v___x_1021_, 3);
            v___x_1023_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1023_, 0, v_s_1012_);
            crate::leanh::lean_ctor_set(v___x_1023_, 1, v___x_1022_);
            crate::leanh::lean_ctor_set(v___x_1023_, 2, v___x_1014_);
            v___x_1024_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1024_, 0, v___x_1023_);
            return v___x_1024_;
        }
    }
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0(
    mut v_s_1025_: *mut crate::leanh::LeanObject,
    mut v_pat_1026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1027_ = l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg(v_s_1025_);
    return v___x_1027_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___boxed(
    mut v_s_1028_: *mut crate::leanh::LeanObject,
    mut v_pat_1029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1030_ = l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0(v_s_1028_, v_pat_1029_);
    crate::leanh::lean_dec_ref(v_pat_1029_);
    return v_res_1030_;
}
pub unsafe fn l___private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f(
    mut v_name_1031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pre_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1039_: u8 = 0;
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1044_: u8 = 0;
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_name_1031_) == 1 {
                    v_pre_1032_ = crate::leanh::lean_ctor_get(v_name_1031_, 0);
                    if crate::leanh::lean_obj_tag(v_pre_1032_) == 0 {
                        v_str_1033_ = crate::leanh::lean_ctor_get(v_name_1031_, 1);
                        crate::leanh::lean_inc_ref(v_str_1033_);
                        crate::leanh::lean_dec_ref_known(v_name_1031_, 2);
                        v___x_1034_ = l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg(v_str_1033_);
                        if crate::leanh::lean_obj_tag(v___x_1034_) == 0 {
                            v___x_1035_ = crate::leanh::lean_box(0);
                            return v___x_1035_;
                        } else {
                            v_val_1036_ = crate::leanh::lean_ctor_get(v___x_1034_, 0);
                            v_isSharedCheck_1044_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1034_)) as u8;
                            if v_isSharedCheck_1044_ == 0 {
                                v___x_1038_ = v___x_1034_;
                                v_isShared_1039_ = v_isSharedCheck_1044_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_1036_);
                                crate::leanh::lean_dec(v___x_1034_);
                                v___x_1038_ = crate::leanh::lean_box(0);
                                v_isShared_1039_ = v_isSharedCheck_1044_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_name_1031_, 2);
                        v___x_1045_ = crate::leanh::lean_box(0);
                        return v___x_1045_;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_1031_);
                    v___x_1046_ = crate::leanh::lean_box(0);
                    return v___x_1046_;
                }
            }
            1 => {
                v___x_1040_ = l_String_Slice_toString(v_val_1036_);
                crate::leanh::lean_dec(v_val_1036_);
                if v_isShared_1039_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1038_, 0, v___x_1040_);
                    v___x_1042_ = v___x_1038_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1043_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1040_);
                    v___x_1042_ = v_reuseFailAlloc_1043_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1042_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_documentUriFromModule_x3f(
    mut v_modName_1048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1059_: u8 = 0;
    let mut v_val_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1063_: u8 = 0;
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1068_: u8 = 0;
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1076_: u8 = 0;
    let mut v_a_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1080_: u8 = 0;
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1084_: u8 = 0;
    let mut v_isSharedCheck_1085_: u8 = 0;
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1090_: u8 = 0;
    let mut v_a_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1094_: u8 = 0;
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1098_: u8 = 0;
    let mut v_a_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1102_: u8 = 0;
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_modName_1048_);
                v___x_1050_ = l___private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f(
                    v_modName_1048_,
                );
                if crate::leanh::lean_obj_tag(v___x_1050_) == 1 {
                    crate::leanh::lean_dec(v_modName_1048_);
                    v___x_1051_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1051_, 0, v___x_1050_);
                    return v___x_1051_;
                } else {
                    crate::leanh::lean_dec(v___x_1050_);
                    v___x_1052_ = l_Lean_getSrcSearchPath();
                    if crate::leanh::lean_obj_tag(v___x_1052_) == 0 {
                        v_a_1053_ = crate::leanh::lean_ctor_get(v___x_1052_, 0);
                        crate::leanh::lean_inc(v_a_1053_);
                        crate::leanh::lean_dec_ref_known(v___x_1052_, 1);
                        v___x_1054_ = l_Lean_Server_documentUriFromModule_x3f___closed__0;
                        v___x_1055_ = l_Lean_SearchPath_findModuleWithExt(
                            v_a_1053_,
                            v___x_1054_,
                            v_modName_1048_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1055_) == 0 {
                            v_a_1056_ = crate::leanh::lean_ctor_get(v___x_1055_, 0);
                            v_isSharedCheck_1090_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1055_)) as u8;
                            if v_isSharedCheck_1090_ == 0 {
                                v___x_1058_ = v___x_1055_;
                                v_isShared_1059_ = v_isSharedCheck_1090_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1056_);
                                crate::leanh::lean_dec(v___x_1055_);
                                v___x_1058_ = crate::leanh::lean_box(0);
                                v_isShared_1059_ = v_isSharedCheck_1090_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_1091_ = crate::leanh::lean_ctor_get(v___x_1055_, 0);
                            v_isSharedCheck_1098_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1055_)) as u8;
                            if v_isSharedCheck_1098_ == 0 {
                                v___x_1093_ = v___x_1055_;
                                v_isShared_1094_ = v_isSharedCheck_1098_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1091_);
                                crate::leanh::lean_dec(v___x_1055_);
                                v___x_1093_ = crate::leanh::lean_box(0);
                                v_isShared_1094_ = v_isSharedCheck_1098_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_modName_1048_);
                        v_a_1099_ = crate::leanh::lean_ctor_get(v___x_1052_, 0);
                        v_isSharedCheck_1106_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1052_)) as u8;
                        if v_isSharedCheck_1106_ == 0 {
                            v___x_1101_ = v___x_1052_;
                            v_isShared_1102_ = v_isSharedCheck_1106_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1099_);
                            crate::leanh::lean_dec(v___x_1052_);
                            v___x_1101_ = crate::leanh::lean_box(0);
                            v_isShared_1102_ = v_isSharedCheck_1106_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1056_) == 1 {
                    crate::leanh::lean_del_object(v___x_1058_);
                    v_val_1060_ = crate::leanh::lean_ctor_get(v_a_1056_, 0);
                    v_isSharedCheck_1085_ = (!crate::leanh::lean_is_exclusive(v_a_1056_)) as u8;
                    if v_isSharedCheck_1085_ == 0 {
                        v___x_1062_ = v_a_1056_;
                        v_isShared_1063_ = v_isSharedCheck_1085_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1060_);
                        crate::leanh::lean_dec(v_a_1056_);
                        v___x_1062_ = crate::leanh::lean_box(0);
                        v_isShared_1063_ = v_isSharedCheck_1085_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1056_);
                    v___x_1086_ = crate::leanh::lean_box(0);
                    if v_isShared_1059_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1058_, 0, v___x_1086_);
                        v___x_1088_ = v___x_1058_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1089_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
                        v___x_1088_ = v_reuseFailAlloc_1089_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1064_ = lean_io_realpath(v_val_1060_);
                if crate::leanh::lean_obj_tag(v___x_1064_) == 0 {
                    v_a_1065_ = crate::leanh::lean_ctor_get(v___x_1064_, 0);
                    v_isSharedCheck_1076_ = (!crate::leanh::lean_is_exclusive(v___x_1064_)) as u8;
                    if v_isSharedCheck_1076_ == 0 {
                        v___x_1067_ = v___x_1064_;
                        v_isShared_1068_ = v_isSharedCheck_1076_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1065_);
                        crate::leanh::lean_dec(v___x_1064_);
                        v___x_1067_ = crate::leanh::lean_box(0);
                        v_isShared_1068_ = v_isSharedCheck_1076_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1062_);
                    v_a_1077_ = crate::leanh::lean_ctor_get(v___x_1064_, 0);
                    v_isSharedCheck_1084_ = (!crate::leanh::lean_is_exclusive(v___x_1064_)) as u8;
                    if v_isSharedCheck_1084_ == 0 {
                        v___x_1079_ = v___x_1064_;
                        v_isShared_1080_ = v_isSharedCheck_1084_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1077_);
                        crate::leanh::lean_dec(v___x_1064_);
                        v___x_1079_ = crate::leanh::lean_box(0);
                        v_isShared_1080_ = v_isSharedCheck_1084_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1069_ = l_System_Uri_pathToUri(v_a_1065_);
                if v_isShared_1063_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1062_, 0, v___x_1069_);
                    v___x_1071_ = v___x_1062_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1075_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1069_);
                    v___x_1071_ = v_reuseFailAlloc_1075_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1068_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1067_, 0, v___x_1071_);
                    v___x_1073_ = v___x_1067_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1074_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1071_);
                    v___x_1073_ = v_reuseFailAlloc_1074_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1073_;
            }
            6 => {
                if v_isShared_1080_ == 0 {
                    v___x_1082_ = v___x_1079_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1083_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
                    v___x_1082_ = v_reuseFailAlloc_1083_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1082_;
            }
            8 => {
                return v___x_1088_;
            }
            9 => {
                if v_isShared_1094_ == 0 {
                    v___x_1096_ = v___x_1093_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1097_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
                    v___x_1096_ = v_reuseFailAlloc_1097_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1096_;
            }
            11 => {
                if v_isShared_1102_ == 0 {
                    v___x_1104_ = v___x_1101_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1105_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
                    v___x_1104_ = v_reuseFailAlloc_1105_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1104_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_documentUriFromModule_x3f___boxed(
    mut v_modName_1107_: *mut crate::leanh::LeanObject,
    mut v_a_1108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1109_ = l_Lean_Server_documentUriFromModule_x3f(v_modName_1107_);
    return v_res_1109_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0(
    mut v_x_1110_: *mut crate::leanh::LeanObject,
    mut v_x_1111_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1110_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_1111_) == 0 {
            let mut v___x_1112_: u8 = 0;
            v___x_1112_ = 1;
            return v___x_1112_;
        } else {
            let mut v___x_1113_: u8 = 0;
            v___x_1113_ = 0;
            return v___x_1113_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_1111_) == 0 {
            let mut v___x_1114_: u8 = 0;
            v___x_1114_ = 0;
            return v___x_1114_;
        } else {
            let mut v_val_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1117_: u8 = 0;
            v_val_1115_ = crate::leanh::lean_ctor_get(v_x_1110_, 0);
            v_val_1116_ = crate::leanh::lean_ctor_get(v_x_1111_, 0);
            v___x_1117_ = lean_string_dec_eq(v_val_1115_, v_val_1116_);
            return v___x_1117_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0___boxed(
    mut v_x_1118_: *mut crate::leanh::LeanObject,
    mut v_x_1119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1120_: u8 = 0;
    let mut v_r_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1120_ = l_Option_instBEq_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0(
        v_x_1118_, v_x_1119_,
    );
    crate::leanh::lean_dec(v_x_1119_);
    crate::leanh::lean_dec(v_x_1118_);
    v_r_1121_ = crate::leanh::lean_box((v_res_1120_) as usize);
    return v_r_1121_;
}
pub unsafe fn l_Lean_Server_moduleFromDocumentUri(
    mut v_uri_1124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1130_: u8 = 0;
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: u8 = 0;
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1144_: u8 = 0;
    let mut v_val_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1153_: u8 = 0;
    let mut v_a_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1157_: u8 = 0;
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1161_: u8 = 0;
    let mut v_a_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1165_: u8 = 0;
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1169_: u8 = 0;
    let mut v_isSharedCheck_1170_: u8 = 0;
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1126_ = l_System_Uri_fileUriToPath_x3f(v_uri_1124_);
                if crate::leanh::lean_obj_tag(v___x_1126_) == 1 {
                    v_val_1127_ = crate::leanh::lean_ctor_get(v___x_1126_, 0);
                    v_isSharedCheck_1170_ = (!crate::leanh::lean_is_exclusive(v___x_1126_)) as u8;
                    if v_isSharedCheck_1170_ == 0 {
                        v___x_1129_ = v___x_1126_;
                        v_isShared_1130_ = v_isSharedCheck_1170_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1127_);
                        crate::leanh::lean_dec(v___x_1126_);
                        v___x_1129_ = crate::leanh::lean_box(0);
                        v_isShared_1130_ = v_isSharedCheck_1170_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1126_);
                    v___x_1171_ =
                        l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(v_uri_1124_);
                    v___x_1172_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1172_, 0, v___x_1171_);
                    return v___x_1172_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_val_1127_);
                v___x_1131_ = l_System_FilePath_extension(v_val_1127_);
                v___x_1132_ = l_Lean_Server_moduleFromDocumentUri___closed__0;
                v___x_1133_ =
                    l_Option_instBEq_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0(
                        v___x_1131_,
                        v___x_1132_,
                    );
                crate::leanh::lean_dec(v___x_1131_);
                if v___x_1133_ == 0 {
                    crate::leanh::lean_dec(v_val_1127_);
                    v___x_1134_ =
                        l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(v_uri_1124_);
                    if v_isShared_1130_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1129_, 0);
                        crate::leanh::lean_ctor_set(v___x_1129_, 0, v___x_1134_);
                        v___x_1136_ = v___x_1129_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1137_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
                        v___x_1136_ = v_reuseFailAlloc_1137_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1129_);
                    v___x_1138_ = l_Lean_getSrcSearchPath();
                    if crate::leanh::lean_obj_tag(v___x_1138_) == 0 {
                        v_a_1139_ = crate::leanh::lean_ctor_get(v___x_1138_, 0);
                        crate::leanh::lean_inc(v_a_1139_);
                        crate::leanh::lean_dec_ref_known(v___x_1138_, 1);
                        v___x_1140_ = l_Lean_searchModuleNameOfFileName(v_val_1127_, v_a_1139_);
                        crate::leanh::lean_dec(v_a_1139_);
                        if crate::leanh::lean_obj_tag(v___x_1140_) == 0 {
                            v_a_1141_ = crate::leanh::lean_ctor_get(v___x_1140_, 0);
                            v_isSharedCheck_1153_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1140_)) as u8;
                            if v_isSharedCheck_1153_ == 0 {
                                v___x_1143_ = v___x_1140_;
                                v_isShared_1144_ = v_isSharedCheck_1153_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1141_);
                                crate::leanh::lean_dec(v___x_1140_);
                                v___x_1143_ = crate::leanh::lean_box(0);
                                v_isShared_1144_ = v_isSharedCheck_1153_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_a_1154_ = crate::leanh::lean_ctor_get(v___x_1140_, 0);
                            v_isSharedCheck_1161_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1140_)) as u8;
                            if v_isSharedCheck_1161_ == 0 {
                                v___x_1156_ = v___x_1140_;
                                v_isShared_1157_ = v_isSharedCheck_1161_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1154_);
                                crate::leanh::lean_dec(v___x_1140_);
                                v___x_1156_ = crate::leanh::lean_box(0);
                                v_isShared_1157_ = v_isSharedCheck_1161_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_1127_);
                        v_a_1162_ = crate::leanh::lean_ctor_get(v___x_1138_, 0);
                        v_isSharedCheck_1169_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1138_)) as u8;
                        if v_isSharedCheck_1169_ == 0 {
                            v___x_1164_ = v___x_1138_;
                            v_isShared_1165_ = v_isSharedCheck_1169_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1162_);
                            crate::leanh::lean_dec(v___x_1138_);
                            v___x_1164_ = crate::leanh::lean_box(0);
                            v_isShared_1165_ = v_isSharedCheck_1169_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1136_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_1141_) == 1 {
                    v_val_1145_ = crate::leanh::lean_ctor_get(v_a_1141_, 0);
                    crate::leanh::lean_inc(v_val_1145_);
                    crate::leanh::lean_dec_ref_known(v_a_1141_, 1);
                    if v_isShared_1144_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1143_, 0, v_val_1145_);
                        v___x_1147_ = v___x_1143_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1148_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_val_1145_);
                        v___x_1147_ = v_reuseFailAlloc_1148_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1141_);
                    v___x_1149_ =
                        l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(v_uri_1124_);
                    if v_isShared_1144_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1143_, 0, v___x_1149_);
                        v___x_1151_ = v___x_1143_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1152_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
                        v___x_1151_ = v_reuseFailAlloc_1152_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1147_;
            }
            5 => {
                return v___x_1151_;
            }
            6 => {
                if v_isShared_1157_ == 0 {
                    v___x_1159_ = v___x_1156_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1160_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
                    v___x_1159_ = v_reuseFailAlloc_1160_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1159_;
            }
            8 => {
                if v_isShared_1165_ == 0 {
                    v___x_1167_ = v___x_1164_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1168_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
                    v___x_1167_ = v_reuseFailAlloc_1168_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1167_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_moduleFromDocumentUri___boxed(
    mut v_uri_1173_: *mut crate::leanh::LeanObject,
    mut v_a_1174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1175_ = l_Lean_Server_moduleFromDocumentUri(v_uri_1173_);
    crate::leanh::lean_dec_ref(v_uri_1173_);
    return v_res_1175_;
}
pub unsafe fn l_Lean_Syntax_Range_toLspRange(
    mut v_text_1176_: *mut crate::leanh::LeanObject,
    mut v_r_1177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1182_: u8 = 0;
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1188_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_1178_ = crate::leanh::lean_ctor_get(v_r_1177_, 0);
                v_stop_1179_ = crate::leanh::lean_ctor_get(v_r_1177_, 1);
                v_isSharedCheck_1188_ = (!crate::leanh::lean_is_exclusive(v_r_1177_)) as u8;
                if v_isSharedCheck_1188_ == 0 {
                    v___x_1181_ = v_r_1177_;
                    v_isShared_1182_ = v_isSharedCheck_1188_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_1179_);
                    crate::leanh::lean_inc(v_start_1178_);
                    crate::leanh::lean_dec(v_r_1177_);
                    v___x_1181_ = crate::leanh::lean_box(0);
                    v_isShared_1182_ = v_isSharedCheck_1188_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_text_1176_);
                v___x_1183_ = l_Lean_FileMap_utf8PosToLspPos(v_text_1176_, v_start_1178_);
                crate::leanh::lean_dec(v_start_1178_);
                v___x_1184_ = l_Lean_FileMap_utf8PosToLspPos(v_text_1176_, v_stop_1179_);
                crate::leanh::lean_dec(v_stop_1179_);
                if v_isShared_1182_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1181_, 1, v___x_1184_);
                    crate::leanh::lean_ctor_set(v___x_1181_, 0, v___x_1183_);
                    v___x_1186_ = v___x_1181_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1187_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1183_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1187_, 1, v___x_1184_);
                    v___x_1186_ = v_reuseFailAlloc_1187_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1186_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_Utils(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_Uri(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Communication(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Diagnostics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Extra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_InfoUtils(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Server_instInhabitedDocumentMeta_default =
        _init_l_Lean_Server_instInhabitedDocumentMeta_default();
    crate::leanh::lean_mark_persistent(l_Lean_Server_instInhabitedDocumentMeta_default);
    l_Lean_Server_instInhabitedDocumentMeta = _init_l_Lean_Server_instInhabitedDocumentMeta();
    crate::leanh::lean_mark_persistent(l_Lean_Server_instInhabitedDocumentMeta);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_Utils(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_Utils(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_Uri(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Lsp_Communication(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Lsp_Diagnostics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Lsp_Extra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Server_InfoUtils(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Utils(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_Utils(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Server_Utils(builtin);
}

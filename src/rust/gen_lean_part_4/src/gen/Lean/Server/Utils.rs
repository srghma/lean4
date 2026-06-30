// Lean compiler output
// Module: Lean.Server.Utils
// Imports: Init.System.Uri Lean.Data.Lsp.Communication Lean.Data.Lsp.Diagnostics Lean.Data.Lsp.Extra Lean.Server.InfoUtils
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_uget_borrowed, lean_io_realpath,
    lean_mk_empty_array_with_capacity, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_to_int,
    lean_string_append, lean_string_dec_eq, lean_string_memcmp, lean_string_utf8_byte_size,
    lean_string_utf8_extract, lean_usize_add, lean_usize_dec_eq, lean_usize_of_nat,
};
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
pub static l_Lean_Server_instInhabitedDocumentMeta_default___closed__0_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_instInhabitedDocumentMeta_default___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Server_instInhabitedDocumentMeta_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Server_instInhabitedDocumentMeta_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Server_instInhabitedDocumentMeta_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Server_instInhabitedDocumentMeta: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Server_mkPublishDiagnosticsNotification___closed__0_value:
    leanh::LeanStringObject<32> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_mkPublishDiagnosticsNotification___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_mkFileProgressNotification___closed__0_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Server_mkFileProgressNotification___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_mkFileProgressNotification___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_mkFileProgressDoneNotification___closed__0_value:
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
static mut l_Lean_Server_mkFileProgressDoneNotification___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_mkFileProgressDoneNotification___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_mkApplyWorkspaceEditRequest___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Server_mkApplyWorkspaceEditRequest___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_mkApplyWorkspaceEditRequest___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0_value
) as *mut leanh::LeanObject;
static mut l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_documentUriFromModule_x3f___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Server_documentUriFromModule_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_documentUriFromModule_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Server_moduleFromDocumentUri___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Server_documentUriFromModule_x3f___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Server_moduleFromDocumentUri___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Server_moduleFromDocumentUri___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_IO_throwServerError___redArg(
    mut v_err_595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_597_ = lean_mk_io_user_error(v_err_595_);
    v___x_598_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_598_, 0, v___x_597_);
    return v___x_598_;
}
pub unsafe fn l_IO_throwServerError___redArg___boxed(
    mut v_err_599_: *mut leanh::LeanObject,
    mut v_a_600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_601_ = l_IO_throwServerError___redArg(v_err_599_);
    return v_res_601_;
}
pub unsafe fn l_IO_throwServerError(
    mut v_00_u03b1_602_: *mut leanh::LeanObject,
    mut v_err_603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_605_ = l_IO_throwServerError___redArg(v_err_603_);
    return v___x_605_;
}
pub unsafe fn l_IO_throwServerError___boxed(
    mut v_00_u03b1_606_: *mut leanh::LeanObject,
    mut v_err_607_: *mut leanh::LeanObject,
    mut v_a_608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_609_ = l_IO_throwServerError(v_00_u03b1_606_, v_err_607_);
    return v_res_609_;
}
pub unsafe fn l_IO_FS_Stream_chainRight___lam__0(
    mut v_read_610_: *mut leanh::LeanObject,
    mut v_b_611_: *mut leanh::LeanObject,
    mut v_flushEagerly_612_: u8,
    mut v_sz_613_: usize,
) -> *mut leanh::LeanObject {
    let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_flush_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_write_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_623_: u8 = 0;
    let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_630_: u8 = 0;
    let mut v___x_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_634_: u8 = 0;
    let mut v_unused_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_639_: u8 = 0;
    let mut v___x_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_643_: u8 = 0;
    let mut v_isSharedCheck_644_: u8 = 0;
    let mut v_unused_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_649_: u8 = 0;
    let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_653_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_615_ = leanh::lean_box_usize(v_sz_613_);
                v___x_616_ =
                    leanh::lean_apply_2(v_read_610_, v___x_615_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_616_) == 0 {
                    v_a_617_ = leanh::lean_ctor_get(v___x_616_, 0);
                    leanh::lean_inc_n(v_a_617_, 2);
                    leanh::lean_dec_ref_known(v___x_616_, 1);
                    v_flush_618_ = leanh::lean_ctor_get(v_b_611_, 0);
                    leanh::lean_inc_ref(v_flush_618_);
                    v_write_619_ = leanh::lean_ctor_get(v_b_611_, 2);
                    leanh::lean_inc_ref(v_write_619_);
                    leanh::lean_dec_ref(v_b_611_);
                    v___x_620_ = leanh::lean_apply_2(
                        v_write_619_,
                        v_a_617_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_620_) == 0 {
                        v_isSharedCheck_644_ = (!leanh::lean_is_exclusive(v___x_620_)) as u8;
                        if v_isSharedCheck_644_ == 0 {
                            v_unused_645_ = leanh::lean_ctor_get(v___x_620_, 0);
                            leanh::lean_dec(v_unused_645_);
                            v___x_622_ = v___x_620_;
                            v_isShared_623_ = v_isSharedCheck_644_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_620_);
                            v___x_622_ = leanh::lean_box(0);
                            v_isShared_623_ = v_isSharedCheck_644_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_flush_618_);
                        leanh::lean_dec(v_a_617_);
                        v_a_646_ = leanh::lean_ctor_get(v___x_620_, 0);
                        v_isSharedCheck_653_ = (!leanh::lean_is_exclusive(v___x_620_)) as u8;
                        if v_isSharedCheck_653_ == 0 {
                            v___x_648_ = v___x_620_;
                            v_isShared_649_ = v_isSharedCheck_653_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_646_);
                            leanh::lean_dec(v___x_620_);
                            v___x_648_ = leanh::lean_box(0);
                            v_isShared_649_ = v_isSharedCheck_653_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_b_611_);
                    return v___x_616_;
                }
            }
            1 => {
                if v_flushEagerly_612_ == 0 {
                    leanh::lean_dec_ref(v_flush_618_);
                    if v_isShared_623_ == 0 {
                        leanh::lean_ctor_set(v___x_622_, 0, v_a_617_);
                        v___x_625_ = v___x_622_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_626_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_617_);
                        v___x_625_ = v_reuseFailAlloc_626_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_622_);
                    v___x_627_ =
                        leanh::lean_apply_1(v_flush_618_, leanh::lean_box(0));
                    if leanh::lean_obj_tag(v___x_627_) == 0 {
                        v_isSharedCheck_634_ = (!leanh::lean_is_exclusive(v___x_627_)) as u8;
                        if v_isSharedCheck_634_ == 0 {
                            v_unused_635_ = leanh::lean_ctor_get(v___x_627_, 0);
                            leanh::lean_dec(v_unused_635_);
                            v___x_629_ = v___x_627_;
                            v_isShared_630_ = v_isSharedCheck_634_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_627_);
                            v___x_629_ = leanh::lean_box(0);
                            v_isShared_630_ = v_isSharedCheck_634_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_617_);
                        v_a_636_ = leanh::lean_ctor_get(v___x_627_, 0);
                        v_isSharedCheck_643_ = (!leanh::lean_is_exclusive(v___x_627_)) as u8;
                        if v_isSharedCheck_643_ == 0 {
                            v___x_638_ = v___x_627_;
                            v_isShared_639_ = v_isSharedCheck_643_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_636_);
                            leanh::lean_dec(v___x_627_);
                            v___x_638_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_629_, 0, v_a_617_);
                    v___x_632_ = v___x_629_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_633_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_617_);
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
                    v_reuseFailAlloc_642_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
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
                    v_reuseFailAlloc_652_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
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
    mut v_read_654_: *mut leanh::LeanObject,
    mut v_b_655_: *mut leanh::LeanObject,
    mut v_flushEagerly_656_: *mut leanh::LeanObject,
    mut v_sz_657_: *mut leanh::LeanObject,
    mut v___y_658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_flushEagerly_boxed_659_: u8 = 0;
    let mut v_sz_boxed_660_: usize = 0;
    let mut v_res_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_flushEagerly_boxed_659_ = (leanh::lean_unbox(v_flushEagerly_656_) as u8);
    v_sz_boxed_660_ = leanh::lean_unbox_usize(v_sz_657_);
    leanh::lean_dec(v_sz_657_);
    v_res_661_ = l_IO_FS_Stream_chainRight___lam__0(
        v_read_654_,
        v_b_655_,
        v_flushEagerly_boxed_659_,
        v_sz_boxed_660_,
    );
    return v_res_661_;
}
pub unsafe fn l_IO_FS_Stream_chainRight___lam__1(
    mut v_getLine_662_: *mut leanh::LeanObject,
    mut v_b_663_: *mut leanh::LeanObject,
    mut v_flushEagerly_664_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_flush_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_673_: u8 = 0;
    let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_680_: u8 = 0;
    let mut v___x_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_684_: u8 = 0;
    let mut v_unused_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_689_: u8 = 0;
    let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_693_: u8 = 0;
    let mut v_isSharedCheck_694_: u8 = 0;
    let mut v_unused_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_699_: u8 = 0;
    let mut v___x_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_703_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_666_ = leanh::lean_apply_1(v_getLine_662_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v___x_666_) == 0 {
                    v_a_667_ = leanh::lean_ctor_get(v___x_666_, 0);
                    leanh::lean_inc_n(v_a_667_, 2);
                    leanh::lean_dec_ref_known(v___x_666_, 1);
                    v_flush_668_ = leanh::lean_ctor_get(v_b_663_, 0);
                    leanh::lean_inc_ref(v_flush_668_);
                    v_putStr_669_ = leanh::lean_ctor_get(v_b_663_, 4);
                    leanh::lean_inc_ref(v_putStr_669_);
                    leanh::lean_dec_ref(v_b_663_);
                    v___x_670_ = leanh::lean_apply_2(
                        v_putStr_669_,
                        v_a_667_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_670_) == 0 {
                        v_isSharedCheck_694_ = (!leanh::lean_is_exclusive(v___x_670_)) as u8;
                        if v_isSharedCheck_694_ == 0 {
                            v_unused_695_ = leanh::lean_ctor_get(v___x_670_, 0);
                            leanh::lean_dec(v_unused_695_);
                            v___x_672_ = v___x_670_;
                            v_isShared_673_ = v_isSharedCheck_694_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_670_);
                            v___x_672_ = leanh::lean_box(0);
                            v_isShared_673_ = v_isSharedCheck_694_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_flush_668_);
                        leanh::lean_dec(v_a_667_);
                        v_a_696_ = leanh::lean_ctor_get(v___x_670_, 0);
                        v_isSharedCheck_703_ = (!leanh::lean_is_exclusive(v___x_670_)) as u8;
                        if v_isSharedCheck_703_ == 0 {
                            v___x_698_ = v___x_670_;
                            v_isShared_699_ = v_isSharedCheck_703_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_696_);
                            leanh::lean_dec(v___x_670_);
                            v___x_698_ = leanh::lean_box(0);
                            v_isShared_699_ = v_isSharedCheck_703_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_b_663_);
                    return v___x_666_;
                }
            }
            1 => {
                if v_flushEagerly_664_ == 0 {
                    leanh::lean_dec_ref(v_flush_668_);
                    if v_isShared_673_ == 0 {
                        leanh::lean_ctor_set(v___x_672_, 0, v_a_667_);
                        v___x_675_ = v___x_672_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_676_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_667_);
                        v___x_675_ = v_reuseFailAlloc_676_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_672_);
                    v___x_677_ =
                        leanh::lean_apply_1(v_flush_668_, leanh::lean_box(0));
                    if leanh::lean_obj_tag(v___x_677_) == 0 {
                        v_isSharedCheck_684_ = (!leanh::lean_is_exclusive(v___x_677_)) as u8;
                        if v_isSharedCheck_684_ == 0 {
                            v_unused_685_ = leanh::lean_ctor_get(v___x_677_, 0);
                            leanh::lean_dec(v_unused_685_);
                            v___x_679_ = v___x_677_;
                            v_isShared_680_ = v_isSharedCheck_684_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_677_);
                            v___x_679_ = leanh::lean_box(0);
                            v_isShared_680_ = v_isSharedCheck_684_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_667_);
                        v_a_686_ = leanh::lean_ctor_get(v___x_677_, 0);
                        v_isSharedCheck_693_ = (!leanh::lean_is_exclusive(v___x_677_)) as u8;
                        if v_isSharedCheck_693_ == 0 {
                            v___x_688_ = v___x_677_;
                            v_isShared_689_ = v_isSharedCheck_693_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_686_);
                            leanh::lean_dec(v___x_677_);
                            v___x_688_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_679_, 0, v_a_667_);
                    v___x_682_ = v___x_679_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_683_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_667_);
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
                    v_reuseFailAlloc_692_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
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
                    v_reuseFailAlloc_702_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
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
    mut v_getLine_704_: *mut leanh::LeanObject,
    mut v_b_705_: *mut leanh::LeanObject,
    mut v_flushEagerly_706_: *mut leanh::LeanObject,
    mut v___y_707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_flushEagerly_boxed_708_: u8 = 0;
    let mut v_res_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_flushEagerly_boxed_708_ = (leanh::lean_unbox(v_flushEagerly_706_) as u8);
    v_res_709_ =
        l_IO_FS_Stream_chainRight___lam__1(v_getLine_704_, v_b_705_, v_flushEagerly_boxed_708_);
    return v_res_709_;
}
pub unsafe fn l_IO_FS_Stream_chainRight___lam__2(
    mut v_flush_710_: *mut leanh::LeanObject,
    mut v_b_711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_713_ = leanh::lean_apply_1(v_flush_710_, leanh::lean_box(0));
    if leanh::lean_obj_tag(v___x_713_) == 0 {
        let mut v_flush_714_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_715_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_713_, 1);
        v_flush_714_ = leanh::lean_ctor_get(v_b_711_, 0);
        leanh::lean_inc_ref(v_flush_714_);
        leanh::lean_dec_ref(v_b_711_);
        v___x_715_ = leanh::lean_apply_1(v_flush_714_, leanh::lean_box(0));
        return v___x_715_;
    } else {
        leanh::lean_dec_ref(v_b_711_);
        return v___x_713_;
    }
}
pub unsafe fn l_IO_FS_Stream_chainRight___lam__2___boxed(
    mut v_flush_716_: *mut leanh::LeanObject,
    mut v_b_717_: *mut leanh::LeanObject,
    mut v___y_718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_719_ = l_IO_FS_Stream_chainRight___lam__2(v_flush_716_, v_b_717_);
    return v_res_719_;
}
pub unsafe fn l_IO_FS_Stream_chainRight(
    mut v_a_720_: *mut leanh::LeanObject,
    mut v_b_721_: *mut leanh::LeanObject,
    mut v_flushEagerly_722_: u8,
) -> *mut leanh::LeanObject {
    let mut v_flush_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_read_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_write_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLine_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isTty_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_731_: u8 = 0;
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_740_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_flush_723_ = leanh::lean_ctor_get(v_a_720_, 0);
                v_read_724_ = leanh::lean_ctor_get(v_a_720_, 1);
                v_write_725_ = leanh::lean_ctor_get(v_a_720_, 2);
                v_getLine_726_ = leanh::lean_ctor_get(v_a_720_, 3);
                v_putStr_727_ = leanh::lean_ctor_get(v_a_720_, 4);
                v_isTty_728_ = leanh::lean_ctor_get(v_a_720_, 5);
                v_isSharedCheck_740_ = (!leanh::lean_is_exclusive(v_a_720_)) as u8;
                if v_isSharedCheck_740_ == 0 {
                    v___x_730_ = v_a_720_;
                    v_isShared_731_ = v_isSharedCheck_740_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_isTty_728_);
                    leanh::lean_inc(v_putStr_727_);
                    leanh::lean_inc(v_getLine_726_);
                    leanh::lean_inc(v_write_725_);
                    leanh::lean_inc(v_read_724_);
                    leanh::lean_inc(v_flush_723_);
                    leanh::lean_dec(v_a_720_);
                    v___x_730_ = leanh::lean_box(0);
                    v_isShared_731_ = v_isSharedCheck_740_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_732_ = leanh::lean_box((v_flushEagerly_722_) as usize);
                leanh::lean_inc_ref_n(v_b_721_, 2);
                v___f_733_ = leanh::lean_alloc_closure(
                    l_IO_FS_Stream_chainRight___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                leanh::lean_closure_set(v___f_733_, 0, v_read_724_);
                leanh::lean_closure_set(v___f_733_, 1, v_b_721_);
                leanh::lean_closure_set(v___f_733_, 2, v___x_732_);
                v___x_734_ = leanh::lean_box((v_flushEagerly_722_) as usize);
                v___f_735_ = leanh::lean_alloc_closure(
                    l_IO_FS_Stream_chainRight___lam__1___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_735_, 0, v_getLine_726_);
                leanh::lean_closure_set(v___f_735_, 1, v_b_721_);
                leanh::lean_closure_set(v___f_735_, 2, v___x_734_);
                v___f_736_ = leanh::lean_alloc_closure(
                    l_IO_FS_Stream_chainRight___lam__2___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_736_, 0, v_flush_723_);
                leanh::lean_closure_set(v___f_736_, 1, v_b_721_);
                if v_isShared_731_ == 0 {
                    leanh::lean_ctor_set(v___x_730_, 3, v___f_735_);
                    leanh::lean_ctor_set(v___x_730_, 1, v___f_733_);
                    leanh::lean_ctor_set(v___x_730_, 0, v___f_736_);
                    v___x_738_ = v___x_730_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_739_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_739_, 0, v___f_736_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_739_, 1, v___f_733_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_739_, 2, v_write_725_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_739_, 3, v___f_735_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_739_, 4, v_putStr_727_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_739_, 5, v_isTty_728_);
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
    mut v_a_741_: *mut leanh::LeanObject,
    mut v_b_742_: *mut leanh::LeanObject,
    mut v_flushEagerly_743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_flushEagerly_boxed_744_: u8 = 0;
    let mut v_res_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_flushEagerly_boxed_744_ = (leanh::lean_unbox(v_flushEagerly_743_) as u8);
    v_res_745_ = l_IO_FS_Stream_chainRight(v_a_741_, v_b_742_, v_flushEagerly_boxed_744_);
    return v_res_745_;
}
pub unsafe fn l_IO_FS_Stream_chainLeft___lam__0(
    mut v_flush_746_: *mut leanh::LeanObject,
    mut v_flush_747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_749_ = leanh::lean_apply_1(v_flush_746_, leanh::lean_box(0));
    if leanh::lean_obj_tag(v___x_749_) == 0 {
        let mut v___x_750_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_749_, 1);
        v___x_750_ = leanh::lean_apply_1(v_flush_747_, leanh::lean_box(0));
        return v___x_750_;
    } else {
        leanh::lean_dec_ref(v_flush_747_);
        return v___x_749_;
    }
}
pub unsafe fn l_IO_FS_Stream_chainLeft___lam__0___boxed(
    mut v_flush_751_: *mut leanh::LeanObject,
    mut v_flush_752_: *mut leanh::LeanObject,
    mut v___y_753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_754_ = l_IO_FS_Stream_chainLeft___lam__0(v_flush_751_, v_flush_752_);
    return v_res_754_;
}
pub unsafe fn l_IO_FS_Stream_chainLeft___lam__1(
    mut v_write_755_: *mut leanh::LeanObject,
    mut v_flushEagerly_756_: u8,
    mut v_write_757_: *mut leanh::LeanObject,
    mut v_flush_758_: *mut leanh::LeanObject,
    mut v_bs_759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_bs_759_);
    v___x_761_ = leanh::lean_apply_2(v_write_755_, v_bs_759_, leanh::lean_box(0));
    if leanh::lean_obj_tag(v___x_761_) == 0 {
        leanh::lean_dec_ref_known(v___x_761_, 1);
        if v_flushEagerly_756_ == 0 {
            let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_flush_758_);
            v___x_762_ =
                leanh::lean_apply_2(v_write_757_, v_bs_759_, leanh::lean_box(0));
            return v___x_762_;
        } else {
            let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_763_ = leanh::lean_apply_1(v_flush_758_, leanh::lean_box(0));
            if leanh::lean_obj_tag(v___x_763_) == 0 {
                let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref_known(v___x_763_, 1);
                v___x_764_ =
                    leanh::lean_apply_2(v_write_757_, v_bs_759_, leanh::lean_box(0));
                return v___x_764_;
            } else {
                leanh::lean_dec_ref(v_bs_759_);
                leanh::lean_dec_ref(v_write_757_);
                return v___x_763_;
            }
        }
    } else {
        leanh::lean_dec_ref(v_bs_759_);
        leanh::lean_dec_ref(v_flush_758_);
        leanh::lean_dec_ref(v_write_757_);
        return v___x_761_;
    }
}
pub unsafe fn l_IO_FS_Stream_chainLeft___lam__1___boxed(
    mut v_write_765_: *mut leanh::LeanObject,
    mut v_flushEagerly_766_: *mut leanh::LeanObject,
    mut v_write_767_: *mut leanh::LeanObject,
    mut v_flush_768_: *mut leanh::LeanObject,
    mut v_bs_769_: *mut leanh::LeanObject,
    mut v___y_770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_flushEagerly_boxed_771_: u8 = 0;
    let mut v_res_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_flushEagerly_boxed_771_ = (leanh::lean_unbox(v_flushEagerly_766_) as u8);
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
    mut v_putStr_773_: *mut leanh::LeanObject,
    mut v_flushEagerly_774_: u8,
    mut v_putStr_775_: *mut leanh::LeanObject,
    mut v_flush_776_: *mut leanh::LeanObject,
    mut v_s_777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_s_777_);
    v___x_779_ = leanh::lean_apply_2(v_putStr_773_, v_s_777_, leanh::lean_box(0));
    if leanh::lean_obj_tag(v___x_779_) == 0 {
        leanh::lean_dec_ref_known(v___x_779_, 1);
        if v_flushEagerly_774_ == 0 {
            let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_flush_776_);
            v___x_780_ =
                leanh::lean_apply_2(v_putStr_775_, v_s_777_, leanh::lean_box(0));
            return v___x_780_;
        } else {
            let mut v___x_781_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_781_ = leanh::lean_apply_1(v_flush_776_, leanh::lean_box(0));
            if leanh::lean_obj_tag(v___x_781_) == 0 {
                let mut v___x_782_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref_known(v___x_781_, 1);
                v___x_782_ =
                    leanh::lean_apply_2(v_putStr_775_, v_s_777_, leanh::lean_box(0));
                return v___x_782_;
            } else {
                leanh::lean_dec_ref(v_s_777_);
                leanh::lean_dec_ref(v_putStr_775_);
                return v___x_781_;
            }
        }
    } else {
        leanh::lean_dec_ref(v_s_777_);
        leanh::lean_dec_ref(v_flush_776_);
        leanh::lean_dec_ref(v_putStr_775_);
        return v___x_779_;
    }
}
pub unsafe fn l_IO_FS_Stream_chainLeft___lam__2___boxed(
    mut v_putStr_783_: *mut leanh::LeanObject,
    mut v_flushEagerly_784_: *mut leanh::LeanObject,
    mut v_putStr_785_: *mut leanh::LeanObject,
    mut v_flush_786_: *mut leanh::LeanObject,
    mut v_s_787_: *mut leanh::LeanObject,
    mut v___y_788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_flushEagerly_boxed_789_: u8 = 0;
    let mut v_res_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_flushEagerly_boxed_789_ = (leanh::lean_unbox(v_flushEagerly_784_) as u8);
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
    mut v_a_791_: *mut leanh::LeanObject,
    mut v_b_792_: *mut leanh::LeanObject,
    mut v_flushEagerly_793_: u8,
) -> *mut leanh::LeanObject {
    let mut v_flush_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_write_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_flush_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_read_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_write_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLine_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isTty_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_805_: u8 = 0;
    let mut v___f_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_814_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_flush_794_ = leanh::lean_ctor_get(v_a_791_, 0);
                leanh::lean_inc_ref(v_flush_794_);
                v_write_795_ = leanh::lean_ctor_get(v_a_791_, 2);
                leanh::lean_inc_ref(v_write_795_);
                v_putStr_796_ = leanh::lean_ctor_get(v_a_791_, 4);
                leanh::lean_inc_ref(v_putStr_796_);
                leanh::lean_dec_ref(v_a_791_);
                v_flush_797_ = leanh::lean_ctor_get(v_b_792_, 0);
                v_read_798_ = leanh::lean_ctor_get(v_b_792_, 1);
                v_write_799_ = leanh::lean_ctor_get(v_b_792_, 2);
                v_getLine_800_ = leanh::lean_ctor_get(v_b_792_, 3);
                v_putStr_801_ = leanh::lean_ctor_get(v_b_792_, 4);
                v_isTty_802_ = leanh::lean_ctor_get(v_b_792_, 5);
                v_isSharedCheck_814_ = (!leanh::lean_is_exclusive(v_b_792_)) as u8;
                if v_isSharedCheck_814_ == 0 {
                    v___x_804_ = v_b_792_;
                    v_isShared_805_ = v_isSharedCheck_814_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_isTty_802_);
                    leanh::lean_inc(v_putStr_801_);
                    leanh::lean_inc(v_getLine_800_);
                    leanh::lean_inc(v_write_799_);
                    leanh::lean_inc(v_read_798_);
                    leanh::lean_inc(v_flush_797_);
                    leanh::lean_dec(v_b_792_);
                    v___x_804_ = leanh::lean_box(0);
                    v_isShared_805_ = v_isSharedCheck_814_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref_n(v_flush_794_, 2);
                v___f_806_ = leanh::lean_alloc_closure(
                    l_IO_FS_Stream_chainLeft___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_806_, 0, v_flush_794_);
                leanh::lean_closure_set(v___f_806_, 1, v_flush_797_);
                v___x_807_ = leanh::lean_box((v_flushEagerly_793_) as usize);
                v___f_808_ = leanh::lean_alloc_closure(
                    l_IO_FS_Stream_chainLeft___lam__1___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                leanh::lean_closure_set(v___f_808_, 0, v_write_795_);
                leanh::lean_closure_set(v___f_808_, 1, v___x_807_);
                leanh::lean_closure_set(v___f_808_, 2, v_write_799_);
                leanh::lean_closure_set(v___f_808_, 3, v_flush_794_);
                v___x_809_ = leanh::lean_box((v_flushEagerly_793_) as usize);
                v___f_810_ = leanh::lean_alloc_closure(
                    l_IO_FS_Stream_chainLeft___lam__2___boxed as *mut core::ffi::c_void,
                    6,
                    4,
                );
                leanh::lean_closure_set(v___f_810_, 0, v_putStr_796_);
                leanh::lean_closure_set(v___f_810_, 1, v___x_809_);
                leanh::lean_closure_set(v___f_810_, 2, v_putStr_801_);
                leanh::lean_closure_set(v___f_810_, 3, v_flush_794_);
                if v_isShared_805_ == 0 {
                    leanh::lean_ctor_set(v___x_804_, 4, v___f_810_);
                    leanh::lean_ctor_set(v___x_804_, 2, v___f_808_);
                    leanh::lean_ctor_set(v___x_804_, 0, v___f_806_);
                    v___x_812_ = v___x_804_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_813_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_813_, 0, v___f_806_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_813_, 1, v_read_798_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_813_, 2, v___f_808_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_813_, 3, v_getLine_800_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_813_, 4, v___f_810_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_813_, 5, v_isTty_802_);
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
    mut v_a_815_: *mut leanh::LeanObject,
    mut v_b_816_: *mut leanh::LeanObject,
    mut v_flushEagerly_817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_flushEagerly_boxed_818_: u8 = 0;
    let mut v_res_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_flushEagerly_boxed_818_ = (leanh::lean_unbox(v_flushEagerly_817_) as u8);
    v_res_819_ = l_IO_FS_Stream_chainLeft(v_a_815_, v_b_816_, v_flushEagerly_boxed_818_);
    return v_res_819_;
}
pub unsafe fn l_IO_FS_Stream_withPrefix___lam__0(
    mut v_putStr_820_: *mut leanh::LeanObject,
    mut v_pre_821_: *mut leanh::LeanObject,
    mut v_write_822_: *mut leanh::LeanObject,
    mut v_bs_823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_825_ = leanh::lean_apply_2(v_putStr_820_, v_pre_821_, leanh::lean_box(0));
    if leanh::lean_obj_tag(v___x_825_) == 0 {
        let mut v___x_826_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_825_, 1);
        v___x_826_ = leanh::lean_apply_2(v_write_822_, v_bs_823_, leanh::lean_box(0));
        return v___x_826_;
    } else {
        leanh::lean_dec_ref(v_bs_823_);
        leanh::lean_dec_ref(v_write_822_);
        return v___x_825_;
    }
}
pub unsafe fn l_IO_FS_Stream_withPrefix___lam__0___boxed(
    mut v_putStr_827_: *mut leanh::LeanObject,
    mut v_pre_828_: *mut leanh::LeanObject,
    mut v_write_829_: *mut leanh::LeanObject,
    mut v_bs_830_: *mut leanh::LeanObject,
    mut v___y_831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_832_ =
        l_IO_FS_Stream_withPrefix___lam__0(v_putStr_827_, v_pre_828_, v_write_829_, v_bs_830_);
    return v_res_832_;
}
pub unsafe fn l_IO_FS_Stream_withPrefix___lam__1(
    mut v_pre_833_: *mut leanh::LeanObject,
    mut v_putStr_834_: *mut leanh::LeanObject,
    mut v_s_835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_837_ = lean_string_append(v_pre_833_, v_s_835_);
    v___x_838_ = leanh::lean_apply_2(v_putStr_834_, v___x_837_, leanh::lean_box(0));
    return v___x_838_;
}
pub unsafe fn l_IO_FS_Stream_withPrefix___lam__1___boxed(
    mut v_pre_839_: *mut leanh::LeanObject,
    mut v_putStr_840_: *mut leanh::LeanObject,
    mut v_s_841_: *mut leanh::LeanObject,
    mut v___y_842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_843_ = l_IO_FS_Stream_withPrefix___lam__1(v_pre_839_, v_putStr_840_, v_s_841_);
    leanh::lean_dec_ref(v_s_841_);
    return v_res_843_;
}
pub unsafe fn l_IO_FS_Stream_withPrefix(
    mut v_a_844_: *mut leanh::LeanObject,
    mut v_pre_845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_flush_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_read_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_write_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLine_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_putStr_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isTty_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_854_: u8 = 0;
    let mut v___f_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_860_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_flush_846_ = leanh::lean_ctor_get(v_a_844_, 0);
                v_read_847_ = leanh::lean_ctor_get(v_a_844_, 1);
                v_write_848_ = leanh::lean_ctor_get(v_a_844_, 2);
                v_getLine_849_ = leanh::lean_ctor_get(v_a_844_, 3);
                v_putStr_850_ = leanh::lean_ctor_get(v_a_844_, 4);
                v_isTty_851_ = leanh::lean_ctor_get(v_a_844_, 5);
                v_isSharedCheck_860_ = (!leanh::lean_is_exclusive(v_a_844_)) as u8;
                if v_isSharedCheck_860_ == 0 {
                    v___x_853_ = v_a_844_;
                    v_isShared_854_ = v_isSharedCheck_860_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_isTty_851_);
                    leanh::lean_inc(v_putStr_850_);
                    leanh::lean_inc(v_getLine_849_);
                    leanh::lean_inc(v_write_848_);
                    leanh::lean_inc(v_read_847_);
                    leanh::lean_inc(v_flush_846_);
                    leanh::lean_dec(v_a_844_);
                    v___x_853_ = leanh::lean_box(0);
                    v_isShared_854_ = v_isSharedCheck_860_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_pre_845_);
                leanh::lean_inc_ref(v_putStr_850_);
                v___f_855_ = leanh::lean_alloc_closure(
                    l_IO_FS_Stream_withPrefix___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                leanh::lean_closure_set(v___f_855_, 0, v_putStr_850_);
                leanh::lean_closure_set(v___f_855_, 1, v_pre_845_);
                leanh::lean_closure_set(v___f_855_, 2, v_write_848_);
                v___f_856_ = leanh::lean_alloc_closure(
                    l_IO_FS_Stream_withPrefix___lam__1___boxed as *mut core::ffi::c_void,
                    4,
                    2,
                );
                leanh::lean_closure_set(v___f_856_, 0, v_pre_845_);
                leanh::lean_closure_set(v___f_856_, 1, v_putStr_850_);
                if v_isShared_854_ == 0 {
                    leanh::lean_ctor_set(v___x_853_, 4, v___f_856_);
                    leanh::lean_ctor_set(v___x_853_, 2, v___f_855_);
                    v___x_858_ = v___x_853_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_859_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_859_, 0, v_flush_846_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_859_, 1, v_read_847_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_859_, 2, v___f_855_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_859_, 3, v_getLine_849_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_859_, 4, v___f_856_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_859_, 5, v_isTty_851_);
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
-> *mut leanh::LeanObject {
    let mut v___x_862_: u8 = 0;
    let mut v___x_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_862_ = 0;
    v___x_863_ = l_Lean_instInhabitedFileMap_default;
    v___x_864_ = leanh::lean_unsigned_to_nat(0);
    v___x_865_ = leanh::lean_box(0);
    v___x_866_ = l_Lean_Server_instInhabitedDocumentMeta_default___closed__0;
    v___x_867_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
    leanh::lean_ctor_set(v___x_867_, 0, v___x_866_);
    leanh::lean_ctor_set(v___x_867_, 1, v___x_865_);
    leanh::lean_ctor_set(v___x_867_, 2, v___x_864_);
    leanh::lean_ctor_set(v___x_867_, 3, v___x_863_);
    leanh::lean_ctor_set_uint8(
        v___x_867_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
        v___x_862_,
    );
    return v___x_867_;
}
pub unsafe fn _init_l_Lean_Server_instInhabitedDocumentMeta_default()
-> *mut leanh::LeanObject {
    let mut v___x_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_868_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Server_instInhabitedDocumentMeta_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Server_instInhabitedDocumentMeta_default___closed__1_once),
        _init_l_Lean_Server_instInhabitedDocumentMeta_default___closed__1,
    );
    return v___x_868_;
}
pub unsafe fn _init_l_Lean_Server_instInhabitedDocumentMeta() -> *mut leanh::LeanObject {
    let mut v___x_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_869_ = l_Lean_Server_instInhabitedDocumentMeta_default;
    return v___x_869_;
}
pub unsafe fn l_Lean_Server_DocumentMeta_mkInputContext(
    mut v_doc_870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_text_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uri_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_text_871_ = leanh::lean_ctor_get(v_doc_870_, 3);
                leanh::lean_inc_ref(v_text_871_);
                v_uri_872_ = leanh::lean_ctor_get(v_doc_870_, 0);
                leanh::lean_inc_ref(v_uri_872_);
                leanh::lean_dec_ref(v_doc_870_);
                v_source_873_ = leanh::lean_ctor_get(v_text_871_, 0);
                leanh::lean_inc_ref(v_source_873_);
                v___x_878_ = l_System_Uri_fileUriToPath_x3f(v_uri_872_);
                if leanh::lean_obj_tag(v___x_878_) == 0 {
                    v___y_875_ = v_uri_872_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_uri_872_);
                    v_val_879_ = leanh::lean_ctor_get(v___x_878_, 0);
                    leanh::lean_inc(v_val_879_);
                    leanh::lean_dec_ref_known(v___x_878_, 1);
                    v___y_875_ = v_val_879_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_876_ = lean_string_utf8_byte_size(v_source_873_);
                v___x_877_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_877_, 0, v_source_873_);
                leanh::lean_ctor_set(v___x_877_, 1, v___y_875_);
                leanh::lean_ctor_set(v___x_877_, 2, v_text_871_);
                leanh::lean_ctor_set(v___x_877_, 3, v___x_876_);
                return v___x_877_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_replaceLspRange(
    mut v_text_880_: *mut leanh::LeanObject,
    mut v_r_881_: *mut leanh::LeanObject,
    mut v_newText_882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_start_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_end_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_end_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_post_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_start_883_ = leanh::lean_ctor_get(v_r_881_, 0);
    leanh::lean_inc_ref(v_start_883_);
    v_end_884_ = leanh::lean_ctor_get(v_r_881_, 1);
    leanh::lean_inc_ref(v_end_884_);
    leanh::lean_dec_ref(v_r_881_);
    v_source_885_ = leanh::lean_ctor_get(v_text_880_, 0);
    v_start_886_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_880_, v_start_883_);
    v_end_887_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_880_, v_end_884_);
    v___x_888_ = leanh::lean_unsigned_to_nat(0);
    v_pre_889_ = lean_string_utf8_extract(v_source_885_, v___x_888_, v_start_886_);
    leanh::lean_dec(v_start_886_);
    v___x_890_ = lean_string_utf8_byte_size(v_source_885_);
    v_post_891_ = lean_string_utf8_extract(v_source_885_, v_end_887_, v___x_890_);
    leanh::lean_dec(v_end_887_);
    v___x_892_ = l_String_crlfToLf(v_newText_882_);
    v___x_893_ = lean_string_append(v_pre_889_, v___x_892_);
    leanh::lean_dec_ref(v___x_892_);
    v___x_894_ = lean_string_append(v___x_893_, v_post_891_);
    leanh::lean_dec_ref(v_post_891_);
    v___x_895_ = l_String_toFileMap(v___x_894_);
    return v___x_895_;
}
pub unsafe fn l_Lean_Server_replaceLspRange___boxed(
    mut v_text_896_: *mut leanh::LeanObject,
    mut v_r_897_: *mut leanh::LeanObject,
    mut v_newText_898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_899_ = l_Lean_Server_replaceLspRange(v_text_896_, v_r_897_, v_newText_898_);
    leanh::lean_dec_ref(v_newText_898_);
    leanh::lean_dec_ref(v_text_896_);
    return v_res_899_;
}
pub unsafe fn l_Lean_Server_applyDocumentChange(
    mut v_oldText_900_: *mut leanh::LeanObject,
    mut v_x_901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_901_) == 0 {
        let mut v_range_902_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_text_903_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_range_902_ = leanh::lean_ctor_get(v_x_901_, 0);
        leanh::lean_inc_ref(v_range_902_);
        v_text_903_ = leanh::lean_ctor_get(v_x_901_, 1);
        leanh::lean_inc_ref(v_text_903_);
        leanh::lean_dec_ref_known(v_x_901_, 2);
        v___x_904_ = l_Lean_Server_replaceLspRange(v_oldText_900_, v_range_902_, v_text_903_);
        leanh::lean_dec_ref(v_text_903_);
        return v___x_904_;
    } else {
        let mut v_text_905_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_906_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_text_905_ = leanh::lean_ctor_get(v_x_901_, 0);
        leanh::lean_inc_ref(v_text_905_);
        leanh::lean_dec_ref_known(v_x_901_, 1);
        v___x_906_ = l_String_crlfToLf(v_text_905_);
        leanh::lean_dec_ref(v_text_905_);
        v___x_907_ = l_String_toFileMap(v___x_906_);
        return v___x_907_;
    }
}
pub unsafe fn l_Lean_Server_applyDocumentChange___boxed(
    mut v_oldText_908_: *mut leanh::LeanObject,
    mut v_x_909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_910_ = l_Lean_Server_applyDocumentChange(v_oldText_908_, v_x_909_);
    leanh::lean_dec_ref(v_oldText_908_);
    return v_res_910_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0(
    mut v_as_911_: *mut leanh::LeanObject,
    mut v_i_912_: usize,
    mut v_stop_913_: usize,
    mut v_b_914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_915_: u8 = 0;
    let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: usize = 0;
    let mut v___x_919_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_915_ = lean_usize_dec_eq(v_i_912_, v_stop_913_);
                if v___x_915_ == 0 {
                    v___x_916_ = lean_array_uget_borrowed(v_as_911_, v_i_912_);
                    leanh::lean_inc(v___x_916_);
                    v___x_917_ = l_Lean_Server_applyDocumentChange(v_b_914_, v___x_916_);
                    leanh::lean_dec_ref(v_b_914_);
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
    mut v_as_921_: *mut leanh::LeanObject,
    mut v_i_922_: *mut leanh::LeanObject,
    mut v_stop_923_: *mut leanh::LeanObject,
    mut v_b_924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_925_: usize = 0;
    let mut v_stop_boxed_926_: usize = 0;
    let mut v_res_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_925_ = leanh::lean_unbox_usize(v_i_922_);
    leanh::lean_dec(v_i_922_);
    v_stop_boxed_926_ = leanh::lean_unbox_usize(v_stop_923_);
    leanh::lean_dec(v_stop_923_);
    v_res_927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0(v_as_921_, v_i_boxed_925_, v_stop_boxed_926_, v_b_924_);
    leanh::lean_dec_ref(v_as_921_);
    return v_res_927_;
}
pub unsafe fn l_Lean_Server_foldDocumentChanges(
    mut v_changes_928_: *mut leanh::LeanObject,
    mut v_oldText_929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: u8 = 0;
    v___x_930_ = leanh::lean_unsigned_to_nat(0);
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
                let mut v___x_936_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_934_ = 0usize;
                v___x_935_ = lean_usize_of_nat(v___x_931_);
                v___x_936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0(v_changes_928_, v___x_934_, v___x_935_, v_oldText_929_);
                return v___x_936_;
            }
        } else {
            let mut v___x_937_: usize = 0;
            let mut v___x_938_: usize = 0;
            let mut v___x_939_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_937_ = 0usize;
            v___x_938_ = lean_usize_of_nat(v___x_931_);
            v___x_939_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0(v_changes_928_, v___x_937_, v___x_938_, v_oldText_929_);
            return v___x_939_;
        }
    }
}
pub unsafe fn l_Lean_Server_foldDocumentChanges___boxed(
    mut v_changes_940_: *mut leanh::LeanObject,
    mut v_oldText_941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_942_ = l_Lean_Server_foldDocumentChanges(v_changes_940_, v_oldText_941_);
    leanh::lean_dec_ref(v_changes_940_);
    return v_res_942_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Server_mkPublishDiagnosticsNotification_spec__0(
    mut v_a_943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_944_ = lean_nat_to_int(v_a_943_);
    return v___x_944_;
}
pub unsafe fn l_Lean_Server_mkPublishDiagnosticsNotification(
    mut v_m_946_: *mut leanh::LeanObject,
    mut v_diagnostics_947_: *mut leanh::LeanObject,
    mut v_isIncremental_948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_uri_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_uri_949_ = leanh::lean_ctor_get(v_m_946_, 0);
    leanh::lean_inc_ref(v_uri_949_);
    v_version_950_ = leanh::lean_ctor_get(v_m_946_, 2);
    leanh::lean_inc(v_version_950_);
    leanh::lean_dec_ref(v_m_946_);
    v___x_951_ = l_Lean_Server_mkPublishDiagnosticsNotification___closed__0;
    v___x_952_ = lean_nat_to_int(v_version_950_);
    v___x_953_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_953_, 0, v___x_952_);
    v___x_954_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_954_, 0, v_uri_949_);
    leanh::lean_ctor_set(v___x_954_, 1, v___x_953_);
    leanh::lean_ctor_set(v___x_954_, 2, v_isIncremental_948_);
    leanh::lean_ctor_set(v___x_954_, 3, v_diagnostics_947_);
    v___x_955_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_955_, 0, v___x_951_);
    leanh::lean_ctor_set(v___x_955_, 1, v___x_954_);
    return v___x_955_;
}
pub unsafe fn l_Lean_Server_mkFileProgressNotification(
    mut v_m_957_: *mut leanh::LeanObject,
    mut v_processing_958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_uri_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_version_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_uri_959_ = leanh::lean_ctor_get(v_m_957_, 0);
    v_version_960_ = leanh::lean_ctor_get(v_m_957_, 2);
    v___x_961_ = l_Lean_Server_mkFileProgressNotification___closed__0;
    leanh::lean_inc(v_version_960_);
    v___x_962_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_962_, 0, v_version_960_);
    leanh::lean_inc_ref(v_uri_959_);
    v___x_963_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_963_, 0, v_uri_959_);
    leanh::lean_ctor_set(v___x_963_, 1, v___x_962_);
    v___x_964_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_964_, 0, v___x_963_);
    leanh::lean_ctor_set(v___x_964_, 1, v_processing_958_);
    v___x_965_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_965_, 0, v___x_961_);
    leanh::lean_ctor_set(v___x_965_, 1, v___x_964_);
    return v___x_965_;
}
pub unsafe fn l_Lean_Server_mkFileProgressNotification___boxed(
    mut v_m_966_: *mut leanh::LeanObject,
    mut v_processing_967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_968_ = l_Lean_Server_mkFileProgressNotification(v_m_966_, v_processing_967_);
    leanh::lean_dec_ref(v_m_966_);
    return v_res_968_;
}
pub unsafe fn l_Lean_Server_mkFileProgressAtPosNotification(
    mut v_m_969_: *mut leanh::LeanObject,
    mut v_pos_970_: *mut leanh::LeanObject,
    mut v_kind_971_: u8,
) -> *mut leanh::LeanObject {
    let mut v_text_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_text_972_ = leanh::lean_ctor_get(v_m_969_, 3);
    v_source_973_ = leanh::lean_ctor_get(v_text_972_, 0);
    leanh::lean_inc_ref_n(v_text_972_, 2);
    v___x_974_ = l_Lean_FileMap_utf8PosToLspPos(v_text_972_, v_pos_970_);
    v___x_975_ = lean_string_utf8_byte_size(v_source_973_);
    v___x_976_ = l_Lean_FileMap_utf8PosToLspPos(v_text_972_, v___x_975_);
    v___x_977_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_977_, 0, v___x_974_);
    leanh::lean_ctor_set(v___x_977_, 1, v___x_976_);
    v___x_978_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_978_, 0, v___x_977_);
    leanh::lean_ctor_set_uint8(
        v___x_978_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_kind_971_,
    );
    v___x_979_ = leanh::lean_unsigned_to_nat(1);
    v___x_980_ = lean_mk_empty_array_with_capacity(v___x_979_);
    v___x_981_ = lean_array_push(v___x_980_, v___x_978_);
    v___x_982_ = l_Lean_Server_mkFileProgressNotification(v_m_969_, v___x_981_);
    leanh::lean_dec_ref(v_m_969_);
    return v___x_982_;
}
pub unsafe fn l_Lean_Server_mkFileProgressAtPosNotification___boxed(
    mut v_m_983_: *mut leanh::LeanObject,
    mut v_pos_984_: *mut leanh::LeanObject,
    mut v_kind_985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_986_: u8 = 0;
    let mut v_res_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_986_ = (leanh::lean_unbox(v_kind_985_) as u8);
    v_res_987_ =
        l_Lean_Server_mkFileProgressAtPosNotification(v_m_983_, v_pos_984_, v_kind_boxed_986_);
    leanh::lean_dec(v_pos_984_);
    return v_res_987_;
}
pub unsafe fn l_Lean_Server_mkFileProgressDoneNotification(
    mut v_m_990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_991_ = l_Lean_Server_mkFileProgressDoneNotification___closed__0;
    v___x_992_ = l_Lean_Server_mkFileProgressNotification(v_m_990_, v___x_991_);
    return v___x_992_;
}
pub unsafe fn l_Lean_Server_mkFileProgressDoneNotification___boxed(
    mut v_m_993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_994_ = l_Lean_Server_mkFileProgressDoneNotification(v_m_993_);
    leanh::lean_dec_ref(v_m_993_);
    return v_res_994_;
}
pub unsafe fn l_Lean_Server_mkApplyWorkspaceEditRequest(
    mut v_params_998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_999_ = l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0;
    v___x_1000_ = l_Lean_Server_mkApplyWorkspaceEditRequest___closed__1;
    v___x_1001_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1001_, 0, v___x_1000_);
    leanh::lean_ctor_set(v___x_1001_, 1, v___x_999_);
    leanh::lean_ctor_set(v___x_1001_, 2, v_params_998_);
    return v___x_1001_;
}
pub unsafe fn l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(
    mut v_uri_1003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1004_ = leanh::lean_box(0);
    v___x_1005_ = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0;
    v___x_1006_ = lean_string_append(v___x_1005_, v_uri_1003_);
    v___x_1007_ = l_Lean_Name_str___override(v___x_1004_, v___x_1006_);
    return v___x_1007_;
}
pub unsafe fn l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___boxed(
    mut v_uri_1008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1009_ = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(v_uri_1008_);
    leanh::lean_dec_ref(v_uri_1008_);
    return v_res_1009_;
}
pub unsafe fn _init_l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1010_ = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0;
    v___x_1011_ = lean_string_utf8_byte_size(v___x_1010_);
    return v___x_1011_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg(
    mut v_s_1012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: u8 = 0;
    v___x_1013_ = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0;
    v___x_1014_ = lean_string_utf8_byte_size(v_s_1012_);
    v___x_1015_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg___closed__0_once), _init_l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg___closed__0);
    v___x_1016_ = lean_nat_dec_le(v___x_1015_, v___x_1014_);
    if v___x_1016_ == 0 {
        let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_s_1012_);
        v___x_1017_ = leanh::lean_box(0);
        return v___x_1017_;
    } else {
        let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1019_: u8 = 0;
        v___x_1018_ = leanh::lean_unsigned_to_nat(0);
        v___x_1019_ = lean_string_memcmp(
            v_s_1012_,
            v___x_1013_,
            v___x_1018_,
            v___x_1018_,
            v___x_1015_,
        );
        if v___x_1019_ == 0 {
            let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_s_1012_);
            v___x_1020_ = leanh::lean_box(0);
            return v___x_1020_;
        } else {
            let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_s_1012_);
            v___x_1021_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_1021_, 0, v_s_1012_);
            leanh::lean_ctor_set(v___x_1021_, 1, v___x_1018_);
            leanh::lean_ctor_set(v___x_1021_, 2, v___x_1014_);
            v___x_1022_ = l_String_Slice_pos_x21(v___x_1021_, v___x_1015_);
            leanh::lean_dec_ref_known(v___x_1021_, 3);
            v___x_1023_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_1023_, 0, v_s_1012_);
            leanh::lean_ctor_set(v___x_1023_, 1, v___x_1022_);
            leanh::lean_ctor_set(v___x_1023_, 2, v___x_1014_);
            v___x_1024_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1024_, 0, v___x_1023_);
            return v___x_1024_;
        }
    }
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0(
    mut v_s_1025_: *mut leanh::LeanObject,
    mut v_pat_1026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1027_ = l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg(v_s_1025_);
    return v___x_1027_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___boxed(
    mut v_s_1028_: *mut leanh::LeanObject,
    mut v_pat_1029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1030_ = l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0(v_s_1028_, v_pat_1029_);
    leanh::lean_dec_ref(v_pat_1029_);
    return v_res_1030_;
}
pub unsafe fn l___private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f(
    mut v_name_1031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pre_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1039_: u8 = 0;
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1044_: u8 = 0;
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_name_1031_) == 1 {
                    v_pre_1032_ = leanh::lean_ctor_get(v_name_1031_, 0);
                    if leanh::lean_obj_tag(v_pre_1032_) == 0 {
                        v_str_1033_ = leanh::lean_ctor_get(v_name_1031_, 1);
                        leanh::lean_inc_ref(v_str_1033_);
                        leanh::lean_dec_ref_known(v_name_1031_, 2);
                        v___x_1034_ = l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg(v_str_1033_);
                        if leanh::lean_obj_tag(v___x_1034_) == 0 {
                            v___x_1035_ = leanh::lean_box(0);
                            return v___x_1035_;
                        } else {
                            v_val_1036_ = leanh::lean_ctor_get(v___x_1034_, 0);
                            v_isSharedCheck_1044_ =
                                (!leanh::lean_is_exclusive(v___x_1034_)) as u8;
                            if v_isSharedCheck_1044_ == 0 {
                                v___x_1038_ = v___x_1034_;
                                v_isShared_1039_ = v_isSharedCheck_1044_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_1036_);
                                leanh::lean_dec(v___x_1034_);
                                v___x_1038_ = leanh::lean_box(0);
                                v_isShared_1039_ = v_isSharedCheck_1044_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_name_1031_, 2);
                        v___x_1045_ = leanh::lean_box(0);
                        return v___x_1045_;
                    }
                } else {
                    leanh::lean_dec(v_name_1031_);
                    v___x_1046_ = leanh::lean_box(0);
                    return v___x_1046_;
                }
            }
            1 => {
                v___x_1040_ = l_String_Slice_toString(v_val_1036_);
                leanh::lean_dec(v_val_1036_);
                if v_isShared_1039_ == 0 {
                    leanh::lean_ctor_set(v___x_1038_, 0, v___x_1040_);
                    v___x_1042_ = v___x_1038_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1043_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1040_);
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
    mut v_modName_1048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1059_: u8 = 0;
    let mut v_val_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1063_: u8 = 0;
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1068_: u8 = 0;
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1076_: u8 = 0;
    let mut v_a_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1080_: u8 = 0;
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1084_: u8 = 0;
    let mut v_isSharedCheck_1085_: u8 = 0;
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1090_: u8 = 0;
    let mut v_a_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1094_: u8 = 0;
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1098_: u8 = 0;
    let mut v_a_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1102_: u8 = 0;
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_modName_1048_);
                v___x_1050_ = l___private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f(
                    v_modName_1048_,
                );
                if leanh::lean_obj_tag(v___x_1050_) == 1 {
                    leanh::lean_dec(v_modName_1048_);
                    v___x_1051_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1051_, 0, v___x_1050_);
                    return v___x_1051_;
                } else {
                    leanh::lean_dec(v___x_1050_);
                    v___x_1052_ = l_Lean_getSrcSearchPath();
                    if leanh::lean_obj_tag(v___x_1052_) == 0 {
                        v_a_1053_ = leanh::lean_ctor_get(v___x_1052_, 0);
                        leanh::lean_inc(v_a_1053_);
                        leanh::lean_dec_ref_known(v___x_1052_, 1);
                        v___x_1054_ = l_Lean_Server_documentUriFromModule_x3f___closed__0;
                        v___x_1055_ = l_Lean_SearchPath_findModuleWithExt(
                            v_a_1053_,
                            v___x_1054_,
                            v_modName_1048_,
                        );
                        if leanh::lean_obj_tag(v___x_1055_) == 0 {
                            v_a_1056_ = leanh::lean_ctor_get(v___x_1055_, 0);
                            v_isSharedCheck_1090_ =
                                (!leanh::lean_is_exclusive(v___x_1055_)) as u8;
                            if v_isSharedCheck_1090_ == 0 {
                                v___x_1058_ = v___x_1055_;
                                v_isShared_1059_ = v_isSharedCheck_1090_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1056_);
                                leanh::lean_dec(v___x_1055_);
                                v___x_1058_ = leanh::lean_box(0);
                                v_isShared_1059_ = v_isSharedCheck_1090_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_1091_ = leanh::lean_ctor_get(v___x_1055_, 0);
                            v_isSharedCheck_1098_ =
                                (!leanh::lean_is_exclusive(v___x_1055_)) as u8;
                            if v_isSharedCheck_1098_ == 0 {
                                v___x_1093_ = v___x_1055_;
                                v_isShared_1094_ = v_isSharedCheck_1098_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1091_);
                                leanh::lean_dec(v___x_1055_);
                                v___x_1093_ = leanh::lean_box(0);
                                v_isShared_1094_ = v_isSharedCheck_1098_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_modName_1048_);
                        v_a_1099_ = leanh::lean_ctor_get(v___x_1052_, 0);
                        v_isSharedCheck_1106_ =
                            (!leanh::lean_is_exclusive(v___x_1052_)) as u8;
                        if v_isSharedCheck_1106_ == 0 {
                            v___x_1101_ = v___x_1052_;
                            v_isShared_1102_ = v_isSharedCheck_1106_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1099_);
                            leanh::lean_dec(v___x_1052_);
                            v___x_1101_ = leanh::lean_box(0);
                            v_isShared_1102_ = v_isSharedCheck_1106_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_1056_) == 1 {
                    leanh::lean_del_object(v___x_1058_);
                    v_val_1060_ = leanh::lean_ctor_get(v_a_1056_, 0);
                    v_isSharedCheck_1085_ = (!leanh::lean_is_exclusive(v_a_1056_)) as u8;
                    if v_isSharedCheck_1085_ == 0 {
                        v___x_1062_ = v_a_1056_;
                        v_isShared_1063_ = v_isSharedCheck_1085_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1060_);
                        leanh::lean_dec(v_a_1056_);
                        v___x_1062_ = leanh::lean_box(0);
                        v_isShared_1063_ = v_isSharedCheck_1085_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1056_);
                    v___x_1086_ = leanh::lean_box(0);
                    if v_isShared_1059_ == 0 {
                        leanh::lean_ctor_set(v___x_1058_, 0, v___x_1086_);
                        v___x_1088_ = v___x_1058_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1089_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
                        v___x_1088_ = v_reuseFailAlloc_1089_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1064_ = lean_io_realpath(v_val_1060_);
                if leanh::lean_obj_tag(v___x_1064_) == 0 {
                    v_a_1065_ = leanh::lean_ctor_get(v___x_1064_, 0);
                    v_isSharedCheck_1076_ = (!leanh::lean_is_exclusive(v___x_1064_)) as u8;
                    if v_isSharedCheck_1076_ == 0 {
                        v___x_1067_ = v___x_1064_;
                        v_isShared_1068_ = v_isSharedCheck_1076_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1065_);
                        leanh::lean_dec(v___x_1064_);
                        v___x_1067_ = leanh::lean_box(0);
                        v_isShared_1068_ = v_isSharedCheck_1076_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1062_);
                    v_a_1077_ = leanh::lean_ctor_get(v___x_1064_, 0);
                    v_isSharedCheck_1084_ = (!leanh::lean_is_exclusive(v___x_1064_)) as u8;
                    if v_isSharedCheck_1084_ == 0 {
                        v___x_1079_ = v___x_1064_;
                        v_isShared_1080_ = v_isSharedCheck_1084_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1077_);
                        leanh::lean_dec(v___x_1064_);
                        v___x_1079_ = leanh::lean_box(0);
                        v_isShared_1080_ = v_isSharedCheck_1084_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1069_ = l_System_Uri_pathToUri(v_a_1065_);
                if v_isShared_1063_ == 0 {
                    leanh::lean_ctor_set(v___x_1062_, 0, v___x_1069_);
                    v___x_1071_ = v___x_1062_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1075_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1069_);
                    v___x_1071_ = v_reuseFailAlloc_1075_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1068_ == 0 {
                    leanh::lean_ctor_set(v___x_1067_, 0, v___x_1071_);
                    v___x_1073_ = v___x_1067_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1074_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1071_);
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
                    v_reuseFailAlloc_1083_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
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
                    v_reuseFailAlloc_1097_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
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
                    v_reuseFailAlloc_1105_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
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
    mut v_modName_1107_: *mut leanh::LeanObject,
    mut v_a_1108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1109_ = l_Lean_Server_documentUriFromModule_x3f(v_modName_1107_);
    return v_res_1109_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0(
    mut v_x_1110_: *mut leanh::LeanObject,
    mut v_x_1111_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_1110_) == 0 {
        if leanh::lean_obj_tag(v_x_1111_) == 0 {
            let mut v___x_1112_: u8 = 0;
            v___x_1112_ = 1;
            return v___x_1112_;
        } else {
            let mut v___x_1113_: u8 = 0;
            v___x_1113_ = 0;
            return v___x_1113_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_1111_) == 0 {
            let mut v___x_1114_: u8 = 0;
            v___x_1114_ = 0;
            return v___x_1114_;
        } else {
            let mut v_val_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1117_: u8 = 0;
            v_val_1115_ = leanh::lean_ctor_get(v_x_1110_, 0);
            v_val_1116_ = leanh::lean_ctor_get(v_x_1111_, 0);
            v___x_1117_ = lean_string_dec_eq(v_val_1115_, v_val_1116_);
            return v___x_1117_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0___boxed(
    mut v_x_1118_: *mut leanh::LeanObject,
    mut v_x_1119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1120_: u8 = 0;
    let mut v_r_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1120_ = l_Option_instBEq_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0(
        v_x_1118_, v_x_1119_,
    );
    leanh::lean_dec(v_x_1119_);
    leanh::lean_dec(v_x_1118_);
    v_r_1121_ = leanh::lean_box((v_res_1120_) as usize);
    return v_r_1121_;
}
pub unsafe fn l_Lean_Server_moduleFromDocumentUri(
    mut v_uri_1124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1130_: u8 = 0;
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: u8 = 0;
    let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1144_: u8 = 0;
    let mut v_val_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1153_: u8 = 0;
    let mut v_a_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1157_: u8 = 0;
    let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1161_: u8 = 0;
    let mut v_a_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1165_: u8 = 0;
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1169_: u8 = 0;
    let mut v_isSharedCheck_1170_: u8 = 0;
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1126_ = l_System_Uri_fileUriToPath_x3f(v_uri_1124_);
                if leanh::lean_obj_tag(v___x_1126_) == 1 {
                    v_val_1127_ = leanh::lean_ctor_get(v___x_1126_, 0);
                    v_isSharedCheck_1170_ = (!leanh::lean_is_exclusive(v___x_1126_)) as u8;
                    if v_isSharedCheck_1170_ == 0 {
                        v___x_1129_ = v___x_1126_;
                        v_isShared_1130_ = v_isSharedCheck_1170_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1127_);
                        leanh::lean_dec(v___x_1126_);
                        v___x_1129_ = leanh::lean_box(0);
                        v_isShared_1130_ = v_isSharedCheck_1170_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1126_);
                    v___x_1171_ =
                        l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(v_uri_1124_);
                    v___x_1172_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1172_, 0, v___x_1171_);
                    return v___x_1172_;
                }
            }
            1 => {
                leanh::lean_inc(v_val_1127_);
                v___x_1131_ = l_System_FilePath_extension(v_val_1127_);
                v___x_1132_ = l_Lean_Server_moduleFromDocumentUri___closed__0;
                v___x_1133_ =
                    l_Option_instBEq_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0(
                        v___x_1131_,
                        v___x_1132_,
                    );
                leanh::lean_dec(v___x_1131_);
                if v___x_1133_ == 0 {
                    leanh::lean_dec(v_val_1127_);
                    v___x_1134_ =
                        l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(v_uri_1124_);
                    if v_isShared_1130_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1129_, 0);
                        leanh::lean_ctor_set(v___x_1129_, 0, v___x_1134_);
                        v___x_1136_ = v___x_1129_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1137_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
                        v___x_1136_ = v_reuseFailAlloc_1137_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1129_);
                    v___x_1138_ = l_Lean_getSrcSearchPath();
                    if leanh::lean_obj_tag(v___x_1138_) == 0 {
                        v_a_1139_ = leanh::lean_ctor_get(v___x_1138_, 0);
                        leanh::lean_inc(v_a_1139_);
                        leanh::lean_dec_ref_known(v___x_1138_, 1);
                        v___x_1140_ = l_Lean_searchModuleNameOfFileName(v_val_1127_, v_a_1139_);
                        leanh::lean_dec(v_a_1139_);
                        if leanh::lean_obj_tag(v___x_1140_) == 0 {
                            v_a_1141_ = leanh::lean_ctor_get(v___x_1140_, 0);
                            v_isSharedCheck_1153_ =
                                (!leanh::lean_is_exclusive(v___x_1140_)) as u8;
                            if v_isSharedCheck_1153_ == 0 {
                                v___x_1143_ = v___x_1140_;
                                v_isShared_1144_ = v_isSharedCheck_1153_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1141_);
                                leanh::lean_dec(v___x_1140_);
                                v___x_1143_ = leanh::lean_box(0);
                                v_isShared_1144_ = v_isSharedCheck_1153_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_a_1154_ = leanh::lean_ctor_get(v___x_1140_, 0);
                            v_isSharedCheck_1161_ =
                                (!leanh::lean_is_exclusive(v___x_1140_)) as u8;
                            if v_isSharedCheck_1161_ == 0 {
                                v___x_1156_ = v___x_1140_;
                                v_isShared_1157_ = v_isSharedCheck_1161_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1154_);
                                leanh::lean_dec(v___x_1140_);
                                v___x_1156_ = leanh::lean_box(0);
                                v_isShared_1157_ = v_isSharedCheck_1161_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_val_1127_);
                        v_a_1162_ = leanh::lean_ctor_get(v___x_1138_, 0);
                        v_isSharedCheck_1169_ =
                            (!leanh::lean_is_exclusive(v___x_1138_)) as u8;
                        if v_isSharedCheck_1169_ == 0 {
                            v___x_1164_ = v___x_1138_;
                            v_isShared_1165_ = v_isSharedCheck_1169_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1162_);
                            leanh::lean_dec(v___x_1138_);
                            v___x_1164_ = leanh::lean_box(0);
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
                if leanh::lean_obj_tag(v_a_1141_) == 1 {
                    v_val_1145_ = leanh::lean_ctor_get(v_a_1141_, 0);
                    leanh::lean_inc(v_val_1145_);
                    leanh::lean_dec_ref_known(v_a_1141_, 1);
                    if v_isShared_1144_ == 0 {
                        leanh::lean_ctor_set(v___x_1143_, 0, v_val_1145_);
                        v___x_1147_ = v___x_1143_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1148_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_val_1145_);
                        v___x_1147_ = v_reuseFailAlloc_1148_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1141_);
                    v___x_1149_ =
                        l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(v_uri_1124_);
                    if v_isShared_1144_ == 0 {
                        leanh::lean_ctor_set(v___x_1143_, 0, v___x_1149_);
                        v___x_1151_ = v___x_1143_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1152_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
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
                    v_reuseFailAlloc_1160_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
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
                    v_reuseFailAlloc_1168_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
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
    mut v_uri_1173_: *mut leanh::LeanObject,
    mut v_a_1174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1175_ = l_Lean_Server_moduleFromDocumentUri(v_uri_1173_);
    leanh::lean_dec_ref(v_uri_1173_);
    return v_res_1175_;
}
pub unsafe fn l_Lean_Syntax_Range_toLspRange(
    mut v_text_1176_: *mut leanh::LeanObject,
    mut v_r_1177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_start_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1182_: u8 = 0;
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1188_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_1178_ = leanh::lean_ctor_get(v_r_1177_, 0);
                v_stop_1179_ = leanh::lean_ctor_get(v_r_1177_, 1);
                v_isSharedCheck_1188_ = (!leanh::lean_is_exclusive(v_r_1177_)) as u8;
                if v_isSharedCheck_1188_ == 0 {
                    v___x_1181_ = v_r_1177_;
                    v_isShared_1182_ = v_isSharedCheck_1188_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_stop_1179_);
                    leanh::lean_inc(v_start_1178_);
                    leanh::lean_dec(v_r_1177_);
                    v___x_1181_ = leanh::lean_box(0);
                    v_isShared_1182_ = v_isSharedCheck_1188_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_text_1176_);
                v___x_1183_ = l_Lean_FileMap_utf8PosToLspPos(v_text_1176_, v_start_1178_);
                leanh::lean_dec(v_start_1178_);
                v___x_1184_ = l_Lean_FileMap_utf8PosToLspPos(v_text_1176_, v_stop_1179_);
                leanh::lean_dec(v_stop_1179_);
                if v_isShared_1182_ == 0 {
                    leanh::lean_ctor_set(v___x_1181_, 1, v___x_1184_);
                    leanh::lean_ctor_set(v___x_1181_, 0, v___x_1183_);
                    v___x_1186_ = v___x_1181_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1187_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1183_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1187_, 1, v___x_1184_);
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
pub unsafe fn runtime_initialize_Lean_Server_Utils(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_Uri(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Communication(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Diagnostics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_InfoUtils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Server_instInhabitedDocumentMeta_default =
        _init_l_Lean_Server_instInhabitedDocumentMeta_default();
    leanh::lean_mark_persistent(l_Lean_Server_instInhabitedDocumentMeta_default);
    l_Lean_Server_instInhabitedDocumentMeta = _init_l_Lean_Server_instInhabitedDocumentMeta();
    leanh::lean_mark_persistent(l_Lean_Server_instInhabitedDocumentMeta);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_Utils(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_Utils(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_Uri(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Lsp_Communication(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Lsp_Diagnostics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Lsp_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Server_InfoUtils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Utils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_Utils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Server_Utils(builtin);
}
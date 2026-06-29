// Lean compiler output
// Module: Lean.Server.FileWorker.SignatureHelp
// Imports: Lean.Server.InfoUtils Lean.Data.Lsp Init.Data.List.Sort.Basic Lean.PrettyPrinter.Delaborator
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::List::Sort::Basic::{
    initialize_Init_Data_List_Sort_Basic, l_List_mergeSort___redArg,
    runtime_initialize_Init_Data_List_Sort_Basic,
};
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_pos_x21;
use crate::r#gen::Init::Data::String::FindPos::l_String_Slice_posGE___redArg;
use crate::r#gen::Init::Data::String::Pattern::String::l_String_Slice_Pattern_ForwardSliceSearcher_buildTable;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_hasArgs;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull,
};
use crate::r#gen::Lean::Data::Lsp::{initialize_Lean_Data_Lsp, runtime_initialize_Lean_Data_Lsp};
use crate::r#gen::Lean::Data::Position::{l_Lean_FileMap_lineStart, l_Lean_FileMap_toPosition};
use crate::r#gen::Lean::Elab::InfoTree::Main::l_Lean_Elab_ContextInfo_runMetaM___redArg;
use crate::r#gen::Lean::Expr::{l_Lean_Expr_hasMVar, l_Lean_Expr_isForall};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::PrettyPrinter::Delaborator::Basic::l_Lean_PrettyPrinter_delabCore___redArg;
use crate::r#gen::Lean::PrettyPrinter::Delaborator::Builtins::l_Lean_PrettyPrinter_Delaborator_delabForallWithSignature___boxed;
use crate::r#gen::Lean::PrettyPrinter::Delaborator::{
    initialize_Lean_PrettyPrinter_Delaborator, runtime_initialize_Lean_PrettyPrinter_Delaborator,
};
use crate::r#gen::Lean::PrettyPrinter::l_Lean_PrettyPrinter_ppTerm;
use crate::r#gen::Lean::Server::InfoUtils::{
    initialize_Lean_Server_InfoUtils, l_Lean_Elab_InfoTree_smallestInfo_x3f,
    runtime_initialize_Lean_Server_InfoUtils,
};
use crate::r#gen::Lean::Syntax::{
    l_Lean_Syntax_Range_contains, l_Lean_Syntax_findStack_x3f,
    l_Lean_Syntax_getRangeWithTrailing_x3f, l_Lean_Syntax_instBEqRange_beq,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_extract, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::PosRaw::lean_string_get_byte_fast;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_mk, lean_array_push,
    lean_array_to_list, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_utf8_byte_size,
    lean_uint8_dec_eq, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
pub static l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Delaborator_delabForallWithSignature___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [45, 45, 0]};
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2: u8 = 0;
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__6_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__3_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [112, 105, 112, 101, 80, 114, 111, 106, 0]};
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__3_value) as *mut crate::leanh::LeanObject,1787791066222317160 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 114, 111, 106, 0]};
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__5_value) as *mut crate::leanh::LeanObject,5353940006376281447 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__7_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [100, 111, 116, 73, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__7_value) as *mut crate::leanh::LeanObject,14183307858573822893 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__14_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__14_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__14_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__16_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 101, 114, 109, 95, 60, 124, 95, 0]};
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__16_value) as *mut crate::leanh::LeanObject,5917499938696079000 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__18_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 101, 114, 109, 95, 36, 95, 95, 0]};
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__19_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__18_value) as *mut crate::leanh::LeanObject,7247595903597861139 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__21_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__22_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__23_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__2_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__0_value:
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
static mut l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__1_value:
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
    m_fun: l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__1_value
) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0(
    mut v_x_996_: *mut crate::leanh::LeanObject,
    mut v_x_997_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_996_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_997_) == 0 {
            let mut v___x_998_: u8 = 0;
            v___x_998_ = 1;
            return v___x_998_;
        } else {
            let mut v___x_999_: u8 = 0;
            v___x_999_ = 0;
            return v___x_999_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_997_) == 0 {
            let mut v___x_1000_: u8 = 0;
            v___x_1000_ = 0;
            return v___x_1000_;
        } else {
            let mut v_val_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1003_: u8 = 0;
            v_val_1001_ = crate::leanh::lean_ctor_get(v_x_996_, 0);
            v_val_1002_ = crate::leanh::lean_ctor_get(v_x_997_, 0);
            v___x_1003_ = l_Lean_Syntax_instBEqRange_beq(v_val_1001_, v_val_1002_);
            return v___x_1003_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0___boxed(
    mut v_x_1004_: *mut crate::leanh::LeanObject,
    mut v_x_1005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1006_: u8 = 0;
    let mut v_r_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1006_ = l_Option_instBEq_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0(v_x_1004_, v_x_1005_);
    crate::leanh::lean_dec(v_x_1005_);
    crate::leanh::lean_dec(v_x_1004_);
    v_r_1007_ = crate::leanh::lean_box((v_res_1006_) as usize);
    return v_r_1007_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg(
    mut v_e_1008_: *mut crate::leanh::LeanObject,
    mut v___y_1009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1011_: u8 = 0;
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1025_: u8 = 0;
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1031_: u8 = 0;
    let mut v_unused_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1011_ = l_Lean_Expr_hasMVar(v_e_1008_);
                if v___x_1011_ == 0 {
                    v___x_1012_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1012_, 0, v_e_1008_);
                    return v___x_1012_;
                } else {
                    v___x_1013_ = lean_st_ref_get(v___y_1009_);
                    v_mctx_1014_ = crate::leanh::lean_ctor_get(v___x_1013_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_1014_);
                    crate::leanh::lean_dec(v___x_1013_);
                    v___x_1015_ = l_Lean_instantiateMVarsCore(v_mctx_1014_, v_e_1008_);
                    v_fst_1016_ = crate::leanh::lean_ctor_get(v___x_1015_, 0);
                    crate::leanh::lean_inc(v_fst_1016_);
                    v_snd_1017_ = crate::leanh::lean_ctor_get(v___x_1015_, 1);
                    crate::leanh::lean_inc(v_snd_1017_);
                    crate::leanh::lean_dec_ref(v___x_1015_);
                    v___x_1018_ = lean_st_ref_take(v___y_1009_);
                    v_cache_1019_ = crate::leanh::lean_ctor_get(v___x_1018_, 1);
                    v_zetaDeltaFVarIds_1020_ = crate::leanh::lean_ctor_get(v___x_1018_, 2);
                    v_postponed_1021_ = crate::leanh::lean_ctor_get(v___x_1018_, 3);
                    v_diag_1022_ = crate::leanh::lean_ctor_get(v___x_1018_, 4);
                    v_isSharedCheck_1031_ = (!crate::leanh::lean_is_exclusive(v___x_1018_)) as u8;
                    if v_isSharedCheck_1031_ == 0 {
                        v_unused_1032_ = crate::leanh::lean_ctor_get(v___x_1018_, 0);
                        crate::leanh::lean_dec(v_unused_1032_);
                        v___x_1024_ = v___x_1018_;
                        v_isShared_1025_ = v_isSharedCheck_1031_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_1022_);
                        crate::leanh::lean_inc(v_postponed_1021_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_1020_);
                        crate::leanh::lean_inc(v_cache_1019_);
                        crate::leanh::lean_dec(v___x_1018_);
                        v___x_1024_ = crate::leanh::lean_box(0);
                        v_isShared_1025_ = v_isSharedCheck_1031_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1025_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1024_, 0, v_snd_1017_);
                    v___x_1027_ = v___x_1024_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1030_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_snd_1017_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_cache_1019_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1030_,
                        2,
                        v_zetaDeltaFVarIds_1020_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1030_, 3, v_postponed_1021_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1030_, 4, v_diag_1022_);
                    v___x_1027_ = v_reuseFailAlloc_1030_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1028_ = lean_st_ref_set(v___y_1009_, v___x_1027_);
                v___x_1029_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1029_, 0, v_fst_1016_);
                return v___x_1029_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg___boxed(
    mut v_e_1033_: *mut crate::leanh::LeanObject,
    mut v___y_1034_: *mut crate::leanh::LeanObject,
    mut v___y_1035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1036_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg(v_e_1033_, v___y_1034_);
    crate::leanh::lean_dec(v___y_1034_);
    return v_res_1036_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1(
    mut v_e_1037_: *mut crate::leanh::LeanObject,
    mut v___y_1038_: *mut crate::leanh::LeanObject,
    mut v___y_1039_: *mut crate::leanh::LeanObject,
    mut v___y_1040_: *mut crate::leanh::LeanObject,
    mut v___y_1041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1043_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg(v_e_1037_, v___y_1039_);
    return v___x_1043_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___boxed(
    mut v_e_1044_: *mut crate::leanh::LeanObject,
    mut v___y_1045_: *mut crate::leanh::LeanObject,
    mut v___y_1046_: *mut crate::leanh::LeanObject,
    mut v___y_1047_: *mut crate::leanh::LeanObject,
    mut v___y_1048_: *mut crate::leanh::LeanObject,
    mut v___y_1049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1050_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1(v_e_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
    crate::leanh::lean_dec(v___y_1048_);
    crate::leanh::lean_dec_ref(v___y_1047_);
    crate::leanh::lean_dec(v___y_1046_);
    crate::leanh::lean_dec_ref(v___y_1045_);
    return v_res_1050_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__0(
    mut v_appStx_1051_: *mut crate::leanh::LeanObject,
    mut v_x_1052_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1052_) == 1 {
        let mut v_i_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toElabInfo_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_stx_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1056_: u8 = 0;
        let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1059_: u8 = 0;
        v_i_1053_ = crate::leanh::lean_ctor_get(v_x_1052_, 0);
        v_toElabInfo_1054_ = crate::leanh::lean_ctor_get(v_i_1053_, 0);
        v_stx_1055_ = crate::leanh::lean_ctor_get(v_toElabInfo_1054_, 1);
        v___x_1056_ = 0;
        v___x_1057_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_1055_, v___x_1056_);
        v___x_1058_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_appStx_1051_, v___x_1056_);
        v___x_1059_ = l_Option_instBEq_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0(v___x_1057_, v___x_1058_);
        crate::leanh::lean_dec(v___x_1058_);
        crate::leanh::lean_dec(v___x_1057_);
        return v___x_1059_;
    } else {
        let mut v___x_1060_: u8 = 0;
        v___x_1060_ = 0;
        return v___x_1060_;
    }
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__0___boxed(
    mut v_appStx_1061_: *mut crate::leanh::LeanObject,
    mut v_x_1062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1063_: u8 = 0;
    let mut v_r_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1063_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__0(
        v_appStx_1061_,
        v_x_1062_,
    );
    crate::leanh::lean_dec_ref(v_x_1062_);
    crate::leanh::lean_dec(v_appStx_1061_);
    v_r_1064_ = crate::leanh::lean_box((v_res_1063_) as usize);
    return v_r_1064_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1(
    mut v_expr_1066_: *mut crate::leanh::LeanObject,
    mut v___y_1067_: *mut crate::leanh::LeanObject,
    mut v___y_1068_: *mut crate::leanh::LeanObject,
    mut v___y_1069_: *mut crate::leanh::LeanObject,
    mut v___y_1070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1078_: u8 = 0;
    let mut v___x_1079_: u8 = 0;
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1093_: u8 = 0;
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1098_: u8 = 0;
    let mut v_a_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1102_: u8 = 0;
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1106_: u8 = 0;
    let mut v_a_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1110_: u8 = 0;
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1114_: u8 = 0;
    let mut v_isSharedCheck_1115_: u8 = 0;
    let mut v_a_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1119_: u8 = 0;
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1123_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_1070_);
                crate::leanh::lean_inc_ref(v___y_1069_);
                crate::leanh::lean_inc(v___y_1068_);
                crate::leanh::lean_inc_ref(v___y_1067_);
                v___x_1072_ = lean_infer_type(
                    v_expr_1066_,
                    v___y_1067_,
                    v___y_1068_,
                    v___y_1069_,
                    v___y_1070_,
                );
                if crate::leanh::lean_obj_tag(v___x_1072_) == 0 {
                    v_a_1073_ = crate::leanh::lean_ctor_get(v___x_1072_, 0);
                    crate::leanh::lean_inc(v_a_1073_);
                    crate::leanh::lean_dec_ref_known(v___x_1072_, 1);
                    v___x_1074_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg(v_a_1073_, v___y_1068_);
                    v_a_1075_ = crate::leanh::lean_ctor_get(v___x_1074_, 0);
                    v_isSharedCheck_1115_ = (!crate::leanh::lean_is_exclusive(v___x_1074_)) as u8;
                    if v_isSharedCheck_1115_ == 0 {
                        v___x_1077_ = v___x_1074_;
                        v_isShared_1078_ = v_isSharedCheck_1115_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1075_);
                        crate::leanh::lean_dec(v___x_1074_);
                        v___x_1077_ = crate::leanh::lean_box(0);
                        v_isShared_1078_ = v_isSharedCheck_1115_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_1070_);
                    crate::leanh::lean_dec_ref(v___y_1069_);
                    crate::leanh::lean_dec(v___y_1068_);
                    crate::leanh::lean_dec_ref(v___y_1067_);
                    v_a_1116_ = crate::leanh::lean_ctor_get(v___x_1072_, 0);
                    v_isSharedCheck_1123_ = (!crate::leanh::lean_is_exclusive(v___x_1072_)) as u8;
                    if v_isSharedCheck_1123_ == 0 {
                        v___x_1118_ = v___x_1072_;
                        v_isShared_1119_ = v_isSharedCheck_1123_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1116_);
                        crate::leanh::lean_dec(v___x_1072_);
                        v___x_1118_ = crate::leanh::lean_box(0);
                        v_isShared_1119_ = v_isSharedCheck_1123_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1079_ = l_Lean_Expr_isForall(v_a_1075_);
                if v___x_1079_ == 0 {
                    crate::leanh::lean_dec(v_a_1075_);
                    crate::leanh::lean_dec(v___y_1070_);
                    crate::leanh::lean_dec_ref(v___y_1069_);
                    crate::leanh::lean_dec(v___y_1068_);
                    crate::leanh::lean_dec_ref(v___y_1067_);
                    v___x_1080_ = crate::leanh::lean_box(0);
                    if v_isShared_1078_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1077_, 0, v___x_1080_);
                        v___x_1082_ = v___x_1077_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1083_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
                        v___x_1082_ = v_reuseFailAlloc_1083_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1077_);
                    v___x_1084_ = crate::leanh::lean_box(1);
                    v___x_1085_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1___closed__0;
                    v___x_1086_ = l_Lean_PrettyPrinter_delabCore___redArg(
                        v_a_1075_,
                        v___x_1084_,
                        v___x_1085_,
                        v___y_1067_,
                        v___y_1068_,
                        v___y_1069_,
                        v___y_1070_,
                    );
                    crate::leanh::lean_dec(v___y_1068_);
                    crate::leanh::lean_dec_ref(v___y_1067_);
                    if crate::leanh::lean_obj_tag(v___x_1086_) == 0 {
                        v_a_1087_ = crate::leanh::lean_ctor_get(v___x_1086_, 0);
                        crate::leanh::lean_inc(v_a_1087_);
                        crate::leanh::lean_dec_ref_known(v___x_1086_, 1);
                        v_fst_1088_ = crate::leanh::lean_ctor_get(v_a_1087_, 0);
                        crate::leanh::lean_inc(v_fst_1088_);
                        crate::leanh::lean_dec(v_a_1087_);
                        v___x_1089_ =
                            l_Lean_PrettyPrinter_ppTerm(v_fst_1088_, v___y_1069_, v___y_1070_);
                        crate::leanh::lean_dec(v___y_1070_);
                        crate::leanh::lean_dec_ref(v___y_1069_);
                        if crate::leanh::lean_obj_tag(v___x_1089_) == 0 {
                            v_a_1090_ = crate::leanh::lean_ctor_get(v___x_1089_, 0);
                            v_isSharedCheck_1098_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1089_)) as u8;
                            if v_isSharedCheck_1098_ == 0 {
                                v___x_1092_ = v___x_1089_;
                                v_isShared_1093_ = v_isSharedCheck_1098_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1090_);
                                crate::leanh::lean_dec(v___x_1089_);
                                v___x_1092_ = crate::leanh::lean_box(0);
                                v_isShared_1093_ = v_isSharedCheck_1098_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_a_1099_ = crate::leanh::lean_ctor_get(v___x_1089_, 0);
                            v_isSharedCheck_1106_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1089_)) as u8;
                            if v_isSharedCheck_1106_ == 0 {
                                v___x_1101_ = v___x_1089_;
                                v_isShared_1102_ = v_isSharedCheck_1106_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1099_);
                                crate::leanh::lean_dec(v___x_1089_);
                                v___x_1101_ = crate::leanh::lean_box(0);
                                v_isShared_1102_ = v_isSharedCheck_1106_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_1070_);
                        crate::leanh::lean_dec_ref(v___y_1069_);
                        v_a_1107_ = crate::leanh::lean_ctor_get(v___x_1086_, 0);
                        v_isSharedCheck_1114_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1086_)) as u8;
                        if v_isSharedCheck_1114_ == 0 {
                            v___x_1109_ = v___x_1086_;
                            v_isShared_1110_ = v_isSharedCheck_1114_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1107_);
                            crate::leanh::lean_dec(v___x_1086_);
                            v___x_1109_ = crate::leanh::lean_box(0);
                            v_isShared_1110_ = v_isSharedCheck_1114_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1082_;
            }
            3 => {
                v___x_1094_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1094_, 0, v_a_1090_);
                if v_isShared_1093_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1092_, 0, v___x_1094_);
                    v___x_1096_ = v___x_1092_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1097_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
                    v___x_1096_ = v_reuseFailAlloc_1097_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1096_;
            }
            5 => {
                if v_isShared_1102_ == 0 {
                    v___x_1104_ = v___x_1101_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1105_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
                    v___x_1104_ = v_reuseFailAlloc_1105_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1104_;
            }
            7 => {
                if v_isShared_1110_ == 0 {
                    v___x_1112_ = v___x_1109_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1113_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
                    v___x_1112_ = v_reuseFailAlloc_1113_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1112_;
            }
            9 => {
                if v_isShared_1119_ == 0 {
                    v___x_1121_ = v___x_1118_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1122_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
                    v___x_1121_ = v_reuseFailAlloc_1122_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1121_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1___boxed(
    mut v_expr_1124_: *mut crate::leanh::LeanObject,
    mut v___y_1125_: *mut crate::leanh::LeanObject,
    mut v___y_1126_: *mut crate::leanh::LeanObject,
    mut v___y_1127_: *mut crate::leanh::LeanObject,
    mut v___y_1128_: *mut crate::leanh::LeanObject,
    mut v___y_1129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1130_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1(
        v_expr_1124_,
        v___y_1125_,
        v___y_1126_,
        v___y_1127_,
        v___y_1128_,
    );
    return v_res_1130_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp(
    mut v_tree_1133_: *mut crate::leanh::LeanObject,
    mut v_appStx_1134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1152_: u8 = 0;
    let mut v_val_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1156_: u8 = 0;
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1173_: u8 = 0;
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1178_: u8 = 0;
    let mut v_a_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1182_: u8 = 0;
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1186_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1139_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1139_, 0, v_appStx_1134_);
                v___x_1140_ = l_Lean_Elab_InfoTree_smallestInfo_x3f(v___f_1139_, v_tree_1133_);
                if crate::leanh::lean_obj_tag(v___x_1140_) == 1 {
                    v_val_1141_ = crate::leanh::lean_ctor_get(v___x_1140_, 0);
                    crate::leanh::lean_inc(v_val_1141_);
                    crate::leanh::lean_dec_ref_known(v___x_1140_, 1);
                    v_snd_1142_ = crate::leanh::lean_ctor_get(v_val_1141_, 1);
                    if crate::leanh::lean_obj_tag(v_snd_1142_) == 1 {
                        v_i_1143_ = crate::leanh::lean_ctor_get(v_snd_1142_, 0);
                        crate::leanh::lean_inc_ref(v_i_1143_);
                        v_fst_1144_ = crate::leanh::lean_ctor_get(v_val_1141_, 0);
                        crate::leanh::lean_inc(v_fst_1144_);
                        crate::leanh::lean_dec(v_val_1141_);
                        v_lctx_1145_ = crate::leanh::lean_ctor_get(v_i_1143_, 1);
                        crate::leanh::lean_inc_ref(v_lctx_1145_);
                        v_expr_1146_ = crate::leanh::lean_ctor_get(v_i_1143_, 3);
                        crate::leanh::lean_inc_ref(v_expr_1146_);
                        crate::leanh::lean_dec_ref(v_i_1143_);
                        v___f_1147_ = crate::leanh::lean_alloc_closure(l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1___boxed as *mut core::ffi::c_void, 6, 1);
                        crate::leanh::lean_closure_set(v___f_1147_, 0, v_expr_1146_);
                        v___x_1148_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(
                            v_fst_1144_,
                            v_lctx_1145_,
                            v___f_1147_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1148_) == 0 {
                            v_a_1149_ = crate::leanh::lean_ctor_get(v___x_1148_, 0);
                            v_isSharedCheck_1178_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1148_)) as u8;
                            if v_isSharedCheck_1178_ == 0 {
                                v___x_1151_ = v___x_1148_;
                                v_isShared_1152_ = v_isSharedCheck_1178_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1149_);
                                crate::leanh::lean_dec(v___x_1148_);
                                v___x_1151_ = crate::leanh::lean_box(0);
                                v_isShared_1152_ = v_isSharedCheck_1178_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_a_1179_ = crate::leanh::lean_ctor_get(v___x_1148_, 0);
                            v_isSharedCheck_1186_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1148_)) as u8;
                            if v_isSharedCheck_1186_ == 0 {
                                v___x_1181_ = v___x_1148_;
                                v_isShared_1182_ = v_isSharedCheck_1186_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1179_);
                                crate::leanh::lean_dec(v___x_1148_);
                                v___x_1181_ = crate::leanh::lean_box(0);
                                v_isShared_1182_ = v_isSharedCheck_1186_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_1141_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1140_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1137_ = crate::leanh::lean_box(0);
                v___x_1138_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1138_, 0, v___x_1137_);
                return v___x_1138_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_1149_) == 1 {
                    v_val_1153_ = crate::leanh::lean_ctor_get(v_a_1149_, 0);
                    v_isSharedCheck_1173_ = (!crate::leanh::lean_is_exclusive(v_a_1149_)) as u8;
                    if v_isSharedCheck_1173_ == 0 {
                        v___x_1155_ = v_a_1149_;
                        v_isShared_1156_ = v_isSharedCheck_1173_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1153_);
                        crate::leanh::lean_dec(v_a_1149_);
                        v___x_1155_ = crate::leanh::lean_box(0);
                        v_isShared_1156_ = v_isSharedCheck_1173_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1149_);
                    v___x_1174_ = crate::leanh::lean_box(0);
                    if v_isShared_1152_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1151_, 0, v___x_1174_);
                        v___x_1176_ = v___x_1151_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1177_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1174_);
                        v___x_1176_ = v_reuseFailAlloc_1177_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1157_ = l_Std_Format_defWidth;
                v___x_1158_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1159_ =
                    l_Std_Format_pretty(v_val_1153_, v___x_1157_, v___x_1158_, v___x_1158_);
                v___x_1160_ = crate::leanh::lean_box(0);
                v___x_1161_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1161_, 0, v___x_1159_);
                crate::leanh::lean_ctor_set(v___x_1161_, 1, v___x_1160_);
                crate::leanh::lean_ctor_set(v___x_1161_, 2, v___x_1160_);
                crate::leanh::lean_ctor_set(v___x_1161_, 3, v___x_1160_);
                v___x_1162_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1163_ = lean_mk_empty_array_with_capacity(v___x_1162_);
                v___x_1164_ = lean_array_push(v___x_1163_, v___x_1161_);
                v___x_1165_ =
                    l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___closed__0;
                v___x_1166_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1166_, 0, v___x_1164_);
                crate::leanh::lean_ctor_set(v___x_1166_, 1, v___x_1165_);
                crate::leanh::lean_ctor_set(v___x_1166_, 2, v___x_1160_);
                if v_isShared_1156_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1155_, 0, v___x_1166_);
                    v___x_1168_ = v___x_1155_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1172_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1166_);
                    v___x_1168_ = v_reuseFailAlloc_1172_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1152_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1151_, 0, v___x_1168_);
                    v___x_1170_ = v___x_1151_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1171_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
                    v___x_1170_ = v_reuseFailAlloc_1171_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1170_;
            }
            6 => {
                return v___x_1176_;
            }
            7 => {
                if v_isShared_1182_ == 0 {
                    v___x_1184_ = v___x_1181_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1185_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
                    v___x_1184_ = v_reuseFailAlloc_1185_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1184_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___boxed(
    mut v_tree_1187_: *mut crate::leanh::LeanObject,
    mut v_appStx_1188_: *mut crate::leanh::LeanObject,
    mut v_a_1189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1190_ =
        l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp(v_tree_1187_, v_appStx_1188_);
    return v_res_1190_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx(
    mut v_x_1191_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_1191_ {
        0 => {
            let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1192_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1192_;
        }
        1 => {
            let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1193_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1193_;
        }
        _ => {
            let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1194_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1194_;
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx___boxed(
    mut v_x_1195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_1196_: u8 = 0;
    let mut v_res_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1196_ = (crate::leanh::lean_unbox(v_x_1195_) as u8);
    v_res_1197_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx(v_x_boxed_1196_);
    return v_res_1197_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_toCtorIdx(
    mut v_x_1198_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1199_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx(v_x_1198_);
    return v___x_1199_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_toCtorIdx___boxed(
    mut v_x_1200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_1201_: u8 = 0;
    let mut v_res_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1201_ = (crate::leanh::lean_unbox(v_x_1200_) as u8);
    v_res_1202_ =
        l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_toCtorIdx(v_x_4__boxed_1201_);
    return v_res_1202_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___redArg(
    mut v_k_1203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1203_);
    return v_k_1203_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___redArg___boxed(
    mut v_k_1204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1205_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___redArg(v_k_1204_);
    crate::leanh::lean_dec(v_k_1204_);
    return v_res_1205_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim(
    mut v_motive_1206_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1207_: *mut crate::leanh::LeanObject,
    mut v_t_1208_: u8,
    mut v_h_1209_: *mut crate::leanh::LeanObject,
    mut v_k_1210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1210_);
    return v_k_1210_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___boxed(
    mut v_motive_1211_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1212_: *mut crate::leanh::LeanObject,
    mut v_t_1213_: *mut crate::leanh::LeanObject,
    mut v_h_1214_: *mut crate::leanh::LeanObject,
    mut v_k_1215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1216_: u8 = 0;
    let mut v_res_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1216_ = (crate::leanh::lean_unbox(v_t_1213_) as u8);
    v_res_1217_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim(
        v_motive_1211_,
        v_ctorIdx_1212_,
        v_t_boxed_1216_,
        v_h_1214_,
        v_k_1215_,
    );
    crate::leanh::lean_dec(v_k_1215_);
    crate::leanh::lean_dec(v_ctorIdx_1212_);
    return v_res_1217_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___redArg(
    mut v_pipeArg_1218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pipeArg_1218_);
    return v_pipeArg_1218_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___redArg___boxed(
    mut v_pipeArg_1219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1220_ =
        l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___redArg(v_pipeArg_1219_);
    crate::leanh::lean_dec(v_pipeArg_1219_);
    return v_res_1220_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim(
    mut v_motive_1221_: *mut crate::leanh::LeanObject,
    mut v_t_1222_: u8,
    mut v_h_1223_: *mut crate::leanh::LeanObject,
    mut v_pipeArg_1224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_pipeArg_1224_);
    return v_pipeArg_1224_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___boxed(
    mut v_motive_1225_: *mut crate::leanh::LeanObject,
    mut v_t_1226_: *mut crate::leanh::LeanObject,
    mut v_h_1227_: *mut crate::leanh::LeanObject,
    mut v_pipeArg_1228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1229_: u8 = 0;
    let mut v_res_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1229_ = (crate::leanh::lean_unbox(v_t_1226_) as u8);
    v_res_1230_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim(
        v_motive_1225_,
        v_t_boxed_1229_,
        v_h_1227_,
        v_pipeArg_1228_,
    );
    crate::leanh::lean_dec(v_pipeArg_1228_);
    return v_res_1230_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___redArg(
    mut v_termArg_1231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_termArg_1231_);
    return v_termArg_1231_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___redArg___boxed(
    mut v_termArg_1232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1233_ =
        l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___redArg(v_termArg_1232_);
    crate::leanh::lean_dec(v_termArg_1232_);
    return v_res_1233_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim(
    mut v_motive_1234_: *mut crate::leanh::LeanObject,
    mut v_t_1235_: u8,
    mut v_h_1236_: *mut crate::leanh::LeanObject,
    mut v_termArg_1237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_termArg_1237_);
    return v_termArg_1237_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___boxed(
    mut v_motive_1238_: *mut crate::leanh::LeanObject,
    mut v_t_1239_: *mut crate::leanh::LeanObject,
    mut v_h_1240_: *mut crate::leanh::LeanObject,
    mut v_termArg_1241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1242_: u8 = 0;
    let mut v_res_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1242_ = (crate::leanh::lean_unbox(v_t_1239_) as u8);
    v_res_1243_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim(
        v_motive_1238_,
        v_t_boxed_1242_,
        v_h_1240_,
        v_termArg_1241_,
    );
    crate::leanh::lean_dec(v_termArg_1241_);
    return v_res_1243_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___redArg(
    mut v_appArg_1244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_appArg_1244_);
    return v_appArg_1244_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___redArg___boxed(
    mut v_appArg_1245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1246_ =
        l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___redArg(v_appArg_1245_);
    crate::leanh::lean_dec(v_appArg_1245_);
    return v_res_1246_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim(
    mut v_motive_1247_: *mut crate::leanh::LeanObject,
    mut v_t_1248_: u8,
    mut v_h_1249_: *mut crate::leanh::LeanObject,
    mut v_appArg_1250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_appArg_1250_);
    return v_appArg_1250_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___boxed(
    mut v_motive_1251_: *mut crate::leanh::LeanObject,
    mut v_t_1252_: *mut crate::leanh::LeanObject,
    mut v_h_1253_: *mut crate::leanh::LeanObject,
    mut v_appArg_1254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1255_: u8 = 0;
    let mut v_res_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1255_ = (crate::leanh::lean_unbox(v_t_1252_) as u8);
    v_res_1256_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim(
        v_motive_1251_,
        v_t_boxed_1255_,
        v_h_1253_,
        v_appArg_1254_,
    );
    crate::leanh::lean_dec(v_appArg_1254_);
    return v_res_1256_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(
    mut v_x_1257_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_1257_ {
        0 => {
            let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1258_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1258_;
        }
        1 => {
            let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1259_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1259_;
        }
        _ => {
            let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1260_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1260_;
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio___boxed(
    mut v_x_1261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_34__boxed_1262_: u8 = 0;
    let mut v_res_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_34__boxed_1262_ = (crate::leanh::lean_unbox(v_x_1261_) as u8);
    v_res_1263_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_x_34__boxed_1262_);
    return v_res_1263_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx(
    mut v_x_1264_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_x_1264_ == 0 {
        let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1265_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_1265_;
    } else {
        let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1266_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_1266_;
    }
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx___boxed(
    mut v_x_1267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_1268_: u8 = 0;
    let mut v_res_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1268_ = (crate::leanh::lean_unbox(v_x_1267_) as u8);
    v_res_1269_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx(v_x_boxed_1268_);
    return v_res_1269_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_toCtorIdx(
    mut v_x_1270_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1271_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx(v_x_1270_);
    return v___x_1271_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_toCtorIdx___boxed(
    mut v_x_1272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_1273_: u8 = 0;
    let mut v_res_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1273_ = (crate::leanh::lean_unbox(v_x_1272_) as u8);
    v_res_1274_ =
        l_Lean_Server_FileWorker_SignatureHelp_SearchControl_toCtorIdx(v_x_4__boxed_1273_);
    return v_res_1274_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___redArg(
    mut v_k_1275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1275_);
    return v_k_1275_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___redArg___boxed(
    mut v_k_1276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1277_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___redArg(v_k_1276_);
    crate::leanh::lean_dec(v_k_1276_);
    return v_res_1277_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim(
    mut v_motive_1278_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1279_: *mut crate::leanh::LeanObject,
    mut v_t_1280_: u8,
    mut v_h_1281_: *mut crate::leanh::LeanObject,
    mut v_k_1282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1282_);
    return v_k_1282_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___boxed(
    mut v_motive_1283_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1284_: *mut crate::leanh::LeanObject,
    mut v_t_1285_: *mut crate::leanh::LeanObject,
    mut v_h_1286_: *mut crate::leanh::LeanObject,
    mut v_k_1287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1288_: u8 = 0;
    let mut v_res_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1288_ = (crate::leanh::lean_unbox(v_t_1285_) as u8);
    v_res_1289_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim(
        v_motive_1283_,
        v_ctorIdx_1284_,
        v_t_boxed_1288_,
        v_h_1286_,
        v_k_1287_,
    );
    crate::leanh::lean_dec(v_k_1287_);
    crate::leanh::lean_dec(v_ctorIdx_1284_);
    return v_res_1289_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___redArg(
    mut v_continue_1290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_continue_1290_);
    return v_continue_1290_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___redArg___boxed(
    mut v_continue_1291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1292_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___redArg(
        v_continue_1291_,
    );
    crate::leanh::lean_dec(v_continue_1291_);
    return v_res_1292_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim(
    mut v_motive_1293_: *mut crate::leanh::LeanObject,
    mut v_t_1294_: u8,
    mut v_h_1295_: *mut crate::leanh::LeanObject,
    mut v_continue_1296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_continue_1296_);
    return v_continue_1296_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___boxed(
    mut v_motive_1297_: *mut crate::leanh::LeanObject,
    mut v_t_1298_: *mut crate::leanh::LeanObject,
    mut v_h_1299_: *mut crate::leanh::LeanObject,
    mut v_continue_1300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1301_: u8 = 0;
    let mut v_res_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1301_ = (crate::leanh::lean_unbox(v_t_1298_) as u8);
    v_res_1302_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim(
        v_motive_1297_,
        v_t_boxed_1301_,
        v_h_1299_,
        v_continue_1300_,
    );
    crate::leanh::lean_dec(v_continue_1300_);
    return v_res_1302_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___redArg(
    mut v_stop_1303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_stop_1303_);
    return v_stop_1303_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___redArg___boxed(
    mut v_stop_1304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1305_ =
        l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___redArg(v_stop_1304_);
    crate::leanh::lean_dec(v_stop_1304_);
    return v_res_1305_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim(
    mut v_motive_1306_: *mut crate::leanh::LeanObject,
    mut v_t_1307_: u8,
    mut v_h_1308_: *mut crate::leanh::LeanObject,
    mut v_stop_1309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_stop_1309_);
    return v_stop_1309_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___boxed(
    mut v_motive_1310_: *mut crate::leanh::LeanObject,
    mut v_t_1311_: *mut crate::leanh::LeanObject,
    mut v_h_1312_: *mut crate::leanh::LeanObject,
    mut v_stop_1313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1314_: u8 = 0;
    let mut v_res_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1314_ = (crate::leanh::lean_unbox(v_t_1311_) as u8);
    v_res_1315_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim(
        v_motive_1310_,
        v_t_boxed_1314_,
        v_h_1312_,
        v_stop_1313_,
    );
    crate::leanh::lean_dec(v_stop_1313_);
    return v_res_1315_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(
    mut v_s_1316_: *mut crate::leanh::LeanObject,
    mut v___x_1317_: *mut crate::leanh::LeanObject,
    mut v___x_1318_: *mut crate::leanh::LeanObject,
    mut v_a_1319_: *mut crate::leanh::LeanObject,
    mut v_b_1320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1327_: u8 = 0;
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1333_: u8 = 0;
    let mut v_needle_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_table_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stackPos_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_needlePos_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1340_: u8 = 0;
    let mut v_str_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basePos_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: u8 = 0;
    let mut v___x_1348_: u8 = 0;
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stackByte_1351_: u8 = 0;
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_patByte_1353_: u8 = 0;
    let mut v___x_1354_: u8 = 0;
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: u8 = 0;
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNeedlePos_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: u8 = 0;
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextNeedlePos_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: u8 = 0;
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1388_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1321_ = crate::leanh::lean_box(0);
                match crate::leanh::lean_obj_tag(v_a_1319_) {
                    0 => {
                        v_pos_1322_ = crate::leanh::lean_ctor_get(v_a_1319_, 0);
                        crate::leanh::lean_inc(v_pos_1322_);
                        crate::leanh::lean_dec_ref_known(v_a_1319_, 1);
                        v___x_1323_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1323_, 0, v_pos_1322_);
                        return v___x_1323_;
                    }
                    1 => {
                        v_pos_1324_ = crate::leanh::lean_ctor_get(v_a_1319_, 0);
                        v_isSharedCheck_1333_ = (!crate::leanh::lean_is_exclusive(v_a_1319_)) as u8;
                        if v_isSharedCheck_1333_ == 0 {
                            v___x_1326_ = v_a_1319_;
                            v_isShared_1327_ = v_isSharedCheck_1333_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_pos_1324_);
                            crate::leanh::lean_dec(v_a_1319_);
                            v___x_1326_ = crate::leanh::lean_box(0);
                            v_isShared_1327_ = v_isSharedCheck_1333_;
                            state = 1;
                            continue;
                        }
                    }
                    2 => {
                        v_needle_1334_ = crate::leanh::lean_ctor_get(v_a_1319_, 0);
                        v_table_1335_ = crate::leanh::lean_ctor_get(v_a_1319_, 1);
                        v_stackPos_1336_ = crate::leanh::lean_ctor_get(v_a_1319_, 2);
                        v_needlePos_1337_ = crate::leanh::lean_ctor_get(v_a_1319_, 3);
                        v_isSharedCheck_1388_ = (!crate::leanh::lean_is_exclusive(v_a_1319_)) as u8;
                        if v_isSharedCheck_1388_ == 0 {
                            v___x_1339_ = v_a_1319_;
                            v_isShared_1340_ = v_isSharedCheck_1388_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_needlePos_1337_);
                            crate::leanh::lean_inc(v_stackPos_1336_);
                            crate::leanh::lean_inc(v_table_1335_);
                            crate::leanh::lean_inc(v_needle_1334_);
                            crate::leanh::lean_dec(v_a_1319_);
                            v___x_1339_ = crate::leanh::lean_box(0);
                            v_isShared_1340_ = v_isSharedCheck_1388_;
                            state = 3;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_inc(v_b_1320_);
                        return v_b_1320_;
                    }
                }
            }
            1 => {
                v___x_1328_ = lean_string_utf8_next_fast(v_s_1316_, v_pos_1324_);
                crate::leanh::lean_dec(v_pos_1324_);
                if v_isShared_1327_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1326_, 0);
                    crate::leanh::lean_ctor_set(v___x_1326_, 0, v___x_1328_);
                    v___x_1330_ = v___x_1326_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1332_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1328_);
                    v___x_1330_ = v_reuseFailAlloc_1332_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1319_ = v___x_1330_;
                v_b_1320_ = v___x_1321_;
                state = 0;
                continue;
            }
            3 => {
                v_str_1341_ = crate::leanh::lean_ctor_get(v_needle_1334_, 0);
                v_startInclusive_1342_ = crate::leanh::lean_ctor_get(v_needle_1334_, 1);
                v_endExclusive_1343_ = crate::leanh::lean_ctor_get(v_needle_1334_, 2);
                v_basePos_1344_ = lean_nat_sub(v_stackPos_1336_, v_needlePos_1337_);
                v___x_1345_ = lean_nat_sub(v_endExclusive_1343_, v_startInclusive_1342_);
                v___x_1346_ = lean_nat_add(v_basePos_1344_, v___x_1345_);
                v___x_1347_ = lean_nat_dec_le(v___x_1346_, v___x_1318_);
                crate::leanh::lean_dec(v___x_1346_);
                if v___x_1347_ == 0 {
                    crate::leanh::lean_dec(v___x_1345_);
                    crate::leanh::lean_del_object(v___x_1339_);
                    crate::leanh::lean_dec(v_needlePos_1337_);
                    crate::leanh::lean_dec(v_stackPos_1336_);
                    crate::leanh::lean_dec_ref(v_table_1335_);
                    crate::leanh::lean_dec_ref(v_needle_1334_);
                    v___x_1348_ = lean_nat_dec_lt(v_basePos_1344_, v___x_1318_);
                    crate::leanh::lean_dec(v_basePos_1344_);
                    if v___x_1348_ == 0 {
                        crate::leanh::lean_inc(v_b_1320_);
                        return v_b_1320_;
                    } else {
                        v___x_1349_ = crate::leanh::lean_box(3);
                        v_a_1319_ = v___x_1349_;
                        v_b_1320_ = v___x_1321_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_basePos_1344_);
                    crate::leanh::lean_inc(v_stackPos_1336_);
                    v_stackByte_1351_ = lean_string_get_byte_fast(v_s_1316_, v_stackPos_1336_);
                    v___x_1352_ = lean_nat_add(v_startInclusive_1342_, v_needlePos_1337_);
                    v_patByte_1353_ = lean_string_get_byte_fast(v_str_1341_, v___x_1352_);
                    v___x_1354_ = lean_uint8_dec_eq(v_stackByte_1351_, v_patByte_1353_);
                    if v___x_1354_ == 0 {
                        crate::leanh::lean_dec(v___x_1345_);
                        v___x_1355_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1356_ = lean_nat_dec_eq(v_needlePos_1337_, v___x_1355_);
                        if v___x_1356_ == 0 {
                            v___x_1357_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1358_ = lean_nat_sub(v_needlePos_1337_, v___x_1357_);
                            crate::leanh::lean_dec(v_needlePos_1337_);
                            v_newNeedlePos_1359_ =
                                lean_array_fget_borrowed(v_table_1335_, v___x_1358_);
                            crate::leanh::lean_dec(v___x_1358_);
                            v___x_1360_ = lean_nat_dec_eq(v_newNeedlePos_1359_, v___x_1355_);
                            if v___x_1360_ == 0 {
                                crate::leanh::lean_inc(v_newNeedlePos_1359_);
                                if v_isShared_1340_ == 0 {
                                    crate::leanh::lean_ctor_set(
                                        v___x_1339_,
                                        3,
                                        v_newNeedlePos_1359_,
                                    );
                                    v___x_1362_ = v___x_1339_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1364_ =
                                        crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1364_,
                                        0,
                                        v_needle_1334_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1364_,
                                        1,
                                        v_table_1335_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1364_,
                                        2,
                                        v_stackPos_1336_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1364_,
                                        3,
                                        v_newNeedlePos_1359_,
                                    );
                                    v___x_1362_ = v_reuseFailAlloc_1364_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                v_nextStackPos_1365_ =
                                    l_String_Slice_posGE___redArg(v___x_1317_, v_stackPos_1336_);
                                if v_isShared_1340_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1339_, 3, v___x_1355_);
                                    crate::leanh::lean_ctor_set(
                                        v___x_1339_,
                                        2,
                                        v_nextStackPos_1365_,
                                    );
                                    v___x_1367_ = v___x_1339_;
                                    state = 5;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1369_ =
                                        crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1369_,
                                        0,
                                        v_needle_1334_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1369_,
                                        1,
                                        v_table_1335_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1369_,
                                        2,
                                        v_nextStackPos_1365_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1369_,
                                        3,
                                        v___x_1355_,
                                    );
                                    v___x_1367_ = v_reuseFailAlloc_1369_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_needlePos_1337_);
                            v___x_1370_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1371_ = lean_nat_add(v_stackPos_1336_, v___x_1370_);
                            crate::leanh::lean_dec(v_stackPos_1336_);
                            v_nextStackPos_1372_ =
                                l_String_Slice_posGE___redArg(v___x_1317_, v___x_1371_);
                            if v_isShared_1340_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1339_, 3, v___x_1355_);
                                crate::leanh::lean_ctor_set(v___x_1339_, 2, v_nextStackPos_1372_);
                                v___x_1374_ = v___x_1339_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_1376_ =
                                    crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1376_,
                                    0,
                                    v_needle_1334_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1376_,
                                    1,
                                    v_table_1335_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1376_,
                                    2,
                                    v_nextStackPos_1372_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 3, v___x_1355_);
                                v___x_1374_ = v_reuseFailAlloc_1376_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        v___x_1377_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_nextStackPos_1378_ = lean_nat_add(v_stackPos_1336_, v___x_1377_);
                        crate::leanh::lean_dec(v_stackPos_1336_);
                        v_nextNeedlePos_1379_ = lean_nat_add(v_needlePos_1337_, v___x_1377_);
                        crate::leanh::lean_dec(v_needlePos_1337_);
                        v___x_1380_ = lean_nat_dec_eq(v_nextNeedlePos_1379_, v___x_1345_);
                        crate::leanh::lean_dec(v___x_1345_);
                        if v___x_1380_ == 0 {
                            if v_isShared_1340_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1339_, 3, v_nextNeedlePos_1379_);
                                crate::leanh::lean_ctor_set(v___x_1339_, 2, v_nextStackPos_1378_);
                                v___x_1382_ = v___x_1339_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_1384_ =
                                    crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1384_,
                                    0,
                                    v_needle_1334_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1384_,
                                    1,
                                    v_table_1335_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1384_,
                                    2,
                                    v_nextStackPos_1378_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1384_,
                                    3,
                                    v_nextNeedlePos_1379_,
                                );
                                v___x_1382_ = v_reuseFailAlloc_1384_;
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1339_);
                            crate::leanh::lean_dec_ref(v_table_1335_);
                            crate::leanh::lean_dec_ref(v_needle_1334_);
                            v___x_1385_ = lean_nat_sub(v_nextStackPos_1378_, v_nextNeedlePos_1379_);
                            crate::leanh::lean_dec(v_nextNeedlePos_1379_);
                            crate::leanh::lean_dec(v_nextStackPos_1378_);
                            v___x_1386_ = l_String_Slice_pos_x21(v___x_1317_, v___x_1385_);
                            crate::leanh::lean_dec(v___x_1385_);
                            v___x_1387_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1387_, 0, v___x_1386_);
                            return v___x_1387_;
                        }
                    }
                }
            }
            4 => {
                v_a_1319_ = v___x_1362_;
                v_b_1320_ = v___x_1321_;
                state = 0;
                continue;
            }
            5 => {
                v_a_1319_ = v___x_1367_;
                v_b_1320_ = v___x_1321_;
                state = 0;
                continue;
            }
            6 => {
                v_a_1319_ = v___x_1374_;
                v_b_1320_ = v___x_1321_;
                state = 0;
                continue;
            }
            7 => {
                v_a_1319_ = v___x_1382_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg___boxed(
    mut v_s_1389_: *mut crate::leanh::LeanObject,
    mut v___x_1390_: *mut crate::leanh::LeanObject,
    mut v___x_1391_: *mut crate::leanh::LeanObject,
    mut v_a_1392_: *mut crate::leanh::LeanObject,
    mut v_b_1393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1394_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(v_s_1389_, v___x_1390_, v___x_1391_, v_a_1392_, v_b_1393_);
    crate::leanh::lean_dec(v_b_1393_);
    crate::leanh::lean_dec(v___x_1391_);
    crate::leanh::lean_dec_ref(v___x_1390_);
    crate::leanh::lean_dec_ref(v_s_1389_);
    return v_res_1394_;
}
pub unsafe fn _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1396_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__0;
    v___x_1397_ = lean_string_utf8_byte_size(v___x_1396_);
    return v___x_1397_;
}
pub unsafe fn _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2()
-> u8 {
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: u8 = 0;
    v___x_1398_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1399_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1_once), _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1);
    v___x_1400_ = lean_nat_dec_eq(v___x_1399_, v___x_1398_);
    return v___x_1400_;
}
pub unsafe fn _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1401_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1_once), _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1);
    v___x_1402_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1403_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__0;
    v___x_1404_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1404_, 0, v___x_1403_);
    crate::leanh::lean_ctor_set(v___x_1404_, 1, v___x_1402_);
    crate::leanh::lean_ctor_set(v___x_1404_, 2, v___x_1401_);
    return v___x_1404_;
}
pub unsafe fn _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1405_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3_once), _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3);
    v___x_1406_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1405_);
    return v___x_1406_;
}
pub unsafe fn _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1407_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1408_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4_once), _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4);
    v___x_1409_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3_once), _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3);
    v___x_1410_ = crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1410_, 0, v___x_1409_);
    crate::leanh::lean_ctor_set(v___x_1410_, 1, v___x_1408_);
    crate::leanh::lean_ctor_set(v___x_1410_, 2, v___x_1407_);
    crate::leanh::lean_ctor_set(v___x_1410_, 3, v___x_1407_);
    return v___x_1410_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f(
    mut v_s_1413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1424_: u8 = 0;
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1428_: u8 = 0;
    let mut v___x_1429_: u8 = 0;
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1414_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1415_ = lean_string_utf8_byte_size(v_s_1413_);
                crate::leanh::lean_inc_ref(v_s_1413_);
                v___x_1416_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1416_, 0, v_s_1413_);
                crate::leanh::lean_ctor_set(v___x_1416_, 1, v___x_1414_);
                crate::leanh::lean_ctor_set(v___x_1416_, 2, v___x_1415_);
                v___x_1429_ = crate::leanh::lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2_once), _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2);
                if v___x_1429_ == 0 {
                    v___x_1430_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5_once), _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5);
                    v___y_1418_ = v___x_1430_;
                    state = 1;
                    continue;
                } else {
                    v___x_1431_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__6;
                    v___y_1418_ = v___x_1431_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1419_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___y_1418_);
                v___x_1420_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(v_s_1413_, v___x_1416_, v___x_1415_, v___y_1418_, v___x_1419_);
                crate::leanh::lean_dec_ref_known(v___x_1416_, 3);
                crate::leanh::lean_dec_ref(v_s_1413_);
                if crate::leanh::lean_obj_tag(v___x_1420_) == 0 {
                    return v___x_1419_;
                } else {
                    v_val_1421_ = crate::leanh::lean_ctor_get(v___x_1420_, 0);
                    v_isSharedCheck_1428_ = (!crate::leanh::lean_is_exclusive(v___x_1420_)) as u8;
                    if v_isSharedCheck_1428_ == 0 {
                        v___x_1423_ = v___x_1420_;
                        v_isShared_1424_ = v_isSharedCheck_1428_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1421_);
                        crate::leanh::lean_dec(v___x_1420_);
                        v___x_1423_ = crate::leanh::lean_box(0);
                        v_isShared_1424_ = v_isSharedCheck_1428_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1424_ == 0 {
                    v___x_1426_ = v___x_1423_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1427_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_val_1421_);
                    v___x_1426_ = v_reuseFailAlloc_1427_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1426_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0(
    mut v_s_1432_: *mut crate::leanh::LeanObject,
    mut v___x_1433_: *mut crate::leanh::LeanObject,
    mut v___x_1434_: *mut crate::leanh::LeanObject,
    mut v_inst_1435_: *mut crate::leanh::LeanObject,
    mut v_R_1436_: *mut crate::leanh::LeanObject,
    mut v_a_1437_: *mut crate::leanh::LeanObject,
    mut v_b_1438_: *mut crate::leanh::LeanObject,
    mut v_c_1439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1440_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(v_s_1432_, v___x_1433_, v___x_1434_, v_a_1437_, v_b_1438_);
    return v___x_1440_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___boxed(
    mut v_s_1441_: *mut crate::leanh::LeanObject,
    mut v___x_1442_: *mut crate::leanh::LeanObject,
    mut v___x_1443_: *mut crate::leanh::LeanObject,
    mut v_inst_1444_: *mut crate::leanh::LeanObject,
    mut v_R_1445_: *mut crate::leanh::LeanObject,
    mut v_a_1446_: *mut crate::leanh::LeanObject,
    mut v_b_1447_: *mut crate::leanh::LeanObject,
    mut v_c_1448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1449_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0(v_s_1441_, v___x_1442_, v___x_1443_, v_inst_1444_, v_R_1445_, v_a_1446_, v_b_1447_, v_c_1448_);
    crate::leanh::lean_dec(v_b_1447_);
    crate::leanh::lean_dec(v___x_1443_);
    crate::leanh::lean_dec_ref(v___x_1442_);
    crate::leanh::lean_dec_ref(v_s_1441_);
    return v_res_1449_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(
    mut v_text_1450_: *mut crate::leanh::LeanObject,
    mut v_pos_1451_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lineStartPos_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lineEndPos_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_text_1450_);
    v___x_1452_ = l_Lean_FileMap_toPosition(v_text_1450_, v_pos_1451_);
    v_line_1453_ = crate::leanh::lean_ctor_get(v___x_1452_, 0);
    crate::leanh::lean_inc(v_line_1453_);
    crate::leanh::lean_dec_ref(v___x_1452_);
    v_source_1454_ = crate::leanh::lean_ctor_get(v_text_1450_, 0);
    crate::leanh::lean_inc_ref(v_source_1454_);
    v_lineStartPos_1455_ = l_Lean_FileMap_lineStart(v_text_1450_, v_line_1453_);
    v___x_1456_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1457_ = lean_nat_add(v_line_1453_, v___x_1456_);
    crate::leanh::lean_dec(v_line_1453_);
    v_lineEndPos_1458_ = l_Lean_FileMap_lineStart(v_text_1450_, v___x_1457_);
    crate::leanh::lean_dec(v___x_1457_);
    crate::leanh::lean_dec_ref(v_text_1450_);
    v_line_1459_ =
        lean_string_utf8_extract(v_source_1454_, v_lineStartPos_1455_, v_lineEndPos_1458_);
    crate::leanh::lean_dec(v_lineEndPos_1458_);
    crate::leanh::lean_dec_ref(v_source_1454_);
    v___x_1460_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f(v_line_1459_);
    if crate::leanh::lean_obj_tag(v___x_1460_) == 1 {
        let mut v_val_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1463_: u8 = 0;
        v_val_1461_ = crate::leanh::lean_ctor_get(v___x_1460_, 0);
        crate::leanh::lean_inc(v_val_1461_);
        crate::leanh::lean_dec_ref_known(v___x_1460_, 1);
        v___x_1462_ = lean_nat_add(v_lineStartPos_1455_, v_val_1461_);
        crate::leanh::lean_dec(v_val_1461_);
        crate::leanh::lean_dec(v_lineStartPos_1455_);
        v___x_1463_ = lean_nat_dec_le(v___x_1462_, v_pos_1451_);
        crate::leanh::lean_dec(v___x_1462_);
        return v___x_1463_;
    } else {
        let mut v___x_1464_: u8 = 0;
        crate::leanh::lean_dec(v___x_1460_);
        crate::leanh::lean_dec(v_lineStartPos_1455_);
        v___x_1464_ = 0;
        return v___x_1464_;
    }
}
pub unsafe fn l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment___boxed(
    mut v_text_1465_: *mut crate::leanh::LeanObject,
    mut v_pos_1466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1467_: u8 = 0;
    let mut v_r_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1467_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(v_text_1465_, v_pos_1466_);
    crate::leanh::lean_dec(v_pos_1466_);
    v_r_1468_ = crate::leanh::lean_box((v_res_1467_) as usize);
    return v_r_1468_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(
    mut v_text_1525_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_1526_: *mut crate::leanh::LeanObject,
    mut v_requestedPos_1527_: *mut crate::leanh::LeanObject,
    mut v_stx_1528_: *mut crate::leanh::LeanObject,
    mut v_parent_1529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_x3f_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: u8 = 0;
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: u8 = 0;
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: u8 = 0;
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: u8 = 0;
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: u8 = 0;
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: u8 = 0;
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: u8 = 0;
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: u8 = 0;
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: u8 = 0;
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: u8 = 0;
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: u8 = 0;
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: u8 = 0;
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: u8 = 0;
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: u8 = 0;
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: u8 = 0;
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: u8 = 0;
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: u8 = 0;
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: u8 = 0;
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: u8 = 0;
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: u8 = 0;
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: u8 = 0;
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: u8 = 0;
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: u8 = 0;
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: u8 = 0;
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1630_: u8 = 0;
    let mut v___y_1631_: u8 = 0;
    let mut v___y_1632_: u8 = 0;
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: u8 = 0;
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: u8 = 0;
    let mut v___y_1639_: u8 = 0;
    let mut v___y_1640_: u8 = 0;
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: u8 = 0;
    let mut v___y_1647_: u8 = 0;
    let mut v_val_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRetrigger_1649_: u8 = 0;
    let mut v_val_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_triggerKind_1651_: u8 = 0;
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1634_ = 1;
                v___x_1635_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1528_, v___x_1634_);
                if crate::leanh::lean_obj_tag(v___x_1635_) == 1 {
                    v_val_1636_ = crate::leanh::lean_ctor_get(v___x_1635_, 0);
                    crate::leanh::lean_inc(v_val_1636_);
                    crate::leanh::lean_dec_ref_known(v___x_1635_, 1);
                    v___x_1637_ = lean_nat_dec_lt(v_requestedPos_1527_, v_val_1636_);
                    if v___x_1637_ == 0 {
                        if crate::leanh::lean_obj_tag(v_ctx_x3f_1526_) == 0 {
                            v___y_1647_ = v___x_1637_;
                            state = 5;
                            continue;
                        } else {
                            v_val_1650_ = crate::leanh::lean_ctor_get(v_ctx_x3f_1526_, 0);
                            v_triggerKind_1651_ = crate::leanh::lean_ctor_get_uint8(
                                v_val_1650_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                            );
                            if v_triggerKind_1651_ == 0 {
                                v___y_1647_ = v___x_1634_;
                                state = 5;
                                continue;
                            } else {
                                v___y_1647_ = v___x_1637_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_1636_);
                        crate::leanh::lean_dec(v_parent_1529_);
                        crate::leanh::lean_dec(v_stx_1528_);
                        crate::leanh::lean_dec_ref(v_text_1525_);
                        v___x_1652_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__23;
                        return v___x_1652_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1635_);
                    crate::leanh::lean_dec(v_parent_1529_);
                    crate::leanh::lean_dec(v_stx_1528_);
                    crate::leanh::lean_dec_ref(v_text_1525_);
                    v___x_1653_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__22;
                    return v___x_1653_;
                }
            }
            1 => {
                v___x_1532_ = 0;
                v___x_1533_ = crate::leanh::lean_box((v___x_1532_) as usize);
                crate::leanh::lean_inc(v_kind_x3f_1531_);
                v___x_1534_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1534_, 0, v_kind_x3f_1531_);
                crate::leanh::lean_ctor_set(v___x_1534_, 1, v___x_1533_);
                return v___x_1534_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_stx_1528_) == 3 {
                    crate::leanh::lean_dec_ref_known(v_stx_1528_, 4);
                    v___x_1536_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4;
                    crate::leanh::lean_inc(v_parent_1529_);
                    v___x_1537_ = l_Lean_Syntax_isOfKind(v_parent_1529_, v___x_1536_);
                    if v___x_1537_ == 0 {
                        v___x_1538_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6;
                        crate::leanh::lean_inc(v_parent_1529_);
                        v___x_1539_ = l_Lean_Syntax_isOfKind(v_parent_1529_, v___x_1538_);
                        if v___x_1539_ == 0 {
                            v___x_1540_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8;
                            crate::leanh::lean_inc(v_parent_1529_);
                            v___x_1541_ = l_Lean_Syntax_isOfKind(v_parent_1529_, v___x_1540_);
                            if v___x_1541_ == 0 {
                                crate::leanh::lean_dec(v_parent_1529_);
                                v___x_1542_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9;
                                v_kind_x3f_1531_ = v___x_1542_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1543_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_1544_ = l_Lean_Syntax_getArg(v_parent_1529_, v___x_1543_);
                                crate::leanh::lean_dec(v_parent_1529_);
                                v___x_1545_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11;
                                v___x_1546_ = l_Lean_Syntax_isOfKind(v___x_1544_, v___x_1545_);
                                if v___x_1546_ == 0 {
                                    v___x_1547_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9;
                                    v_kind_x3f_1531_ = v___x_1547_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_1548_ = crate::leanh::lean_box(0);
                                    v_kind_x3f_1531_ = v___x_1548_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v___x_1549_ = crate::leanh::lean_unsigned_to_nat(2);
                            v___x_1550_ = l_Lean_Syntax_getArg(v_parent_1529_, v___x_1549_);
                            crate::leanh::lean_dec(v_parent_1529_);
                            v___x_1551_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11;
                            v___x_1552_ = l_Lean_Syntax_isOfKind(v___x_1550_, v___x_1551_);
                            if v___x_1552_ == 0 {
                                v___x_1553_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9;
                                v_kind_x3f_1531_ = v___x_1553_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1554_ = crate::leanh::lean_box(0);
                                v_kind_x3f_1531_ = v___x_1554_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v___x_1555_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_1556_ = l_Lean_Syntax_getArg(v_parent_1529_, v___x_1555_);
                        v___x_1557_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11;
                        v___x_1558_ = l_Lean_Syntax_isOfKind(v___x_1556_, v___x_1557_);
                        if v___x_1558_ == 0 {
                            crate::leanh::lean_dec(v_parent_1529_);
                            v___x_1559_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9;
                            v_kind_x3f_1531_ = v___x_1559_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1560_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_1561_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_1562_ = l_Lean_Syntax_getArg(v_parent_1529_, v___x_1561_);
                            crate::leanh::lean_dec(v_parent_1529_);
                            v___x_1563_ = l_Lean_Syntax_matchesNull(v___x_1562_, v___x_1560_);
                            if v___x_1563_ == 0 {
                                v___x_1564_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9;
                                v_kind_x3f_1531_ = v___x_1564_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1565_ = crate::leanh::lean_box(0);
                                v_kind_x3f_1531_ = v___x_1565_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_parent_1529_);
                    if crate::leanh::lean_obj_tag(v_stx_1528_) == 1 {
                        v_kind_1566_ = crate::leanh::lean_ctor_get(v_stx_1528_, 1);
                        v_args_1567_ = crate::leanh::lean_ctor_get(v_stx_1528_, 2);
                        crate::leanh::lean_inc_ref(v_args_1567_);
                        v___x_1568_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__13;
                        v___x_1569_ = lean_name_eq(v_kind_1566_, v___x_1568_);
                        if v___x_1569_ == 0 {
                            v___x_1570_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15;
                            v___x_1571_ = lean_name_eq(v_kind_1566_, v___x_1570_);
                            if v___x_1571_ == 0 {
                                v___x_1572_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__17;
                                crate::leanh::lean_inc_ref(v_stx_1528_);
                                v___x_1573_ = l_Lean_Syntax_isOfKind(v_stx_1528_, v___x_1572_);
                                if v___x_1573_ == 0 {
                                    v___x_1574_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__19;
                                    crate::leanh::lean_inc_ref(v_stx_1528_);
                                    v___x_1575_ = l_Lean_Syntax_isOfKind(v_stx_1528_, v___x_1574_);
                                    if v___x_1575_ == 0 {
                                        v___x_1576_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4;
                                        crate::leanh::lean_inc_ref(v_stx_1528_);
                                        v___x_1577_ =
                                            l_Lean_Syntax_isOfKind(v_stx_1528_, v___x_1576_);
                                        if v___x_1577_ == 0 {
                                            v___x_1578_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8;
                                            crate::leanh::lean_inc_ref(v_stx_1528_);
                                            v___x_1579_ =
                                                l_Lean_Syntax_isOfKind(v_stx_1528_, v___x_1578_);
                                            if v___x_1579_ == 0 {
                                                v___x_1580_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6;
                                                crate::leanh::lean_inc_ref(v_stx_1528_);
                                                v___x_1581_ = l_Lean_Syntax_isOfKind(
                                                    v_stx_1528_,
                                                    v___x_1580_,
                                                );
                                                if v___x_1581_ == 0 {
                                                    crate::leanh::lean_dec_ref_known(
                                                        v_stx_1528_,
                                                        3,
                                                    );
                                                    v___x_1582_ = lean_array_get_size(v_args_1567_);
                                                    crate::leanh::lean_dec_ref(v_args_1567_);
                                                    v___x_1583_ =
                                                        crate::leanh::lean_unsigned_to_nat(1);
                                                    v___x_1584_ =
                                                        lean_nat_dec_le(v___x_1582_, v___x_1583_);
                                                    if v___x_1584_ == 0 {
                                                        v___x_1585_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9;
                                                        v_kind_x3f_1531_ = v___x_1585_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v___x_1586_ = crate::leanh::lean_box(0);
                                                        v_kind_x3f_1531_ = v___x_1586_;
                                                        state = 1;
                                                        continue;
                                                    }
                                                } else {
                                                    v___x_1587_ =
                                                        crate::leanh::lean_unsigned_to_nat(2);
                                                    v___x_1588_ = l_Lean_Syntax_getArg(
                                                        v_stx_1528_,
                                                        v___x_1587_,
                                                    );
                                                    crate::leanh::lean_dec_ref_known(
                                                        v_stx_1528_,
                                                        3,
                                                    );
                                                    v___x_1589_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11;
                                                    v___x_1590_ = l_Lean_Syntax_isOfKind(
                                                        v___x_1588_,
                                                        v___x_1589_,
                                                    );
                                                    if v___x_1590_ == 0 {
                                                        v___x_1591_ =
                                                            crate::leanh::lean_unsigned_to_nat(1);
                                                        v___x_1592_ =
                                                            lean_array_get_size(v_args_1567_);
                                                        crate::leanh::lean_dec_ref(v_args_1567_);
                                                        v___x_1593_ = lean_nat_dec_le(
                                                            v___x_1592_,
                                                            v___x_1591_,
                                                        );
                                                        if v___x_1593_ == 0 {
                                                            v___x_1594_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9;
                                                            v_kind_x3f_1531_ = v___x_1594_;
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            v___x_1595_ = crate::leanh::lean_box(0);
                                                            v_kind_x3f_1531_ = v___x_1595_;
                                                            state = 1;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v_args_1567_);
                                                        v___x_1596_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9;
                                                        v_kind_x3f_1531_ = v___x_1596_;
                                                        state = 1;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                v___x_1597_ = crate::leanh::lean_unsigned_to_nat(1);
                                                v___x_1598_ =
                                                    l_Lean_Syntax_getArg(v_stx_1528_, v___x_1597_);
                                                crate::leanh::lean_dec_ref_known(v_stx_1528_, 3);
                                                v___x_1599_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11;
                                                v___x_1600_ = l_Lean_Syntax_isOfKind(
                                                    v___x_1598_,
                                                    v___x_1599_,
                                                );
                                                if v___x_1600_ == 0 {
                                                    v___x_1601_ = lean_array_get_size(v_args_1567_);
                                                    crate::leanh::lean_dec_ref(v_args_1567_);
                                                    v___x_1602_ =
                                                        lean_nat_dec_le(v___x_1601_, v___x_1597_);
                                                    if v___x_1602_ == 0 {
                                                        v___x_1603_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9;
                                                        v_kind_x3f_1531_ = v___x_1603_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v___x_1604_ = crate::leanh::lean_box(0);
                                                        v_kind_x3f_1531_ = v___x_1604_;
                                                        state = 1;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v_args_1567_);
                                                    v___x_1605_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9;
                                                    v_kind_x3f_1531_ = v___x_1605_;
                                                    state = 1;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            v___x_1606_ = crate::leanh::lean_unsigned_to_nat(1);
                                            v___x_1607_ = crate::leanh::lean_unsigned_to_nat(2);
                                            v___x_1608_ =
                                                l_Lean_Syntax_getArg(v_stx_1528_, v___x_1607_);
                                            v___x_1609_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11;
                                            v___x_1610_ =
                                                l_Lean_Syntax_isOfKind(v___x_1608_, v___x_1609_);
                                            if v___x_1610_ == 0 {
                                                crate::leanh::lean_dec_ref_known(v_stx_1528_, 3);
                                                v___x_1611_ = lean_array_get_size(v_args_1567_);
                                                crate::leanh::lean_dec_ref(v_args_1567_);
                                                v___x_1612_ =
                                                    lean_nat_dec_le(v___x_1611_, v___x_1606_);
                                                if v___x_1612_ == 0 {
                                                    v___x_1613_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9;
                                                    v_kind_x3f_1531_ = v___x_1613_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___x_1614_ = crate::leanh::lean_box(0);
                                                    v_kind_x3f_1531_ = v___x_1614_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                v___x_1615_ = crate::leanh::lean_unsigned_to_nat(0);
                                                v___x_1616_ = crate::leanh::lean_unsigned_to_nat(3);
                                                v___x_1617_ =
                                                    l_Lean_Syntax_getArg(v_stx_1528_, v___x_1616_);
                                                crate::leanh::lean_dec_ref_known(v_stx_1528_, 3);
                                                v___x_1618_ = l_Lean_Syntax_matchesNull(
                                                    v___x_1617_,
                                                    v___x_1615_,
                                                );
                                                if v___x_1618_ == 0 {
                                                    v___x_1619_ = lean_array_get_size(v_args_1567_);
                                                    crate::leanh::lean_dec_ref(v_args_1567_);
                                                    v___x_1620_ =
                                                        lean_nat_dec_le(v___x_1619_, v___x_1606_);
                                                    if v___x_1620_ == 0 {
                                                        v___x_1621_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9;
                                                        v_kind_x3f_1531_ = v___x_1621_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v___x_1622_ = crate::leanh::lean_box(0);
                                                        v_kind_x3f_1531_ = v___x_1622_;
                                                        state = 1;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v_args_1567_);
                                                    v___x_1623_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20;
                                                    v_kind_x3f_1531_ = v___x_1623_;
                                                    state = 1;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_args_1567_);
                                        crate::leanh::lean_dec_ref_known(v_stx_1528_, 3);
                                        v___x_1624_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20;
                                        v_kind_x3f_1531_ = v___x_1624_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_args_1567_);
                                    crate::leanh::lean_dec_ref_known(v_stx_1528_, 3);
                                    v___x_1625_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20;
                                    v_kind_x3f_1531_ = v___x_1625_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_args_1567_);
                                crate::leanh::lean_dec_ref_known(v_stx_1528_, 3);
                                v___x_1626_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__21;
                                v_kind_x3f_1531_ = v___x_1626_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_args_1567_);
                            crate::leanh::lean_dec_ref_known(v_stx_1528_, 3);
                            v___x_1627_ = crate::leanh::lean_box(0);
                            v_kind_x3f_1531_ = v___x_1627_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_stx_1528_);
                        v___x_1628_ = crate::leanh::lean_box(0);
                        v_kind_x3f_1531_ = v___x_1628_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                if v___y_1630_ == 0 {
                    if v___y_1631_ == 0 {
                        if v___y_1632_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_parent_1529_);
                            crate::leanh::lean_dec(v_stx_1528_);
                            v___x_1633_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__22;
                            return v___x_1633_;
                        }
                    } else {
                        state = 2;
                        continue;
                    }
                } else {
                    state = 2;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v_text_1525_);
                v___x_1641_ = l_Lean_FileMap_toPosition(v_text_1525_, v_requestedPos_1527_);
                v_line_1642_ = crate::leanh::lean_ctor_get(v___x_1641_, 0);
                crate::leanh::lean_inc(v_line_1642_);
                crate::leanh::lean_dec_ref(v___x_1641_);
                v___x_1643_ = l_Lean_FileMap_toPosition(v_text_1525_, v_val_1636_);
                crate::leanh::lean_dec(v_val_1636_);
                v_line_1644_ = crate::leanh::lean_ctor_get(v___x_1643_, 0);
                crate::leanh::lean_inc(v_line_1644_);
                crate::leanh::lean_dec_ref(v___x_1643_);
                v___x_1645_ = lean_nat_dec_eq(v_line_1642_, v_line_1644_);
                crate::leanh::lean_dec(v_line_1644_);
                crate::leanh::lean_dec(v_line_1642_);
                if v___x_1645_ == 0 {
                    v___y_1630_ = v___y_1639_;
                    v___y_1631_ = v___y_1640_;
                    v___y_1632_ = v___x_1634_;
                    state = 3;
                    continue;
                } else {
                    v___y_1630_ = v___y_1639_;
                    v___y_1631_ = v___y_1640_;
                    v___y_1632_ = v___x_1637_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_ctx_x3f_1526_) == 0 {
                    v___y_1639_ = v___y_1647_;
                    v___y_1640_ = v___x_1637_;
                    state = 4;
                    continue;
                } else {
                    v_val_1648_ = crate::leanh::lean_ctor_get(v_ctx_x3f_1526_, 0);
                    v_isRetrigger_1649_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_1648_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                    );
                    v___y_1639_ = v___y_1647_;
                    v___y_1640_ = v_isRetrigger_1649_;
                    state = 4;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___boxed(
    mut v_text_1654_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_1655_: *mut crate::leanh::LeanObject,
    mut v_requestedPos_1656_: *mut crate::leanh::LeanObject,
    mut v_stx_1657_: *mut crate::leanh::LeanObject,
    mut v_parent_1658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1659_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(v_text_1654_, v_ctx_x3f_1655_, v_requestedPos_1656_, v_stx_1657_, v_parent_1658_);
    crate::leanh::lean_dec(v_requestedPos_1656_);
    crate::leanh::lean_dec(v_ctx_x3f_1655_);
    return v_res_1659_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0(
    mut v___x_1660_: u8,
    mut v_stx_1661_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1662_: u8 = 0;
    v___x_1662_ = l_Lean_Syntax_hasArgs(v_stx_1661_);
    if v___x_1662_ == 0 {
        let mut v___x_1663_: u8 = 0;
        v___x_1663_ = 1;
        return v___x_1663_;
    } else {
        return v___x_1660_;
    }
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0___boxed(
    mut v___x_1664_: *mut crate::leanh::LeanObject,
    mut v_stx_1665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3193__boxed_1666_: u8 = 0;
    let mut v_res_1667_: u8 = 0;
    let mut v_r_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3193__boxed_1666_ = (crate::leanh::lean_unbox(v___x_1664_) as u8);
    v_res_1667_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0(
        v___x_3193__boxed_1666_,
        v_stx_1665_,
    );
    crate::leanh::lean_dec(v_stx_1665_);
    v_r_1668_ = crate::leanh::lean_box((v_res_1667_) as usize);
    return v_r_1668_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1(
    mut v___x_1669_: u8,
    mut v_requestedPos_1670_: *mut crate::leanh::LeanObject,
    mut v___x_1671_: u8,
    mut v_stx_1672_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1673_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_1672_, v___x_1669_);
    if crate::leanh::lean_obj_tag(v___x_1673_) == 1 {
        let mut v_val_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1675_: u8 = 0;
        v_val_1674_ = crate::leanh::lean_ctor_get(v___x_1673_, 0);
        crate::leanh::lean_inc(v_val_1674_);
        crate::leanh::lean_dec_ref_known(v___x_1673_, 1);
        v___x_1675_ = l_Lean_Syntax_Range_contains(v_val_1674_, v_requestedPos_1670_, v___x_1669_);
        crate::leanh::lean_dec(v_val_1674_);
        return v___x_1675_;
    } else {
        crate::leanh::lean_dec(v___x_1673_);
        return v___x_1671_;
    }
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1___boxed(
    mut v___x_1676_: *mut crate::leanh::LeanObject,
    mut v_requestedPos_1677_: *mut crate::leanh::LeanObject,
    mut v___x_1678_: *mut crate::leanh::LeanObject,
    mut v_stx_1679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3200__boxed_1680_: u8 = 0;
    let mut v___x_3201__boxed_1681_: u8 = 0;
    let mut v_res_1682_: u8 = 0;
    let mut v_r_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3200__boxed_1680_ = (crate::leanh::lean_unbox(v___x_1676_) as u8);
    v___x_3201__boxed_1681_ = (crate::leanh::lean_unbox(v___x_1678_) as u8);
    v_res_1682_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1(
        v___x_3200__boxed_1680_,
        v_requestedPos_1677_,
        v___x_3201__boxed_1681_,
        v_stx_1679_,
    );
    crate::leanh::lean_dec(v_stx_1679_);
    crate::leanh::lean_dec(v_requestedPos_1677_);
    v_r_1683_ = crate::leanh::lean_box((v_res_1682_) as usize);
    return v_r_1683_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2(
    mut v_c1_1684_: *mut crate::leanh::LeanObject,
    mut v_c2_1685_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_kind_1686_: u8 = 0;
    let mut v_kind_1687_: u8 = 0;
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: u8 = 0;
    v_kind_1686_ = crate::leanh::lean_ctor_get_uint8(
        v_c2_1685_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    v_kind_1687_ = crate::leanh::lean_ctor_get_uint8(
        v_c1_1684_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    v___x_1688_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_kind_1686_);
    v___x_1689_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_kind_1687_);
    v___x_1690_ = lean_nat_dec_le(v___x_1688_, v___x_1689_);
    crate::leanh::lean_dec(v___x_1689_);
    crate::leanh::lean_dec(v___x_1688_);
    return v___x_1690_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2___boxed(
    mut v_c1_1691_: *mut crate::leanh::LeanObject,
    mut v_c2_1692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1693_: u8 = 0;
    let mut v_r_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2(
        v_c1_1691_, v_c2_1692_,
    );
    crate::leanh::lean_dec_ref(v_c2_1692_);
    crate::leanh::lean_dec_ref(v_c1_1691_);
    v_r_1694_ = crate::leanh::lean_box((v_res_1693_) as usize);
    return v_r_1694_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(
    mut v_tree_1703_: *mut crate::leanh::LeanObject,
    mut v___y_1704_: u8,
    mut v___x_1705_: u8,
    mut v_as_1706_: *mut crate::leanh::LeanObject,
    mut v_sz_1707_: usize,
    mut v_i_1708_: usize,
    mut v_b_1709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1711_: u8 = 0;
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1714_: u8 = 0;
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_appStx_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1723_: u8 = 0;
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: usize = 0;
    let mut v___x_1730_: usize = 0;
    let mut v_isSharedCheck_1732_: u8 = 0;
    let mut v_a_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1736_: u8 = 0;
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1740_: u8 = 0;
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1711_ = lean_usize_dec_lt(v_i_1708_, v_sz_1707_);
                if v___x_1711_ == 0 {
                    crate::leanh::lean_dec_ref(v_tree_1703_);
                    v___x_1712_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1712_, 0, v_b_1709_);
                    return v___x_1712_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_1709_);
                    v_a_1713_ = lean_array_uget_borrowed(v_as_1706_, v_i_1708_);
                    v_kind_1714_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_1713_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v___x_1715_ = crate::leanh::lean_box(0);
                    v___x_1716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0;
                    if v_kind_1714_ == 1 {
                        state = 6;
                        continue;
                    } else {
                        if v___x_1705_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_appStx_1718_ = crate::leanh::lean_ctor_get(v_a_1713_, 0);
                crate::leanh::lean_inc(v_appStx_1718_);
                crate::leanh::lean_inc_ref(v_tree_1703_);
                v___x_1719_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp(
                    v_tree_1703_,
                    v_appStx_1718_,
                );
                if crate::leanh::lean_obj_tag(v___x_1719_) == 0 {
                    v_a_1720_ = crate::leanh::lean_ctor_get(v___x_1719_, 0);
                    v_isSharedCheck_1732_ = (!crate::leanh::lean_is_exclusive(v___x_1719_)) as u8;
                    if v_isSharedCheck_1732_ == 0 {
                        v___x_1722_ = v___x_1719_;
                        v_isShared_1723_ = v_isSharedCheck_1732_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1720_);
                        crate::leanh::lean_dec(v___x_1719_);
                        v___x_1722_ = crate::leanh::lean_box(0);
                        v_isShared_1723_ = v_isSharedCheck_1732_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_tree_1703_);
                    v_a_1733_ = crate::leanh::lean_ctor_get(v___x_1719_, 0);
                    v_isSharedCheck_1740_ = (!crate::leanh::lean_is_exclusive(v___x_1719_)) as u8;
                    if v_isSharedCheck_1740_ == 0 {
                        v___x_1735_ = v___x_1719_;
                        v_isShared_1736_ = v_isSharedCheck_1740_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1733_);
                        crate::leanh::lean_dec(v___x_1719_);
                        v___x_1735_ = crate::leanh::lean_box(0);
                        v_isShared_1736_ = v_isSharedCheck_1740_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_1720_) == 1 {
                    crate::leanh::lean_dec_ref(v_tree_1703_);
                    v___x_1724_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1724_, 0, v_a_1720_);
                    v___x_1725_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1725_, 0, v___x_1724_);
                    crate::leanh::lean_ctor_set(v___x_1725_, 1, v___x_1715_);
                    if v_isShared_1723_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1722_, 0, v___x_1725_);
                        v___x_1727_ = v___x_1722_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1728_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1725_);
                        v___x_1727_ = v_reuseFailAlloc_1728_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1722_);
                    crate::leanh::lean_dec(v_a_1720_);
                    v___x_1729_ = 1usize;
                    v___x_1730_ = lean_usize_add(v_i_1708_, v___x_1729_);
                    v_i_1708_ = v___x_1730_;
                    v_b_1709_ = v___x_1716_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_1727_;
            }
            4 => {
                if v_isShared_1736_ == 0 {
                    v___x_1738_ = v___x_1735_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1739_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
                    v___x_1738_ = v_reuseFailAlloc_1739_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1738_;
            }
            6 => {
                if v___y_1704_ == 0 {
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_tree_1703_);
                    v___x_1742_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__2;
                    v___x_1743_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1743_, 0, v___x_1742_);
                    return v___x_1743_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___boxed(
    mut v_tree_1744_: *mut crate::leanh::LeanObject,
    mut v___y_1745_: *mut crate::leanh::LeanObject,
    mut v___x_1746_: *mut crate::leanh::LeanObject,
    mut v_as_1747_: *mut crate::leanh::LeanObject,
    mut v_sz_1748_: *mut crate::leanh::LeanObject,
    mut v_i_1749_: *mut crate::leanh::LeanObject,
    mut v_b_1750_: *mut crate::leanh::LeanObject,
    mut v___y_1751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3234__boxed_1752_: u8 = 0;
    let mut v___x_3235__boxed_1753_: u8 = 0;
    let mut v_sz_boxed_1754_: usize = 0;
    let mut v_i_boxed_1755_: usize = 0;
    let mut v_res_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_3234__boxed_1752_ = (crate::leanh::lean_unbox(v___y_1745_) as u8);
    v___x_3235__boxed_1753_ = (crate::leanh::lean_unbox(v___x_1746_) as u8);
    v_sz_boxed_1754_ = crate::leanh::lean_unbox_usize(v_sz_1748_);
    crate::leanh::lean_dec(v_sz_1748_);
    v_i_boxed_1755_ = crate::leanh::lean_unbox_usize(v_i_1749_);
    crate::leanh::lean_dec(v_i_1749_);
    v_res_1756_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(v_tree_1744_, v___y_3234__boxed_1752_, v___x_3235__boxed_1753_, v_as_1747_, v_sz_boxed_1754_, v_i_boxed_1755_, v_b_1750_);
    crate::leanh::lean_dec_ref(v_as_1747_);
    return v_res_1756_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1757_: u8 = 0;
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1757_ = 1;
    v___x_1758_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v___x_1757_);
    return v___x_1758_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(
    mut v_as_1759_: *mut crate::leanh::LeanObject,
    mut v_i_1760_: usize,
    mut v_stop_1761_: usize,
) -> u8 {
    let mut v___x_1762_: u8 = 0;
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1764_: u8 = 0;
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: u8 = 0;
    let mut v___x_1768_: usize = 0;
    let mut v___x_1769_: usize = 0;
    let mut v___x_1771_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1762_ = lean_usize_dec_eq(v_i_1760_, v_stop_1761_);
                if v___x_1762_ == 0 {
                    v___x_1763_ = lean_array_uget_borrowed(v_as_1759_, v_i_1760_);
                    v_kind_1764_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_1763_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v___x_1765_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0);
                    v___x_1766_ =
                        l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_kind_1764_);
                    v___x_1767_ = lean_nat_dec_lt(v___x_1765_, v___x_1766_);
                    crate::leanh::lean_dec(v___x_1766_);
                    if v___x_1767_ == 0 {
                        v___x_1768_ = 1usize;
                        v___x_1769_ = lean_usize_add(v_i_1760_, v___x_1768_);
                        v_i_1760_ = v___x_1769_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1767_;
                    }
                } else {
                    v___x_1771_ = 0;
                    return v___x_1771_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___boxed(
    mut v_as_1772_: *mut crate::leanh::LeanObject,
    mut v_i_1773_: *mut crate::leanh::LeanObject,
    mut v_stop_1774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1775_: usize = 0;
    let mut v_stop_boxed_1776_: usize = 0;
    let mut v_res_1777_: u8 = 0;
    let mut v_r_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1775_ = crate::leanh::lean_unbox_usize(v_i_1773_);
    crate::leanh::lean_dec(v_i_1773_);
    v_stop_boxed_1776_ = crate::leanh::lean_unbox_usize(v_stop_1774_);
    crate::leanh::lean_dec(v_stop_1774_);
    v_res_1777_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(v_as_1772_, v_i_boxed_1775_, v_stop_boxed_1776_);
    crate::leanh::lean_dec_ref(v_as_1772_);
    v_r_1778_ = crate::leanh::lean_box((v_res_1777_) as usize);
    return v_r_1778_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(
    mut v_snd_1779_: u8,
    mut v___x_1780_: u8,
    mut v_____r_1781_: *mut crate::leanh::LeanObject,
    mut v_candidates_1782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_snd_1779_ == 1 {
                    state = 1;
                    continue;
                } else {
                    if v___x_1780_ == 0 {
                        v___x_1787_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1787_, 0, v_candidates_1782_);
                        v___x_1788_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1788_, 0, v___x_1787_);
                        return v___x_1788_;
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1785_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1785_, 0, v_candidates_1782_);
                v___x_1786_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1786_, 0, v___x_1785_);
                return v___x_1786_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0___boxed(
    mut v_snd_1789_: *mut crate::leanh::LeanObject,
    mut v___x_1790_: *mut crate::leanh::LeanObject,
    mut v_____r_1791_: *mut crate::leanh::LeanObject,
    mut v_candidates_1792_: *mut crate::leanh::LeanObject,
    mut v___y_1793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_3336__boxed_1794_: u8 = 0;
    let mut v___x_3337__boxed_1795_: u8 = 0;
    let mut v_res_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_3336__boxed_1794_ = (crate::leanh::lean_unbox(v_snd_1789_) as u8);
    v___x_3337__boxed_1795_ = (crate::leanh::lean_unbox(v___x_1790_) as u8);
    v_res_1796_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(v_snd_3336__boxed_1794_, v___x_3337__boxed_1795_, v_____r_1791_, v_candidates_1792_);
    return v_res_1796_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(
    mut v_upperBound_1797_: *mut crate::leanh::LeanObject,
    mut v_stack_1798_: *mut crate::leanh::LeanObject,
    mut v_text_1799_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_1800_: *mut crate::leanh::LeanObject,
    mut v_requestedPos_1801_: *mut crate::leanh::LeanObject,
    mut v___x_1802_: u8,
    mut v_a_1803_: *mut crate::leanh::LeanObject,
    mut v_b_1804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1811_: u8 = 0;
    let mut v_a_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1820_: u8 = 0;
    let mut v_a_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1824_: u8 = 0;
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1828_: u8 = 0;
    let mut v___x_1829_: u8 = 0;
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: u8 = 0;
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: u8 = 0;
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: u8 = 0;
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: u8 = 0;
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1829_ = lean_nat_dec_lt(v_a_1803_, v_upperBound_1797_);
                if v___x_1829_ == 0 {
                    crate::leanh::lean_dec(v_a_1803_);
                    crate::leanh::lean_dec_ref(v_text_1799_);
                    v___x_1830_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1830_, 0, v_b_1804_);
                    return v___x_1830_;
                } else {
                    v___x_1831_ = lean_array_fget_borrowed(v_stack_1798_, v_a_1803_);
                    v___x_1848_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1849_ = lean_nat_add(v_a_1803_, v___x_1848_);
                    v___x_1850_ = lean_array_get_size(v_stack_1798_);
                    v___x_1851_ = lean_nat_dec_lt(v___x_1849_, v___x_1850_);
                    if v___x_1851_ == 0 {
                        crate::leanh::lean_dec(v___x_1849_);
                        v___x_1852_ = crate::leanh::lean_box(0);
                        v___y_1833_ = v___x_1852_;
                        state = 6;
                        continue;
                    } else {
                        v___x_1853_ = lean_array_fget_borrowed(v_stack_1798_, v___x_1849_);
                        crate::leanh::lean_dec(v___x_1849_);
                        crate::leanh::lean_inc(v___x_1853_);
                        v___y_1833_ = v___x_1853_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_1807_) == 0 {
                    v_a_1808_ = crate::leanh::lean_ctor_get(v___y_1807_, 0);
                    v_isSharedCheck_1820_ = (!crate::leanh::lean_is_exclusive(v___y_1807_)) as u8;
                    if v_isSharedCheck_1820_ == 0 {
                        v___x_1810_ = v___y_1807_;
                        v_isShared_1811_ = v_isSharedCheck_1820_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1808_);
                        crate::leanh::lean_dec(v___y_1807_);
                        v___x_1810_ = crate::leanh::lean_box(0);
                        v_isShared_1811_ = v_isSharedCheck_1820_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1803_);
                    crate::leanh::lean_dec_ref(v_text_1799_);
                    v_a_1821_ = crate::leanh::lean_ctor_get(v___y_1807_, 0);
                    v_isSharedCheck_1828_ = (!crate::leanh::lean_is_exclusive(v___y_1807_)) as u8;
                    if v_isSharedCheck_1828_ == 0 {
                        v___x_1823_ = v___y_1807_;
                        v_isShared_1824_ = v_isSharedCheck_1828_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1821_);
                        crate::leanh::lean_dec(v___y_1807_);
                        v___x_1823_ = crate::leanh::lean_box(0);
                        v_isShared_1824_ = v_isSharedCheck_1828_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_1808_) == 0 {
                    crate::leanh::lean_dec(v_a_1803_);
                    crate::leanh::lean_dec_ref(v_text_1799_);
                    v_a_1812_ = crate::leanh::lean_ctor_get(v_a_1808_, 0);
                    crate::leanh::lean_inc(v_a_1812_);
                    crate::leanh::lean_dec_ref_known(v_a_1808_, 1);
                    if v_isShared_1811_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1810_, 0, v_a_1812_);
                        v___x_1814_ = v___x_1810_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1815_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1812_);
                        v___x_1814_ = v_reuseFailAlloc_1815_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1810_);
                    v_a_1816_ = crate::leanh::lean_ctor_get(v_a_1808_, 0);
                    crate::leanh::lean_inc(v_a_1816_);
                    crate::leanh::lean_dec_ref_known(v_a_1808_, 1);
                    v___x_1817_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1818_ = lean_nat_add(v_a_1803_, v___x_1817_);
                    crate::leanh::lean_dec(v_a_1803_);
                    v_a_1803_ = v___x_1818_;
                    v_b_1804_ = v_a_1816_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_1814_;
            }
            4 => {
                if v_isShared_1824_ == 0 {
                    v___x_1826_ = v___x_1823_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1827_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
                    v___x_1826_ = v_reuseFailAlloc_1827_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1826_;
            }
            6 => {
                crate::leanh::lean_inc(v___x_1831_);
                crate::leanh::lean_inc_ref(v_text_1799_);
                v___x_1834_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(v_text_1799_, v_ctx_x3f_1800_, v_requestedPos_1801_, v___x_1831_, v___y_1833_);
                v_fst_1835_ = crate::leanh::lean_ctor_get(v___x_1834_, 0);
                crate::leanh::lean_inc(v_fst_1835_);
                if crate::leanh::lean_obj_tag(v_fst_1835_) == 1 {
                    v_snd_1836_ = crate::leanh::lean_ctor_get(v___x_1834_, 1);
                    crate::leanh::lean_inc(v_snd_1836_);
                    crate::leanh::lean_dec_ref(v___x_1834_);
                    v_val_1837_ = crate::leanh::lean_ctor_get(v_fst_1835_, 0);
                    crate::leanh::lean_inc(v_val_1837_);
                    crate::leanh::lean_dec_ref_known(v_fst_1835_, 1);
                    crate::leanh::lean_inc(v___x_1831_);
                    v___x_1838_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1838_, 0, v___x_1831_);
                    v___x_1839_ = (crate::leanh::lean_unbox(v_val_1837_) as u8);
                    crate::leanh::lean_dec(v_val_1837_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1838_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_1839_,
                    );
                    v___x_1840_ = lean_array_push(v_b_1804_, v___x_1838_);
                    v___x_1841_ = crate::leanh::lean_box(0);
                    v___x_1842_ = (crate::leanh::lean_unbox(v_snd_1836_) as u8);
                    crate::leanh::lean_dec(v_snd_1836_);
                    v___x_1843_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(v___x_1842_, v___x_1802_, v___x_1841_, v___x_1840_);
                    v___y_1807_ = v___x_1843_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_1835_);
                    v_snd_1844_ = crate::leanh::lean_ctor_get(v___x_1834_, 1);
                    crate::leanh::lean_inc(v_snd_1844_);
                    crate::leanh::lean_dec_ref(v___x_1834_);
                    v___x_1845_ = crate::leanh::lean_box(0);
                    v___x_1846_ = (crate::leanh::lean_unbox(v_snd_1844_) as u8);
                    crate::leanh::lean_dec(v_snd_1844_);
                    v___x_1847_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(v___x_1846_, v___x_1802_, v___x_1845_, v_b_1804_);
                    v___y_1807_ = v___x_1847_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___boxed(
    mut v_upperBound_1854_: *mut crate::leanh::LeanObject,
    mut v_stack_1855_: *mut crate::leanh::LeanObject,
    mut v_text_1856_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_1857_: *mut crate::leanh::LeanObject,
    mut v_requestedPos_1858_: *mut crate::leanh::LeanObject,
    mut v___x_1859_: *mut crate::leanh::LeanObject,
    mut v_a_1860_: *mut crate::leanh::LeanObject,
    mut v_b_1861_: *mut crate::leanh::LeanObject,
    mut v___y_1862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3359__boxed_1863_: u8 = 0;
    let mut v_res_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3359__boxed_1863_ = (crate::leanh::lean_unbox(v___x_1859_) as u8);
    v_res_1864_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(v_upperBound_1854_, v_stack_1855_, v_text_1856_, v_ctx_x3f_1857_, v_requestedPos_1858_, v___x_3359__boxed_1863_, v_a_1860_, v_b_1861_);
    crate::leanh::lean_dec(v_requestedPos_1858_);
    crate::leanh::lean_dec(v_ctx_x3f_1857_);
    crate::leanh::lean_dec_ref(v_stack_1855_);
    crate::leanh::lean_dec(v_upperBound_1854_);
    return v_res_1864_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(
    mut v_sz_1865_: usize,
    mut v_i_1866_: usize,
    mut v_bs_1867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1868_: u8 = 0;
    let mut v_v_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: usize = 0;
    let mut v___x_1874_: usize = 0;
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1868_ = lean_usize_dec_lt(v_i_1866_, v_sz_1865_);
                if v___x_1868_ == 0 {
                    return v_bs_1867_;
                } else {
                    v_v_1869_ = lean_array_uget_borrowed(v_bs_1867_, v_i_1866_);
                    v_fst_1870_ = crate::leanh::lean_ctor_get(v_v_1869_, 0);
                    crate::leanh::lean_inc(v_fst_1870_);
                    v___x_1871_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1872_ = lean_array_uset(v_bs_1867_, v_i_1866_, v___x_1871_);
                    v___x_1873_ = 1usize;
                    v___x_1874_ = lean_usize_add(v_i_1866_, v___x_1873_);
                    v___x_1875_ = lean_array_uset(v_bs_x27_1872_, v_i_1866_, v_fst_1870_);
                    v_i_1866_ = v___x_1874_;
                    v_bs_1867_ = v___x_1875_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0___boxed(
    mut v_sz_1877_: *mut crate::leanh::LeanObject,
    mut v_i_1878_: *mut crate::leanh::LeanObject,
    mut v_bs_1879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1880_: usize = 0;
    let mut v_i_boxed_1881_: usize = 0;
    let mut v_res_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1880_ = crate::leanh::lean_unbox_usize(v_sz_1877_);
    crate::leanh::lean_dec(v_sz_1877_);
    v_i_boxed_1881_ = crate::leanh::lean_unbox_usize(v_i_1878_);
    crate::leanh::lean_dec(v_i_1878_);
    v_res_1882_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(v_sz_boxed_1880_, v_i_boxed_1881_, v_bs_1879_);
    return v_res_1882_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f(
    mut v_text_1886_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_1887_: *mut crate::leanh::LeanObject,
    mut v_cmdStx_1888_: *mut crate::leanh::LeanObject,
    mut v_tree_1889_: *mut crate::leanh::LeanObject,
    mut v_requestedPos_1890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1892_: u8 = 0;
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: u8 = 0;
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stack_x3f_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1902_: usize = 0;
    let mut v___x_1903_: usize = 0;
    let mut v_stack_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_candidates_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1915_: u8 = 0;
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1918_: usize = 0;
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1923_: u8 = 0;
    let mut v_fst_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1932_: u8 = 0;
    let mut v_a_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1936_: u8 = 0;
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1940_: u8 = 0;
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: u8 = 0;
    let mut v___x_1943_: usize = 0;
    let mut v___x_1944_: u8 = 0;
    let mut v_a_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1948_: u8 = 0;
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1952_: u8 = 0;
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_text_1886_);
                v___x_1892_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(v_text_1886_, v_requestedPos_1890_);
                if v___x_1892_ == 0 {
                    v___x_1893_ = crate::leanh::lean_box((v___x_1892_) as usize);
                    v___f_1894_ = crate::leanh::lean_alloc_closure(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                    crate::leanh::lean_closure_set(v___f_1894_, 0, v___x_1893_);
                    v___x_1895_ = 1;
                    v___x_1896_ = crate::leanh::lean_box((v___x_1895_) as usize);
                    v___x_1897_ = crate::leanh::lean_box((v___x_1892_) as usize);
                    crate::leanh::lean_inc(v_requestedPos_1890_);
                    v___f_1898_ = crate::leanh::lean_alloc_closure(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1___boxed as *mut core::ffi::c_void, 4, 3);
                    crate::leanh::lean_closure_set(v___f_1898_, 0, v___x_1896_);
                    crate::leanh::lean_closure_set(v___f_1898_, 1, v_requestedPos_1890_);
                    crate::leanh::lean_closure_set(v___f_1898_, 2, v___x_1897_);
                    v_stack_x3f_1899_ =
                        l_Lean_Syntax_findStack_x3f(v_cmdStx_1888_, v___f_1898_, v___f_1894_);
                    if crate::leanh::lean_obj_tag(v_stack_x3f_1899_) == 1 {
                        v_val_1900_ = crate::leanh::lean_ctor_get(v_stack_x3f_1899_, 0);
                        crate::leanh::lean_inc(v_val_1900_);
                        crate::leanh::lean_dec_ref_known(v_stack_x3f_1899_, 1);
                        v___x_1901_ = lean_array_mk(v_val_1900_);
                        v_sz_1902_ = lean_array_size(v___x_1901_);
                        v___x_1903_ = 0usize;
                        v_stack_1904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(v_sz_1902_, v___x_1903_, v___x_1901_);
                        v___x_1905_ = lean_array_get_size(v_stack_1904_);
                        v___x_1906_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_candidates_1907_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__0;
                        v___x_1908_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(v___x_1905_, v_stack_1904_, v_text_1886_, v_ctx_x3f_1887_, v_requestedPos_1890_, v___x_1892_, v___x_1906_, v_candidates_1907_);
                        crate::leanh::lean_dec(v_requestedPos_1890_);
                        crate::leanh::lean_dec_ref(v_stack_1904_);
                        if crate::leanh::lean_obj_tag(v___x_1908_) == 0 {
                            v_a_1909_ = crate::leanh::lean_ctor_get(v___x_1908_, 0);
                            crate::leanh::lean_inc(v_a_1909_);
                            crate::leanh::lean_dec_ref_known(v___x_1908_, 1);
                            v___f_1910_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__1;
                            v___x_1911_ = lean_array_to_list(v_a_1909_);
                            v___x_1912_ = l_List_mergeSort___redArg(v___x_1911_, v___f_1910_);
                            v___x_1913_ = lean_array_mk(v___x_1912_);
                            v___x_1941_ = lean_array_get_size(v___x_1913_);
                            v___x_1942_ = lean_nat_dec_lt(v___x_1906_, v___x_1941_);
                            if v___x_1942_ == 0 {
                                v___y_1915_ = v___x_1892_;
                                state = 1;
                                continue;
                            } else {
                                if v___x_1942_ == 0 {
                                    v___y_1915_ = v___x_1892_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_1943_ = lean_usize_of_nat(v___x_1941_);
                                    v___x_1944_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(v___x_1913_, v___x_1903_, v___x_1943_);
                                    v___y_1915_ = v___x_1944_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_tree_1889_);
                            v_a_1945_ = crate::leanh::lean_ctor_get(v___x_1908_, 0);
                            v_isSharedCheck_1952_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1908_)) as u8;
                            if v_isSharedCheck_1952_ == 0 {
                                v___x_1947_ = v___x_1908_;
                                v_isShared_1948_ = v_isSharedCheck_1952_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1945_);
                                crate::leanh::lean_dec(v___x_1908_);
                                v___x_1947_ = crate::leanh::lean_box(0);
                                v_isShared_1948_ = v_isSharedCheck_1952_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_stack_x3f_1899_);
                        crate::leanh::lean_dec(v_requestedPos_1890_);
                        crate::leanh::lean_dec_ref(v_tree_1889_);
                        crate::leanh::lean_dec_ref(v_text_1886_);
                        v___x_1953_ = crate::leanh::lean_box(0);
                        v___x_1954_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1954_, 0, v___x_1953_);
                        return v___x_1954_;
                    }
                } else {
                    crate::leanh::lean_dec(v_requestedPos_1890_);
                    crate::leanh::lean_dec_ref(v_tree_1889_);
                    crate::leanh::lean_dec(v_cmdStx_1888_);
                    crate::leanh::lean_dec_ref(v_text_1886_);
                    v___x_1955_ = crate::leanh::lean_box(0);
                    v___x_1956_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1956_, 0, v___x_1955_);
                    return v___x_1956_;
                }
            }
            1 => {
                v___x_1916_ = crate::leanh::lean_box(0);
                v___x_1917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0;
                v_sz_1918_ = lean_array_size(v___x_1913_);
                v___x_1919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(v_tree_1889_, v___y_1915_, v___x_1892_, v___x_1913_, v_sz_1918_, v___x_1903_, v___x_1917_);
                crate::leanh::lean_dec_ref(v___x_1913_);
                if crate::leanh::lean_obj_tag(v___x_1919_) == 0 {
                    v_a_1920_ = crate::leanh::lean_ctor_get(v___x_1919_, 0);
                    v_isSharedCheck_1932_ = (!crate::leanh::lean_is_exclusive(v___x_1919_)) as u8;
                    if v_isSharedCheck_1932_ == 0 {
                        v___x_1922_ = v___x_1919_;
                        v_isShared_1923_ = v_isSharedCheck_1932_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1920_);
                        crate::leanh::lean_dec(v___x_1919_);
                        v___x_1922_ = crate::leanh::lean_box(0);
                        v_isShared_1923_ = v_isSharedCheck_1932_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1933_ = crate::leanh::lean_ctor_get(v___x_1919_, 0);
                    v_isSharedCheck_1940_ = (!crate::leanh::lean_is_exclusive(v___x_1919_)) as u8;
                    if v_isSharedCheck_1940_ == 0 {
                        v___x_1935_ = v___x_1919_;
                        v_isShared_1936_ = v_isSharedCheck_1940_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1933_);
                        crate::leanh::lean_dec(v___x_1919_);
                        v___x_1935_ = crate::leanh::lean_box(0);
                        v_isShared_1936_ = v_isSharedCheck_1940_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_1924_ = crate::leanh::lean_ctor_get(v_a_1920_, 0);
                crate::leanh::lean_inc(v_fst_1924_);
                crate::leanh::lean_dec(v_a_1920_);
                if crate::leanh::lean_obj_tag(v_fst_1924_) == 0 {
                    if v_isShared_1923_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1922_, 0, v___x_1916_);
                        v___x_1926_ = v___x_1922_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1927_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1916_);
                        v___x_1926_ = v_reuseFailAlloc_1927_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_val_1928_ = crate::leanh::lean_ctor_get(v_fst_1924_, 0);
                    crate::leanh::lean_inc(v_val_1928_);
                    crate::leanh::lean_dec_ref_known(v_fst_1924_, 1);
                    if v_isShared_1923_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1922_, 0, v_val_1928_);
                        v___x_1930_ = v___x_1922_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1931_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_val_1928_);
                        v___x_1930_ = v_reuseFailAlloc_1931_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1926_;
            }
            4 => {
                return v___x_1930_;
            }
            5 => {
                if v_isShared_1936_ == 0 {
                    v___x_1938_ = v___x_1935_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1939_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
                    v___x_1938_ = v_reuseFailAlloc_1939_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1938_;
            }
            7 => {
                if v_isShared_1948_ == 0 {
                    v___x_1950_ = v___x_1947_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1951_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
                    v___x_1950_ = v_reuseFailAlloc_1951_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1950_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___boxed(
    mut v_text_1957_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_1958_: *mut crate::leanh::LeanObject,
    mut v_cmdStx_1959_: *mut crate::leanh::LeanObject,
    mut v_tree_1960_: *mut crate::leanh::LeanObject,
    mut v_requestedPos_1961_: *mut crate::leanh::LeanObject,
    mut v_a_1962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1963_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f(
        v_text_1957_,
        v_ctx_x3f_1958_,
        v_cmdStx_1959_,
        v_tree_1960_,
        v_requestedPos_1961_,
    );
    crate::leanh::lean_dec(v_ctx_x3f_1958_);
    return v_res_1963_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3(
    mut v_upperBound_1964_: *mut crate::leanh::LeanObject,
    mut v_stack_1965_: *mut crate::leanh::LeanObject,
    mut v_text_1966_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_1967_: *mut crate::leanh::LeanObject,
    mut v_requestedPos_1968_: *mut crate::leanh::LeanObject,
    mut v___x_1969_: u8,
    mut v_inst_1970_: *mut crate::leanh::LeanObject,
    mut v_R_1971_: *mut crate::leanh::LeanObject,
    mut v_a_1972_: *mut crate::leanh::LeanObject,
    mut v_b_1973_: *mut crate::leanh::LeanObject,
    mut v_c_1974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1976_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(v_upperBound_1964_, v_stack_1965_, v_text_1966_, v_ctx_x3f_1967_, v_requestedPos_1968_, v___x_1969_, v_a_1972_, v_b_1973_);
    return v___x_1976_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___boxed(
    mut v_upperBound_1977_: *mut crate::leanh::LeanObject,
    mut v_stack_1978_: *mut crate::leanh::LeanObject,
    mut v_text_1979_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_1980_: *mut crate::leanh::LeanObject,
    mut v_requestedPos_1981_: *mut crate::leanh::LeanObject,
    mut v___x_1982_: *mut crate::leanh::LeanObject,
    mut v_inst_1983_: *mut crate::leanh::LeanObject,
    mut v_R_1984_: *mut crate::leanh::LeanObject,
    mut v_a_1985_: *mut crate::leanh::LeanObject,
    mut v_b_1986_: *mut crate::leanh::LeanObject,
    mut v_c_1987_: *mut crate::leanh::LeanObject,
    mut v___y_1988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3606__boxed_1989_: u8 = 0;
    let mut v_res_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3606__boxed_1989_ = (crate::leanh::lean_unbox(v___x_1982_) as u8);
    v_res_1990_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3(v_upperBound_1977_, v_stack_1978_, v_text_1979_, v_ctx_x3f_1980_, v_requestedPos_1981_, v___x_3606__boxed_1989_, v_inst_1983_, v_R_1984_, v_a_1985_, v_b_1986_, v_c_1987_);
    crate::leanh::lean_dec(v_requestedPos_1981_);
    crate::leanh::lean_dec(v_ctx_x3f_1980_);
    crate::leanh::lean_dec_ref(v_stack_1978_);
    crate::leanh::lean_dec(v_upperBound_1977_);
    return v_res_1990_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_FileWorker_SignatureHelp(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_InfoUtils(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sort_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_FileWorker_SignatureHelp(
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
pub unsafe fn initialize_Lean_Server_FileWorker_SignatureHelp(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_InfoUtils(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Lsp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Sort_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_PrettyPrinter_Delaborator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_FileWorker_SignatureHelp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_FileWorker_SignatureHelp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Server_FileWorker_SignatureHelp(builtin);
}

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
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Syntax_getArg, l_Lean_Syntax_getTailPos_x3f,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once,
    lean_obj_tag, lean_uint8_once, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Delaborator_delabForallWithSignature___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___closed__0_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [45, 45, 0]};
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2: u8 = 0;
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__6_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__3_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [112, 105, 112, 101, 80, 114, 111, 106, 0]};
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__3_value) as *mut LeanObject;
static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__3_value) as *mut LeanObject,1787791066222317160 as *mut LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__5_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 114, 111, 106, 0]};
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__5_value) as *mut LeanObject;
static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__5_value) as *mut LeanObject,5353940006376281447 as *mut LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__7_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [100, 111, 116, 73, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__7_value) as *mut LeanObject;
static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__7_value) as *mut LeanObject,14183307858573822893 as *mut LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__10_value) as *mut LeanObject,5117844058249666356 as *mut LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__12_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__14_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__14_value) as *mut LeanObject;
static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__14_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15_value) as *mut LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__16_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 101, 114, 109, 95, 60, 124, 95, 0]};
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__16_value) as *mut LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__16_value) as *mut LeanObject,5917499938696079000 as *mut LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__17_value) as *mut LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__18_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 101, 114, 109, 95, 36, 95, 95, 0]};
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__18_value) as *mut LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__19_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__18_value) as *mut LeanObject,7247595903597861139 as *mut LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__19_value) as *mut LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20_value) as *mut LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__21_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 2 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__21_value) as *mut LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__22_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__22_value) as *mut LeanObject;
pub static l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__23_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__23: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__23_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__2_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__1_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__2_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__1_value:
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
    m_fun: l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__1_value
) as *mut LeanObject;
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0(
    mut v_x_996_: *mut LeanObject,
    mut v_x_997_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_996_) == 0 {
        if lean_obj_tag(v_x_997_) == 0 {
            let mut v___x_998_: u8 = 0;
            v___x_998_ = 1;
            return v___x_998_;
        } else {
            let mut v___x_999_: u8 = 0;
            v___x_999_ = 0;
            return v___x_999_;
        }
    } else {
        if lean_obj_tag(v_x_997_) == 0 {
            let mut v___x_1000_: u8 = 0;
            v___x_1000_ = 0;
            return v___x_1000_;
        } else {
            let mut v_val_1001_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_1002_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1003_: u8 = 0;
            v_val_1001_ = lean_ctor_get(v_x_996_, 0);
            v_val_1002_ = lean_ctor_get(v_x_997_, 0);
            v___x_1003_ = l_Lean_Syntax_instBEqRange_beq(v_val_1001_, v_val_1002_);
            return v___x_1003_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0___boxed(
    mut v_x_1004_: *mut LeanObject,
    mut v_x_1005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1006_: u8 = 0;
    let mut v_r_1007_: *mut LeanObject = core::ptr::null_mut();
    v_res_1006_ = l_Option_instBEq_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0(v_x_1004_, v_x_1005_);
    lean_dec(v_x_1005_);
    lean_dec(v_x_1004_);
    v_r_1007_ = lean_box((v_res_1006_) as usize);
    return v_r_1007_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg(
    mut v_e_1008_: *mut LeanObject,
    mut v___y_1009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1011_: u8 = 0;
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1025_: u8 = 0;
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1031_: u8 = 0;
    let mut v_unused_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1011_ = l_Lean_Expr_hasMVar(v_e_1008_);
                if v___x_1011_ == 0 {
                    v___x_1012_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1012_, 0, v_e_1008_);
                    return v___x_1012_;
                } else {
                    v___x_1013_ = lean_st_ref_get(v___y_1009_);
                    v_mctx_1014_ = lean_ctor_get(v___x_1013_, 0);
                    lean_inc_ref(v_mctx_1014_);
                    lean_dec(v___x_1013_);
                    v___x_1015_ = l_Lean_instantiateMVarsCore(v_mctx_1014_, v_e_1008_);
                    v_fst_1016_ = lean_ctor_get(v___x_1015_, 0);
                    lean_inc(v_fst_1016_);
                    v_snd_1017_ = lean_ctor_get(v___x_1015_, 1);
                    lean_inc(v_snd_1017_);
                    lean_dec_ref(v___x_1015_);
                    v___x_1018_ = lean_st_ref_take(v___y_1009_);
                    v_cache_1019_ = lean_ctor_get(v___x_1018_, 1);
                    v_zetaDeltaFVarIds_1020_ = lean_ctor_get(v___x_1018_, 2);
                    v_postponed_1021_ = lean_ctor_get(v___x_1018_, 3);
                    v_diag_1022_ = lean_ctor_get(v___x_1018_, 4);
                    v_isSharedCheck_1031_ = (!lean_is_exclusive(v___x_1018_)) as u8;
                    if v_isSharedCheck_1031_ == 0 {
                        v_unused_1032_ = lean_ctor_get(v___x_1018_, 0);
                        lean_dec(v_unused_1032_);
                        v___x_1024_ = v___x_1018_;
                        v_isShared_1025_ = v_isSharedCheck_1031_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_1022_);
                        lean_inc(v_postponed_1021_);
                        lean_inc(v_zetaDeltaFVarIds_1020_);
                        lean_inc(v_cache_1019_);
                        lean_dec(v___x_1018_);
                        v___x_1024_ = lean_box(0);
                        v_isShared_1025_ = v_isSharedCheck_1031_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1025_ == 0 {
                    lean_ctor_set(v___x_1024_, 0, v_snd_1017_);
                    v___x_1027_ = v___x_1024_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_snd_1017_);
                    lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_cache_1019_);
                    lean_ctor_set(v_reuseFailAlloc_1030_, 2, v_zetaDeltaFVarIds_1020_);
                    lean_ctor_set(v_reuseFailAlloc_1030_, 3, v_postponed_1021_);
                    lean_ctor_set(v_reuseFailAlloc_1030_, 4, v_diag_1022_);
                    v___x_1027_ = v_reuseFailAlloc_1030_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1028_ = lean_st_ref_set(v___y_1009_, v___x_1027_);
                v___x_1029_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1029_, 0, v_fst_1016_);
                return v___x_1029_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg___boxed(
    mut v_e_1033_: *mut LeanObject,
    mut v___y_1034_: *mut LeanObject,
    mut v___y_1035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1036_: *mut LeanObject = core::ptr::null_mut();
    v_res_1036_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg(v_e_1033_, v___y_1034_);
    lean_dec(v___y_1034_);
    return v_res_1036_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1(
    mut v_e_1037_: *mut LeanObject,
    mut v___y_1038_: *mut LeanObject,
    mut v___y_1039_: *mut LeanObject,
    mut v___y_1040_: *mut LeanObject,
    mut v___y_1041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    v___x_1043_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg(v_e_1037_, v___y_1039_);
    return v___x_1043_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___boxed(
    mut v_e_1044_: *mut LeanObject,
    mut v___y_1045_: *mut LeanObject,
    mut v___y_1046_: *mut LeanObject,
    mut v___y_1047_: *mut LeanObject,
    mut v___y_1048_: *mut LeanObject,
    mut v___y_1049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1050_: *mut LeanObject = core::ptr::null_mut();
    v_res_1050_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1(v_e_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
    lean_dec(v___y_1048_);
    lean_dec_ref(v___y_1047_);
    lean_dec(v___y_1046_);
    lean_dec_ref(v___y_1045_);
    return v_res_1050_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__0(
    mut v_appStx_1051_: *mut LeanObject,
    mut v_x_1052_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_1052_) == 1 {
        let mut v_i_1053_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toElabInfo_1054_: *mut LeanObject = core::ptr::null_mut();
        let mut v_stx_1055_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1056_: u8 = 0;
        let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1059_: u8 = 0;
        v_i_1053_ = lean_ctor_get(v_x_1052_, 0);
        v_toElabInfo_1054_ = lean_ctor_get(v_i_1053_, 0);
        v_stx_1055_ = lean_ctor_get(v_toElabInfo_1054_, 1);
        v___x_1056_ = 0;
        v___x_1057_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_1055_, v___x_1056_);
        v___x_1058_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_appStx_1051_, v___x_1056_);
        v___x_1059_ = l_Option_instBEq_beq___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__0(v___x_1057_, v___x_1058_);
        lean_dec(v___x_1058_);
        lean_dec(v___x_1057_);
        return v___x_1059_;
    } else {
        let mut v___x_1060_: u8 = 0;
        v___x_1060_ = 0;
        return v___x_1060_;
    }
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__0___boxed(
    mut v_appStx_1061_: *mut LeanObject,
    mut v_x_1062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1063_: u8 = 0;
    let mut v_r_1064_: *mut LeanObject = core::ptr::null_mut();
    v_res_1063_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__0(
        v_appStx_1061_,
        v_x_1062_,
    );
    lean_dec_ref(v_x_1062_);
    lean_dec(v_appStx_1061_);
    v_r_1064_ = lean_box((v_res_1063_) as usize);
    return v_r_1064_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1(
    mut v_expr_1066_: *mut LeanObject,
    mut v___y_1067_: *mut LeanObject,
    mut v___y_1068_: *mut LeanObject,
    mut v___y_1069_: *mut LeanObject,
    mut v___y_1070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1078_: u8 = 0;
    let mut v___x_1079_: u8 = 0;
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1093_: u8 = 0;
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1098_: u8 = 0;
    let mut v_a_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1102_: u8 = 0;
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1106_: u8 = 0;
    let mut v_a_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1110_: u8 = 0;
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1114_: u8 = 0;
    let mut v_isSharedCheck_1115_: u8 = 0;
    let mut v_a_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1119_: u8 = 0;
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1123_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_1070_);
                lean_inc_ref(v___y_1069_);
                lean_inc(v___y_1068_);
                lean_inc_ref(v___y_1067_);
                v___x_1072_ = lean_infer_type(
                    v_expr_1066_,
                    v___y_1067_,
                    v___y_1068_,
                    v___y_1069_,
                    v___y_1070_,
                );
                if lean_obj_tag(v___x_1072_) == 0 {
                    v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
                    lean_inc(v_a_1073_);
                    lean_dec_ref_known(v___x_1072_, 1);
                    v___x_1074_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp_spec__1___redArg(v_a_1073_, v___y_1068_);
                    v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
                    v_isSharedCheck_1115_ = (!lean_is_exclusive(v___x_1074_)) as u8;
                    if v_isSharedCheck_1115_ == 0 {
                        v___x_1077_ = v___x_1074_;
                        v_isShared_1078_ = v_isSharedCheck_1115_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1075_);
                        lean_dec(v___x_1074_);
                        v___x_1077_ = lean_box(0);
                        v_isShared_1078_ = v_isSharedCheck_1115_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___y_1070_);
                    lean_dec_ref(v___y_1069_);
                    lean_dec(v___y_1068_);
                    lean_dec_ref(v___y_1067_);
                    v_a_1116_ = lean_ctor_get(v___x_1072_, 0);
                    v_isSharedCheck_1123_ = (!lean_is_exclusive(v___x_1072_)) as u8;
                    if v_isSharedCheck_1123_ == 0 {
                        v___x_1118_ = v___x_1072_;
                        v_isShared_1119_ = v_isSharedCheck_1123_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_1116_);
                        lean_dec(v___x_1072_);
                        v___x_1118_ = lean_box(0);
                        v_isShared_1119_ = v_isSharedCheck_1123_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1079_ = l_Lean_Expr_isForall(v_a_1075_);
                if v___x_1079_ == 0 {
                    lean_dec(v_a_1075_);
                    lean_dec(v___y_1070_);
                    lean_dec_ref(v___y_1069_);
                    lean_dec(v___y_1068_);
                    lean_dec_ref(v___y_1067_);
                    v___x_1080_ = lean_box(0);
                    if v_isShared_1078_ == 0 {
                        lean_ctor_set(v___x_1077_, 0, v___x_1080_);
                        v___x_1082_ = v___x_1077_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
                        v___x_1082_ = v_reuseFailAlloc_1083_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1077_);
                    v___x_1084_ = lean_box(1);
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
                    lean_dec(v___y_1068_);
                    lean_dec_ref(v___y_1067_);
                    if lean_obj_tag(v___x_1086_) == 0 {
                        v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
                        lean_inc(v_a_1087_);
                        lean_dec_ref_known(v___x_1086_, 1);
                        v_fst_1088_ = lean_ctor_get(v_a_1087_, 0);
                        lean_inc(v_fst_1088_);
                        lean_dec(v_a_1087_);
                        v___x_1089_ =
                            l_Lean_PrettyPrinter_ppTerm(v_fst_1088_, v___y_1069_, v___y_1070_);
                        lean_dec(v___y_1070_);
                        lean_dec_ref(v___y_1069_);
                        if lean_obj_tag(v___x_1089_) == 0 {
                            v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
                            v_isSharedCheck_1098_ = (!lean_is_exclusive(v___x_1089_)) as u8;
                            if v_isSharedCheck_1098_ == 0 {
                                v___x_1092_ = v___x_1089_;
                                v_isShared_1093_ = v_isSharedCheck_1098_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_1090_);
                                lean_dec(v___x_1089_);
                                v___x_1092_ = lean_box(0);
                                v_isShared_1093_ = v_isSharedCheck_1098_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_a_1099_ = lean_ctor_get(v___x_1089_, 0);
                            v_isSharedCheck_1106_ = (!lean_is_exclusive(v___x_1089_)) as u8;
                            if v_isSharedCheck_1106_ == 0 {
                                v___x_1101_ = v___x_1089_;
                                v_isShared_1102_ = v_isSharedCheck_1106_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_1099_);
                                lean_dec(v___x_1089_);
                                v___x_1101_ = lean_box(0);
                                v_isShared_1102_ = v_isSharedCheck_1106_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___y_1070_);
                        lean_dec_ref(v___y_1069_);
                        v_a_1107_ = lean_ctor_get(v___x_1086_, 0);
                        v_isSharedCheck_1114_ = (!lean_is_exclusive(v___x_1086_)) as u8;
                        if v_isSharedCheck_1114_ == 0 {
                            v___x_1109_ = v___x_1086_;
                            v_isShared_1110_ = v_isSharedCheck_1114_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_1107_);
                            lean_dec(v___x_1086_);
                            v___x_1109_ = lean_box(0);
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
                v___x_1094_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1094_, 0, v_a_1090_);
                if v_isShared_1093_ == 0 {
                    lean_ctor_set(v___x_1092_, 0, v___x_1094_);
                    v___x_1096_ = v___x_1092_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
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
                    v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
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
                    v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
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
                    v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
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
    mut v_expr_1124_: *mut LeanObject,
    mut v___y_1125_: *mut LeanObject,
    mut v___y_1126_: *mut LeanObject,
    mut v___y_1127_: *mut LeanObject,
    mut v___y_1128_: *mut LeanObject,
    mut v___y_1129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1130_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_tree_1133_: *mut LeanObject,
    mut v_appStx_1134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1152_: u8 = 0;
    let mut v_val_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1156_: u8 = 0;
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1173_: u8 = 0;
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1178_: u8 = 0;
    let mut v_a_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1182_: u8 = 0;
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1186_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1139_ = lean_alloc_closure(
                    l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_1139_, 0, v_appStx_1134_);
                v___x_1140_ = l_Lean_Elab_InfoTree_smallestInfo_x3f(v___f_1139_, v_tree_1133_);
                if lean_obj_tag(v___x_1140_) == 1 {
                    v_val_1141_ = lean_ctor_get(v___x_1140_, 0);
                    lean_inc(v_val_1141_);
                    lean_dec_ref_known(v___x_1140_, 1);
                    v_snd_1142_ = lean_ctor_get(v_val_1141_, 1);
                    if lean_obj_tag(v_snd_1142_) == 1 {
                        v_i_1143_ = lean_ctor_get(v_snd_1142_, 0);
                        lean_inc_ref(v_i_1143_);
                        v_fst_1144_ = lean_ctor_get(v_val_1141_, 0);
                        lean_inc(v_fst_1144_);
                        lean_dec(v_val_1141_);
                        v_lctx_1145_ = lean_ctor_get(v_i_1143_, 1);
                        lean_inc_ref(v_lctx_1145_);
                        v_expr_1146_ = lean_ctor_get(v_i_1143_, 3);
                        lean_inc_ref(v_expr_1146_);
                        lean_dec_ref(v_i_1143_);
                        v___f_1147_ = lean_alloc_closure(l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lam__1___boxed as *mut core::ffi::c_void, 6, 1);
                        lean_closure_set(v___f_1147_, 0, v_expr_1146_);
                        v___x_1148_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(
                            v_fst_1144_,
                            v_lctx_1145_,
                            v___f_1147_,
                        );
                        if lean_obj_tag(v___x_1148_) == 0 {
                            v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
                            v_isSharedCheck_1178_ = (!lean_is_exclusive(v___x_1148_)) as u8;
                            if v_isSharedCheck_1178_ == 0 {
                                v___x_1151_ = v___x_1148_;
                                v_isShared_1152_ = v_isSharedCheck_1178_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_1149_);
                                lean_dec(v___x_1148_);
                                v___x_1151_ = lean_box(0);
                                v_isShared_1152_ = v_isSharedCheck_1178_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_a_1179_ = lean_ctor_get(v___x_1148_, 0);
                            v_isSharedCheck_1186_ = (!lean_is_exclusive(v___x_1148_)) as u8;
                            if v_isSharedCheck_1186_ == 0 {
                                v___x_1181_ = v___x_1148_;
                                v_isShared_1182_ = v_isSharedCheck_1186_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_1179_);
                                lean_dec(v___x_1148_);
                                v___x_1181_ = lean_box(0);
                                v_isShared_1182_ = v_isSharedCheck_1186_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_val_1141_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1140_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1137_ = lean_box(0);
                v___x_1138_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1138_, 0, v___x_1137_);
                return v___x_1138_;
            }
            2 => {
                if lean_obj_tag(v_a_1149_) == 1 {
                    v_val_1153_ = lean_ctor_get(v_a_1149_, 0);
                    v_isSharedCheck_1173_ = (!lean_is_exclusive(v_a_1149_)) as u8;
                    if v_isSharedCheck_1173_ == 0 {
                        v___x_1155_ = v_a_1149_;
                        v_isShared_1156_ = v_isSharedCheck_1173_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_1153_);
                        lean_dec(v_a_1149_);
                        v___x_1155_ = lean_box(0);
                        v_isShared_1156_ = v_isSharedCheck_1173_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1149_);
                    v___x_1174_ = lean_box(0);
                    if v_isShared_1152_ == 0 {
                        lean_ctor_set(v___x_1151_, 0, v___x_1174_);
                        v___x_1176_ = v___x_1151_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1174_);
                        v___x_1176_ = v_reuseFailAlloc_1177_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1157_ = l_Std_Format_defWidth;
                v___x_1158_ = lean_unsigned_to_nat(0);
                v___x_1159_ =
                    l_Std_Format_pretty(v_val_1153_, v___x_1157_, v___x_1158_, v___x_1158_);
                v___x_1160_ = lean_box(0);
                v___x_1161_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_1161_, 0, v___x_1159_);
                lean_ctor_set(v___x_1161_, 1, v___x_1160_);
                lean_ctor_set(v___x_1161_, 2, v___x_1160_);
                lean_ctor_set(v___x_1161_, 3, v___x_1160_);
                v___x_1162_ = lean_unsigned_to_nat(1);
                v___x_1163_ = lean_mk_empty_array_with_capacity(v___x_1162_);
                v___x_1164_ = lean_array_push(v___x_1163_, v___x_1161_);
                v___x_1165_ =
                    l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___closed__0;
                v___x_1166_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1166_, 0, v___x_1164_);
                lean_ctor_set(v___x_1166_, 1, v___x_1165_);
                lean_ctor_set(v___x_1166_, 2, v___x_1160_);
                if v_isShared_1156_ == 0 {
                    lean_ctor_set(v___x_1155_, 0, v___x_1166_);
                    v___x_1168_ = v___x_1155_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1166_);
                    v___x_1168_ = v_reuseFailAlloc_1172_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1152_ == 0 {
                    lean_ctor_set(v___x_1151_, 0, v___x_1168_);
                    v___x_1170_ = v___x_1151_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
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
                    v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
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
    mut v_tree_1187_: *mut LeanObject,
    mut v_appStx_1188_: *mut LeanObject,
    mut v_a_1189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1190_: *mut LeanObject = core::ptr::null_mut();
    v_res_1190_ =
        l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp(v_tree_1187_, v_appStx_1188_);
    return v_res_1190_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx(
    mut v_x_1191_: u8,
) -> *mut LeanObject {
    match v_x_1191_ {
        0 => {
            let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
            v___x_1192_ = lean_unsigned_to_nat(0);
            return v___x_1192_;
        }
        1 => {
            let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
            v___x_1193_ = lean_unsigned_to_nat(1);
            return v___x_1193_;
        }
        _ => {
            let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
            v___x_1194_ = lean_unsigned_to_nat(2);
            return v___x_1194_;
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx___boxed(
    mut v_x_1195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_1196_: u8 = 0;
    let mut v_res_1197_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_1196_ = (lean_unbox(v_x_1195_) as u8);
    v_res_1197_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx(v_x_boxed_1196_);
    return v_res_1197_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_toCtorIdx(
    mut v_x_1198_: u8,
) -> *mut LeanObject {
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    v___x_1199_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorIdx(v_x_1198_);
    return v___x_1199_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_toCtorIdx___boxed(
    mut v_x_1200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_1201_: u8 = 0;
    let mut v_res_1202_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1201_ = (lean_unbox(v_x_1200_) as u8);
    v_res_1202_ =
        l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_toCtorIdx(v_x_4__boxed_1201_);
    return v_res_1202_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___redArg(
    mut v_k_1203_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_1203_);
    return v_k_1203_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___redArg___boxed(
    mut v_k_1204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1205_: *mut LeanObject = core::ptr::null_mut();
    v_res_1205_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___redArg(v_k_1204_);
    lean_dec(v_k_1204_);
    return v_res_1205_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim(
    mut v_motive_1206_: *mut LeanObject,
    mut v_ctorIdx_1207_: *mut LeanObject,
    mut v_t_1208_: u8,
    mut v_h_1209_: *mut LeanObject,
    mut v_k_1210_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_1210_);
    return v_k_1210_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim___boxed(
    mut v_motive_1211_: *mut LeanObject,
    mut v_ctorIdx_1212_: *mut LeanObject,
    mut v_t_1213_: *mut LeanObject,
    mut v_h_1214_: *mut LeanObject,
    mut v_k_1215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1216_: u8 = 0;
    let mut v_res_1217_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1216_ = (lean_unbox(v_t_1213_) as u8);
    v_res_1217_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_ctorElim(
        v_motive_1211_,
        v_ctorIdx_1212_,
        v_t_boxed_1216_,
        v_h_1214_,
        v_k_1215_,
    );
    lean_dec(v_k_1215_);
    lean_dec(v_ctorIdx_1212_);
    return v_res_1217_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___redArg(
    mut v_pipeArg_1218_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_pipeArg_1218_);
    return v_pipeArg_1218_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___redArg___boxed(
    mut v_pipeArg_1219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1220_: *mut LeanObject = core::ptr::null_mut();
    v_res_1220_ =
        l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___redArg(v_pipeArg_1219_);
    lean_dec(v_pipeArg_1219_);
    return v_res_1220_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim(
    mut v_motive_1221_: *mut LeanObject,
    mut v_t_1222_: u8,
    mut v_h_1223_: *mut LeanObject,
    mut v_pipeArg_1224_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_pipeArg_1224_);
    return v_pipeArg_1224_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim___boxed(
    mut v_motive_1225_: *mut LeanObject,
    mut v_t_1226_: *mut LeanObject,
    mut v_h_1227_: *mut LeanObject,
    mut v_pipeArg_1228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1229_: u8 = 0;
    let mut v_res_1230_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1229_ = (lean_unbox(v_t_1226_) as u8);
    v_res_1230_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_pipeArg_elim(
        v_motive_1225_,
        v_t_boxed_1229_,
        v_h_1227_,
        v_pipeArg_1228_,
    );
    lean_dec(v_pipeArg_1228_);
    return v_res_1230_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___redArg(
    mut v_termArg_1231_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_termArg_1231_);
    return v_termArg_1231_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___redArg___boxed(
    mut v_termArg_1232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1233_: *mut LeanObject = core::ptr::null_mut();
    v_res_1233_ =
        l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___redArg(v_termArg_1232_);
    lean_dec(v_termArg_1232_);
    return v_res_1233_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim(
    mut v_motive_1234_: *mut LeanObject,
    mut v_t_1235_: u8,
    mut v_h_1236_: *mut LeanObject,
    mut v_termArg_1237_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_termArg_1237_);
    return v_termArg_1237_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim___boxed(
    mut v_motive_1238_: *mut LeanObject,
    mut v_t_1239_: *mut LeanObject,
    mut v_h_1240_: *mut LeanObject,
    mut v_termArg_1241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1242_: u8 = 0;
    let mut v_res_1243_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1242_ = (lean_unbox(v_t_1239_) as u8);
    v_res_1243_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_termArg_elim(
        v_motive_1238_,
        v_t_boxed_1242_,
        v_h_1240_,
        v_termArg_1241_,
    );
    lean_dec(v_termArg_1241_);
    return v_res_1243_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___redArg(
    mut v_appArg_1244_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_appArg_1244_);
    return v_appArg_1244_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___redArg___boxed(
    mut v_appArg_1245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1246_: *mut LeanObject = core::ptr::null_mut();
    v_res_1246_ =
        l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___redArg(v_appArg_1245_);
    lean_dec(v_appArg_1245_);
    return v_res_1246_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim(
    mut v_motive_1247_: *mut LeanObject,
    mut v_t_1248_: u8,
    mut v_h_1249_: *mut LeanObject,
    mut v_appArg_1250_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_appArg_1250_);
    return v_appArg_1250_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim___boxed(
    mut v_motive_1251_: *mut LeanObject,
    mut v_t_1252_: *mut LeanObject,
    mut v_h_1253_: *mut LeanObject,
    mut v_appArg_1254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1255_: u8 = 0;
    let mut v_res_1256_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1255_ = (lean_unbox(v_t_1252_) as u8);
    v_res_1256_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_appArg_elim(
        v_motive_1251_,
        v_t_boxed_1255_,
        v_h_1253_,
        v_appArg_1254_,
    );
    lean_dec(v_appArg_1254_);
    return v_res_1256_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(
    mut v_x_1257_: u8,
) -> *mut LeanObject {
    match v_x_1257_ {
        0 => {
            let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
            v___x_1258_ = lean_unsigned_to_nat(0);
            return v___x_1258_;
        }
        1 => {
            let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
            v___x_1259_ = lean_unsigned_to_nat(1);
            return v___x_1259_;
        }
        _ => {
            let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
            v___x_1260_ = lean_unsigned_to_nat(2);
            return v___x_1260_;
        }
    }
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio___boxed(
    mut v_x_1261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_34__boxed_1262_: u8 = 0;
    let mut v_res_1263_: *mut LeanObject = core::ptr::null_mut();
    v_x_34__boxed_1262_ = (lean_unbox(v_x_1261_) as u8);
    v_res_1263_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_x_34__boxed_1262_);
    return v_res_1263_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx(
    mut v_x_1264_: u8,
) -> *mut LeanObject {
    if v_x_1264_ == 0 {
        let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
        v___x_1265_ = lean_unsigned_to_nat(0);
        return v___x_1265_;
    } else {
        let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
        v___x_1266_ = lean_unsigned_to_nat(1);
        return v___x_1266_;
    }
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx___boxed(
    mut v_x_1267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_1268_: u8 = 0;
    let mut v_res_1269_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_1268_ = (lean_unbox(v_x_1267_) as u8);
    v_res_1269_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx(v_x_boxed_1268_);
    return v_res_1269_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_toCtorIdx(
    mut v_x_1270_: u8,
) -> *mut LeanObject {
    let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
    v___x_1271_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorIdx(v_x_1270_);
    return v___x_1271_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_toCtorIdx___boxed(
    mut v_x_1272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_1273_: u8 = 0;
    let mut v_res_1274_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1273_ = (lean_unbox(v_x_1272_) as u8);
    v_res_1274_ =
        l_Lean_Server_FileWorker_SignatureHelp_SearchControl_toCtorIdx(v_x_4__boxed_1273_);
    return v_res_1274_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___redArg(
    mut v_k_1275_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_1275_);
    return v_k_1275_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___redArg___boxed(
    mut v_k_1276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1277_: *mut LeanObject = core::ptr::null_mut();
    v_res_1277_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___redArg(v_k_1276_);
    lean_dec(v_k_1276_);
    return v_res_1277_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim(
    mut v_motive_1278_: *mut LeanObject,
    mut v_ctorIdx_1279_: *mut LeanObject,
    mut v_t_1280_: u8,
    mut v_h_1281_: *mut LeanObject,
    mut v_k_1282_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_1282_);
    return v_k_1282_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim___boxed(
    mut v_motive_1283_: *mut LeanObject,
    mut v_ctorIdx_1284_: *mut LeanObject,
    mut v_t_1285_: *mut LeanObject,
    mut v_h_1286_: *mut LeanObject,
    mut v_k_1287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1288_: u8 = 0;
    let mut v_res_1289_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1288_ = (lean_unbox(v_t_1285_) as u8);
    v_res_1289_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_ctorElim(
        v_motive_1283_,
        v_ctorIdx_1284_,
        v_t_boxed_1288_,
        v_h_1286_,
        v_k_1287_,
    );
    lean_dec(v_k_1287_);
    lean_dec(v_ctorIdx_1284_);
    return v_res_1289_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___redArg(
    mut v_continue_1290_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_continue_1290_);
    return v_continue_1290_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___redArg___boxed(
    mut v_continue_1291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1292_: *mut LeanObject = core::ptr::null_mut();
    v_res_1292_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___redArg(
        v_continue_1291_,
    );
    lean_dec(v_continue_1291_);
    return v_res_1292_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim(
    mut v_motive_1293_: *mut LeanObject,
    mut v_t_1294_: u8,
    mut v_h_1295_: *mut LeanObject,
    mut v_continue_1296_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_continue_1296_);
    return v_continue_1296_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim___boxed(
    mut v_motive_1297_: *mut LeanObject,
    mut v_t_1298_: *mut LeanObject,
    mut v_h_1299_: *mut LeanObject,
    mut v_continue_1300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1301_: u8 = 0;
    let mut v_res_1302_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1301_ = (lean_unbox(v_t_1298_) as u8);
    v_res_1302_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_continue_elim(
        v_motive_1297_,
        v_t_boxed_1301_,
        v_h_1299_,
        v_continue_1300_,
    );
    lean_dec(v_continue_1300_);
    return v_res_1302_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___redArg(
    mut v_stop_1303_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_stop_1303_);
    return v_stop_1303_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___redArg___boxed(
    mut v_stop_1304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1305_: *mut LeanObject = core::ptr::null_mut();
    v_res_1305_ =
        l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___redArg(v_stop_1304_);
    lean_dec(v_stop_1304_);
    return v_res_1305_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim(
    mut v_motive_1306_: *mut LeanObject,
    mut v_t_1307_: u8,
    mut v_h_1308_: *mut LeanObject,
    mut v_stop_1309_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_stop_1309_);
    return v_stop_1309_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim___boxed(
    mut v_motive_1310_: *mut LeanObject,
    mut v_t_1311_: *mut LeanObject,
    mut v_h_1312_: *mut LeanObject,
    mut v_stop_1313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1314_: u8 = 0;
    let mut v_res_1315_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1314_ = (lean_unbox(v_t_1311_) as u8);
    v_res_1315_ = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_stop_elim(
        v_motive_1310_,
        v_t_boxed_1314_,
        v_h_1312_,
        v_stop_1313_,
    );
    lean_dec(v_stop_1313_);
    return v_res_1315_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(
    mut v_s_1316_: *mut LeanObject,
    mut v___x_1317_: *mut LeanObject,
    mut v___x_1318_: *mut LeanObject,
    mut v_a_1319_: *mut LeanObject,
    mut v_b_1320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1327_: u8 = 0;
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1333_: u8 = 0;
    let mut v_needle_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_table_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stackPos_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_needlePos_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1340_: u8 = 0;
    let mut v_str_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_basePos_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: u8 = 0;
    let mut v___x_1348_: u8 = 0;
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stackByte_1351_: u8 = 0;
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_patByte_1353_: u8 = 0;
    let mut v___x_1354_: u8 = 0;
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: u8 = 0;
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNeedlePos_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: u8 = 0;
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextNeedlePos_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: u8 = 0;
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1388_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1321_ = lean_box(0);
                match lean_obj_tag(v_a_1319_) {
                    0 => {
                        v_pos_1322_ = lean_ctor_get(v_a_1319_, 0);
                        lean_inc(v_pos_1322_);
                        lean_dec_ref_known(v_a_1319_, 1);
                        v___x_1323_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1323_, 0, v_pos_1322_);
                        return v___x_1323_;
                    }
                    1 => {
                        v_pos_1324_ = lean_ctor_get(v_a_1319_, 0);
                        v_isSharedCheck_1333_ = (!lean_is_exclusive(v_a_1319_)) as u8;
                        if v_isSharedCheck_1333_ == 0 {
                            v___x_1326_ = v_a_1319_;
                            v_isShared_1327_ = v_isSharedCheck_1333_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_pos_1324_);
                            lean_dec(v_a_1319_);
                            v___x_1326_ = lean_box(0);
                            v_isShared_1327_ = v_isSharedCheck_1333_;
                            state = 1;
                            continue;
                        }
                    }
                    2 => {
                        v_needle_1334_ = lean_ctor_get(v_a_1319_, 0);
                        v_table_1335_ = lean_ctor_get(v_a_1319_, 1);
                        v_stackPos_1336_ = lean_ctor_get(v_a_1319_, 2);
                        v_needlePos_1337_ = lean_ctor_get(v_a_1319_, 3);
                        v_isSharedCheck_1388_ = (!lean_is_exclusive(v_a_1319_)) as u8;
                        if v_isSharedCheck_1388_ == 0 {
                            v___x_1339_ = v_a_1319_;
                            v_isShared_1340_ = v_isSharedCheck_1388_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_needlePos_1337_);
                            lean_inc(v_stackPos_1336_);
                            lean_inc(v_table_1335_);
                            lean_inc(v_needle_1334_);
                            lean_dec(v_a_1319_);
                            v___x_1339_ = lean_box(0);
                            v_isShared_1340_ = v_isSharedCheck_1388_;
                            state = 3;
                            continue;
                        }
                    }
                    _ => {
                        lean_inc(v_b_1320_);
                        return v_b_1320_;
                    }
                }
            }
            1 => {
                v___x_1328_ = lean_string_utf8_next_fast(v_s_1316_, v_pos_1324_);
                lean_dec(v_pos_1324_);
                if v_isShared_1327_ == 0 {
                    lean_ctor_set_tag(v___x_1326_, 0);
                    lean_ctor_set(v___x_1326_, 0, v___x_1328_);
                    v___x_1330_ = v___x_1326_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1328_);
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
                v_str_1341_ = lean_ctor_get(v_needle_1334_, 0);
                v_startInclusive_1342_ = lean_ctor_get(v_needle_1334_, 1);
                v_endExclusive_1343_ = lean_ctor_get(v_needle_1334_, 2);
                v_basePos_1344_ = lean_nat_sub(v_stackPos_1336_, v_needlePos_1337_);
                v___x_1345_ = lean_nat_sub(v_endExclusive_1343_, v_startInclusive_1342_);
                v___x_1346_ = lean_nat_add(v_basePos_1344_, v___x_1345_);
                v___x_1347_ = lean_nat_dec_le(v___x_1346_, v___x_1318_);
                lean_dec(v___x_1346_);
                if v___x_1347_ == 0 {
                    lean_dec(v___x_1345_);
                    lean_del_object(v___x_1339_);
                    lean_dec(v_needlePos_1337_);
                    lean_dec(v_stackPos_1336_);
                    lean_dec_ref(v_table_1335_);
                    lean_dec_ref(v_needle_1334_);
                    v___x_1348_ = lean_nat_dec_lt(v_basePos_1344_, v___x_1318_);
                    lean_dec(v_basePos_1344_);
                    if v___x_1348_ == 0 {
                        lean_inc(v_b_1320_);
                        return v_b_1320_;
                    } else {
                        v___x_1349_ = lean_box(3);
                        v_a_1319_ = v___x_1349_;
                        v_b_1320_ = v___x_1321_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec(v_basePos_1344_);
                    lean_inc(v_stackPos_1336_);
                    v_stackByte_1351_ = lean_string_get_byte_fast(v_s_1316_, v_stackPos_1336_);
                    v___x_1352_ = lean_nat_add(v_startInclusive_1342_, v_needlePos_1337_);
                    v_patByte_1353_ = lean_string_get_byte_fast(v_str_1341_, v___x_1352_);
                    v___x_1354_ = lean_uint8_dec_eq(v_stackByte_1351_, v_patByte_1353_);
                    if v___x_1354_ == 0 {
                        lean_dec(v___x_1345_);
                        v___x_1355_ = lean_unsigned_to_nat(0);
                        v___x_1356_ = lean_nat_dec_eq(v_needlePos_1337_, v___x_1355_);
                        if v___x_1356_ == 0 {
                            v___x_1357_ = lean_unsigned_to_nat(1);
                            v___x_1358_ = lean_nat_sub(v_needlePos_1337_, v___x_1357_);
                            lean_dec(v_needlePos_1337_);
                            v_newNeedlePos_1359_ =
                                lean_array_fget_borrowed(v_table_1335_, v___x_1358_);
                            lean_dec(v___x_1358_);
                            v___x_1360_ = lean_nat_dec_eq(v_newNeedlePos_1359_, v___x_1355_);
                            if v___x_1360_ == 0 {
                                lean_inc(v_newNeedlePos_1359_);
                                if v_isShared_1340_ == 0 {
                                    lean_ctor_set(v___x_1339_, 3, v_newNeedlePos_1359_);
                                    v___x_1362_ = v___x_1339_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1364_ = lean_alloc_ctor(2, 4, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_needle_1334_);
                                    lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_table_1335_);
                                    lean_ctor_set(v_reuseFailAlloc_1364_, 2, v_stackPos_1336_);
                                    lean_ctor_set(v_reuseFailAlloc_1364_, 3, v_newNeedlePos_1359_);
                                    v___x_1362_ = v_reuseFailAlloc_1364_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                v_nextStackPos_1365_ =
                                    l_String_Slice_posGE___redArg(v___x_1317_, v_stackPos_1336_);
                                if v_isShared_1340_ == 0 {
                                    lean_ctor_set(v___x_1339_, 3, v___x_1355_);
                                    lean_ctor_set(v___x_1339_, 2, v_nextStackPos_1365_);
                                    v___x_1367_ = v___x_1339_;
                                    state = 5;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1369_ = lean_alloc_ctor(2, 4, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_needle_1334_);
                                    lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_table_1335_);
                                    lean_ctor_set(v_reuseFailAlloc_1369_, 2, v_nextStackPos_1365_);
                                    lean_ctor_set(v_reuseFailAlloc_1369_, 3, v___x_1355_);
                                    v___x_1367_ = v_reuseFailAlloc_1369_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_needlePos_1337_);
                            v___x_1370_ = lean_unsigned_to_nat(1);
                            v___x_1371_ = lean_nat_add(v_stackPos_1336_, v___x_1370_);
                            lean_dec(v_stackPos_1336_);
                            v_nextStackPos_1372_ =
                                l_String_Slice_posGE___redArg(v___x_1317_, v___x_1371_);
                            if v_isShared_1340_ == 0 {
                                lean_ctor_set(v___x_1339_, 3, v___x_1355_);
                                lean_ctor_set(v___x_1339_, 2, v_nextStackPos_1372_);
                                v___x_1374_ = v___x_1339_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_1376_ = lean_alloc_ctor(2, 4, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_needle_1334_);
                                lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_table_1335_);
                                lean_ctor_set(v_reuseFailAlloc_1376_, 2, v_nextStackPos_1372_);
                                lean_ctor_set(v_reuseFailAlloc_1376_, 3, v___x_1355_);
                                v___x_1374_ = v_reuseFailAlloc_1376_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        v___x_1377_ = lean_unsigned_to_nat(1);
                        v_nextStackPos_1378_ = lean_nat_add(v_stackPos_1336_, v___x_1377_);
                        lean_dec(v_stackPos_1336_);
                        v_nextNeedlePos_1379_ = lean_nat_add(v_needlePos_1337_, v___x_1377_);
                        lean_dec(v_needlePos_1337_);
                        v___x_1380_ = lean_nat_dec_eq(v_nextNeedlePos_1379_, v___x_1345_);
                        lean_dec(v___x_1345_);
                        if v___x_1380_ == 0 {
                            if v_isShared_1340_ == 0 {
                                lean_ctor_set(v___x_1339_, 3, v_nextNeedlePos_1379_);
                                lean_ctor_set(v___x_1339_, 2, v_nextStackPos_1378_);
                                v___x_1382_ = v___x_1339_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_1384_ = lean_alloc_ctor(2, 4, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_needle_1334_);
                                lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_table_1335_);
                                lean_ctor_set(v_reuseFailAlloc_1384_, 2, v_nextStackPos_1378_);
                                lean_ctor_set(v_reuseFailAlloc_1384_, 3, v_nextNeedlePos_1379_);
                                v___x_1382_ = v_reuseFailAlloc_1384_;
                                state = 7;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_1339_);
                            lean_dec_ref(v_table_1335_);
                            lean_dec_ref(v_needle_1334_);
                            v___x_1385_ = lean_nat_sub(v_nextStackPos_1378_, v_nextNeedlePos_1379_);
                            lean_dec(v_nextNeedlePos_1379_);
                            lean_dec(v_nextStackPos_1378_);
                            v___x_1386_ = l_String_Slice_pos_x21(v___x_1317_, v___x_1385_);
                            lean_dec(v___x_1385_);
                            v___x_1387_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_1387_, 0, v___x_1386_);
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
    mut v_s_1389_: *mut LeanObject,
    mut v___x_1390_: *mut LeanObject,
    mut v___x_1391_: *mut LeanObject,
    mut v_a_1392_: *mut LeanObject,
    mut v_b_1393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1394_: *mut LeanObject = core::ptr::null_mut();
    v_res_1394_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(v_s_1389_, v___x_1390_, v___x_1391_, v_a_1392_, v_b_1393_);
    lean_dec(v_b_1393_);
    lean_dec(v___x_1391_);
    lean_dec_ref(v___x_1390_);
    lean_dec_ref(v_s_1389_);
    return v_res_1394_;
}
pub unsafe fn _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1()
-> *mut LeanObject {
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    v___x_1396_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__0;
    v___x_1397_ = lean_string_utf8_byte_size(v___x_1396_);
    return v___x_1397_;
}
pub unsafe fn _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2()
-> u8 {
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: u8 = 0;
    v___x_1398_ = lean_unsigned_to_nat(0);
    v___x_1399_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1_once), _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1);
    v___x_1400_ = lean_nat_dec_eq(v___x_1399_, v___x_1398_);
    return v___x_1400_;
}
pub unsafe fn _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3()
-> *mut LeanObject {
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    v___x_1401_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1_once), _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1);
    v___x_1402_ = lean_unsigned_to_nat(0);
    v___x_1403_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__0;
    v___x_1404_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1404_, 0, v___x_1403_);
    lean_ctor_set(v___x_1404_, 1, v___x_1402_);
    lean_ctor_set(v___x_1404_, 2, v___x_1401_);
    return v___x_1404_;
}
pub unsafe fn _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4()
-> *mut LeanObject {
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    v___x_1405_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3_once), _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3);
    v___x_1406_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_1405_);
    return v___x_1406_;
}
pub unsafe fn _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5()
-> *mut LeanObject {
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    v___x_1407_ = lean_unsigned_to_nat(0);
    v___x_1408_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4_once), _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__4);
    v___x_1409_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3_once), _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__3);
    v___x_1410_ = lean_alloc_ctor(2, 4, (0) as u32);
    lean_ctor_set(v___x_1410_, 0, v___x_1409_);
    lean_ctor_set(v___x_1410_, 1, v___x_1408_);
    lean_ctor_set(v___x_1410_, 2, v___x_1407_);
    lean_ctor_set(v___x_1410_, 3, v___x_1407_);
    return v___x_1410_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f(
    mut v_s_1413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1424_: u8 = 0;
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1428_: u8 = 0;
    let mut v___x_1429_: u8 = 0;
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1414_ = lean_unsigned_to_nat(0);
                v___x_1415_ = lean_string_utf8_byte_size(v_s_1413_);
                lean_inc_ref(v_s_1413_);
                v___x_1416_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1416_, 0, v_s_1413_);
                lean_ctor_set(v___x_1416_, 1, v___x_1414_);
                lean_ctor_set(v___x_1416_, 2, v___x_1415_);
                v___x_1429_ = lean_uint8_once(core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2_once), _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2);
                if v___x_1429_ == 0 {
                    v___x_1430_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5_once), _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__5);
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
                v___x_1419_ = lean_box(0);
                lean_inc(v___y_1418_);
                v___x_1420_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(v_s_1413_, v___x_1416_, v___x_1415_, v___y_1418_, v___x_1419_);
                lean_dec_ref_known(v___x_1416_, 3);
                lean_dec_ref(v_s_1413_);
                if lean_obj_tag(v___x_1420_) == 0 {
                    return v___x_1419_;
                } else {
                    v_val_1421_ = lean_ctor_get(v___x_1420_, 0);
                    v_isSharedCheck_1428_ = (!lean_is_exclusive(v___x_1420_)) as u8;
                    if v_isSharedCheck_1428_ == 0 {
                        v___x_1423_ = v___x_1420_;
                        v_isShared_1424_ = v_isSharedCheck_1428_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_1421_);
                        lean_dec(v___x_1420_);
                        v___x_1423_ = lean_box(0);
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
                    v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_val_1421_);
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
    mut v_s_1432_: *mut LeanObject,
    mut v___x_1433_: *mut LeanObject,
    mut v___x_1434_: *mut LeanObject,
    mut v_inst_1435_: *mut LeanObject,
    mut v_R_1436_: *mut LeanObject,
    mut v_a_1437_: *mut LeanObject,
    mut v_b_1438_: *mut LeanObject,
    mut v_c_1439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    v___x_1440_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___redArg(v_s_1432_, v___x_1433_, v___x_1434_, v_a_1437_, v_b_1438_);
    return v___x_1440_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0___boxed(
    mut v_s_1441_: *mut LeanObject,
    mut v___x_1442_: *mut LeanObject,
    mut v___x_1443_: *mut LeanObject,
    mut v_inst_1444_: *mut LeanObject,
    mut v_R_1445_: *mut LeanObject,
    mut v_a_1446_: *mut LeanObject,
    mut v_b_1447_: *mut LeanObject,
    mut v_c_1448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1449_: *mut LeanObject = core::ptr::null_mut();
    v_res_1449_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f_spec__0(v_s_1441_, v___x_1442_, v___x_1443_, v_inst_1444_, v_R_1445_, v_a_1446_, v_b_1447_, v_c_1448_);
    lean_dec(v_b_1447_);
    lean_dec(v___x_1443_);
    lean_dec_ref(v___x_1442_);
    lean_dec_ref(v_s_1441_);
    return v_res_1449_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(
    mut v_text_1450_: *mut LeanObject,
    mut v_pos_1451_: *mut LeanObject,
) -> u8 {
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lineStartPos_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lineEndPos_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_text_1450_);
    v___x_1452_ = l_Lean_FileMap_toPosition(v_text_1450_, v_pos_1451_);
    v_line_1453_ = lean_ctor_get(v___x_1452_, 0);
    lean_inc(v_line_1453_);
    lean_dec_ref(v___x_1452_);
    v_source_1454_ = lean_ctor_get(v_text_1450_, 0);
    lean_inc_ref(v_source_1454_);
    v_lineStartPos_1455_ = l_Lean_FileMap_lineStart(v_text_1450_, v_line_1453_);
    v___x_1456_ = lean_unsigned_to_nat(1);
    v___x_1457_ = lean_nat_add(v_line_1453_, v___x_1456_);
    lean_dec(v_line_1453_);
    v_lineEndPos_1458_ = l_Lean_FileMap_lineStart(v_text_1450_, v___x_1457_);
    lean_dec(v___x_1457_);
    lean_dec_ref(v_text_1450_);
    v_line_1459_ =
        lean_string_utf8_extract(v_source_1454_, v_lineStartPos_1455_, v_lineEndPos_1458_);
    lean_dec(v_lineEndPos_1458_);
    lean_dec_ref(v_source_1454_);
    v___x_1460_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f(v_line_1459_);
    if lean_obj_tag(v___x_1460_) == 1 {
        let mut v_val_1461_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1463_: u8 = 0;
        v_val_1461_ = lean_ctor_get(v___x_1460_, 0);
        lean_inc(v_val_1461_);
        lean_dec_ref_known(v___x_1460_, 1);
        v___x_1462_ = lean_nat_add(v_lineStartPos_1455_, v_val_1461_);
        lean_dec(v_val_1461_);
        lean_dec(v_lineStartPos_1455_);
        v___x_1463_ = lean_nat_dec_le(v___x_1462_, v_pos_1451_);
        lean_dec(v___x_1462_);
        return v___x_1463_;
    } else {
        let mut v___x_1464_: u8 = 0;
        lean_dec(v___x_1460_);
        lean_dec(v_lineStartPos_1455_);
        v___x_1464_ = 0;
        return v___x_1464_;
    }
}
pub unsafe fn l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment___boxed(
    mut v_text_1465_: *mut LeanObject,
    mut v_pos_1466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1467_: u8 = 0;
    let mut v_r_1468_: *mut LeanObject = core::ptr::null_mut();
    v_res_1467_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(v_text_1465_, v_pos_1466_);
    lean_dec(v_pos_1466_);
    v_r_1468_ = lean_box((v_res_1467_) as usize);
    return v_r_1468_;
}
pub unsafe fn l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(
    mut v_text_1525_: *mut LeanObject,
    mut v_ctx_x3f_1526_: *mut LeanObject,
    mut v_requestedPos_1527_: *mut LeanObject,
    mut v_stx_1528_: *mut LeanObject,
    mut v_parent_1529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_x3f_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: u8 = 0;
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: u8 = 0;
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: u8 = 0;
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: u8 = 0;
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: u8 = 0;
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: u8 = 0;
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: u8 = 0;
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: u8 = 0;
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: u8 = 0;
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: u8 = 0;
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: u8 = 0;
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: u8 = 0;
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: u8 = 0;
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: u8 = 0;
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: u8 = 0;
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: u8 = 0;
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: u8 = 0;
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: u8 = 0;
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: u8 = 0;
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: u8 = 0;
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: u8 = 0;
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: u8 = 0;
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: u8 = 0;
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: u8 = 0;
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1630_: u8 = 0;
    let mut v___y_1631_: u8 = 0;
    let mut v___y_1632_: u8 = 0;
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: u8 = 0;
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: u8 = 0;
    let mut v___y_1639_: u8 = 0;
    let mut v___y_1640_: u8 = 0;
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_line_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: u8 = 0;
    let mut v___y_1647_: u8 = 0;
    let mut v_val_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isRetrigger_1649_: u8 = 0;
    let mut v_val_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_triggerKind_1651_: u8 = 0;
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1634_ = 1;
                v___x_1635_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1528_, v___x_1634_);
                if lean_obj_tag(v___x_1635_) == 1 {
                    v_val_1636_ = lean_ctor_get(v___x_1635_, 0);
                    lean_inc(v_val_1636_);
                    lean_dec_ref_known(v___x_1635_, 1);
                    v___x_1637_ = lean_nat_dec_lt(v_requestedPos_1527_, v_val_1636_);
                    if v___x_1637_ == 0 {
                        if lean_obj_tag(v_ctx_x3f_1526_) == 0 {
                            v___y_1647_ = v___x_1637_;
                            state = 5;
                            continue;
                        } else {
                            v_val_1650_ = lean_ctor_get(v_ctx_x3f_1526_, 0);
                            v_triggerKind_1651_ = lean_ctor_get_uint8(
                                v_val_1650_,
                                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
                        lean_dec(v_val_1636_);
                        lean_dec(v_parent_1529_);
                        lean_dec(v_stx_1528_);
                        lean_dec_ref(v_text_1525_);
                        v___x_1652_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__23;
                        return v___x_1652_;
                    }
                } else {
                    lean_dec(v___x_1635_);
                    lean_dec(v_parent_1529_);
                    lean_dec(v_stx_1528_);
                    lean_dec_ref(v_text_1525_);
                    v___x_1653_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__22;
                    return v___x_1653_;
                }
            }
            1 => {
                v___x_1532_ = 0;
                v___x_1533_ = lean_box((v___x_1532_) as usize);
                lean_inc(v_kind_x3f_1531_);
                v___x_1534_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1534_, 0, v_kind_x3f_1531_);
                lean_ctor_set(v___x_1534_, 1, v___x_1533_);
                return v___x_1534_;
            }
            2 => {
                if lean_obj_tag(v_stx_1528_) == 3 {
                    lean_dec_ref_known(v_stx_1528_, 4);
                    v___x_1536_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4;
                    lean_inc(v_parent_1529_);
                    v___x_1537_ = l_Lean_Syntax_isOfKind(v_parent_1529_, v___x_1536_);
                    if v___x_1537_ == 0 {
                        v___x_1538_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6;
                        lean_inc(v_parent_1529_);
                        v___x_1539_ = l_Lean_Syntax_isOfKind(v_parent_1529_, v___x_1538_);
                        if v___x_1539_ == 0 {
                            v___x_1540_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8;
                            lean_inc(v_parent_1529_);
                            v___x_1541_ = l_Lean_Syntax_isOfKind(v_parent_1529_, v___x_1540_);
                            if v___x_1541_ == 0 {
                                lean_dec(v_parent_1529_);
                                v___x_1542_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9;
                                v_kind_x3f_1531_ = v___x_1542_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1543_ = lean_unsigned_to_nat(1);
                                v___x_1544_ = l_Lean_Syntax_getArg(v_parent_1529_, v___x_1543_);
                                lean_dec(v_parent_1529_);
                                v___x_1545_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11;
                                v___x_1546_ = l_Lean_Syntax_isOfKind(v___x_1544_, v___x_1545_);
                                if v___x_1546_ == 0 {
                                    v___x_1547_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9;
                                    v_kind_x3f_1531_ = v___x_1547_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_1548_ = lean_box(0);
                                    v_kind_x3f_1531_ = v___x_1548_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v___x_1549_ = lean_unsigned_to_nat(2);
                            v___x_1550_ = l_Lean_Syntax_getArg(v_parent_1529_, v___x_1549_);
                            lean_dec(v_parent_1529_);
                            v___x_1551_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11;
                            v___x_1552_ = l_Lean_Syntax_isOfKind(v___x_1550_, v___x_1551_);
                            if v___x_1552_ == 0 {
                                v___x_1553_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9;
                                v_kind_x3f_1531_ = v___x_1553_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1554_ = lean_box(0);
                                v_kind_x3f_1531_ = v___x_1554_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v___x_1555_ = lean_unsigned_to_nat(2);
                        v___x_1556_ = l_Lean_Syntax_getArg(v_parent_1529_, v___x_1555_);
                        v___x_1557_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11;
                        v___x_1558_ = l_Lean_Syntax_isOfKind(v___x_1556_, v___x_1557_);
                        if v___x_1558_ == 0 {
                            lean_dec(v_parent_1529_);
                            v___x_1559_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9;
                            v_kind_x3f_1531_ = v___x_1559_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1560_ = lean_unsigned_to_nat(0);
                            v___x_1561_ = lean_unsigned_to_nat(3);
                            v___x_1562_ = l_Lean_Syntax_getArg(v_parent_1529_, v___x_1561_);
                            lean_dec(v_parent_1529_);
                            v___x_1563_ = l_Lean_Syntax_matchesNull(v___x_1562_, v___x_1560_);
                            if v___x_1563_ == 0 {
                                v___x_1564_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9;
                                v_kind_x3f_1531_ = v___x_1564_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1565_ = lean_box(0);
                                v_kind_x3f_1531_ = v___x_1565_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_parent_1529_);
                    if lean_obj_tag(v_stx_1528_) == 1 {
                        v_kind_1566_ = lean_ctor_get(v_stx_1528_, 1);
                        v_args_1567_ = lean_ctor_get(v_stx_1528_, 2);
                        lean_inc_ref(v_args_1567_);
                        v___x_1568_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__13;
                        v___x_1569_ = lean_name_eq(v_kind_1566_, v___x_1568_);
                        if v___x_1569_ == 0 {
                            v___x_1570_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__15;
                            v___x_1571_ = lean_name_eq(v_kind_1566_, v___x_1570_);
                            if v___x_1571_ == 0 {
                                v___x_1572_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__17;
                                lean_inc_ref(v_stx_1528_);
                                v___x_1573_ = l_Lean_Syntax_isOfKind(v_stx_1528_, v___x_1572_);
                                if v___x_1573_ == 0 {
                                    v___x_1574_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__19;
                                    lean_inc_ref(v_stx_1528_);
                                    v___x_1575_ = l_Lean_Syntax_isOfKind(v_stx_1528_, v___x_1574_);
                                    if v___x_1575_ == 0 {
                                        v___x_1576_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__4;
                                        lean_inc_ref(v_stx_1528_);
                                        v___x_1577_ =
                                            l_Lean_Syntax_isOfKind(v_stx_1528_, v___x_1576_);
                                        if v___x_1577_ == 0 {
                                            v___x_1578_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__8;
                                            lean_inc_ref(v_stx_1528_);
                                            v___x_1579_ =
                                                l_Lean_Syntax_isOfKind(v_stx_1528_, v___x_1578_);
                                            if v___x_1579_ == 0 {
                                                v___x_1580_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__6;
                                                lean_inc_ref(v_stx_1528_);
                                                v___x_1581_ = l_Lean_Syntax_isOfKind(
                                                    v_stx_1528_,
                                                    v___x_1580_,
                                                );
                                                if v___x_1581_ == 0 {
                                                    lean_dec_ref_known(v_stx_1528_, 3);
                                                    v___x_1582_ = lean_array_get_size(v_args_1567_);
                                                    lean_dec_ref(v_args_1567_);
                                                    v___x_1583_ = lean_unsigned_to_nat(1);
                                                    v___x_1584_ =
                                                        lean_nat_dec_le(v___x_1582_, v___x_1583_);
                                                    if v___x_1584_ == 0 {
                                                        v___x_1585_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9;
                                                        v_kind_x3f_1531_ = v___x_1585_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v___x_1586_ = lean_box(0);
                                                        v_kind_x3f_1531_ = v___x_1586_;
                                                        state = 1;
                                                        continue;
                                                    }
                                                } else {
                                                    v___x_1587_ = lean_unsigned_to_nat(2);
                                                    v___x_1588_ = l_Lean_Syntax_getArg(
                                                        v_stx_1528_,
                                                        v___x_1587_,
                                                    );
                                                    lean_dec_ref_known(v_stx_1528_, 3);
                                                    v___x_1589_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11;
                                                    v___x_1590_ = l_Lean_Syntax_isOfKind(
                                                        v___x_1588_,
                                                        v___x_1589_,
                                                    );
                                                    if v___x_1590_ == 0 {
                                                        v___x_1591_ = lean_unsigned_to_nat(1);
                                                        v___x_1592_ =
                                                            lean_array_get_size(v_args_1567_);
                                                        lean_dec_ref(v_args_1567_);
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
                                                            v___x_1595_ = lean_box(0);
                                                            v_kind_x3f_1531_ = v___x_1595_;
                                                            state = 1;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_args_1567_);
                                                        v___x_1596_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9;
                                                        v_kind_x3f_1531_ = v___x_1596_;
                                                        state = 1;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                v___x_1597_ = lean_unsigned_to_nat(1);
                                                v___x_1598_ =
                                                    l_Lean_Syntax_getArg(v_stx_1528_, v___x_1597_);
                                                lean_dec_ref_known(v_stx_1528_, 3);
                                                v___x_1599_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11;
                                                v___x_1600_ = l_Lean_Syntax_isOfKind(
                                                    v___x_1598_,
                                                    v___x_1599_,
                                                );
                                                if v___x_1600_ == 0 {
                                                    v___x_1601_ = lean_array_get_size(v_args_1567_);
                                                    lean_dec_ref(v_args_1567_);
                                                    v___x_1602_ =
                                                        lean_nat_dec_le(v___x_1601_, v___x_1597_);
                                                    if v___x_1602_ == 0 {
                                                        v___x_1603_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9;
                                                        v_kind_x3f_1531_ = v___x_1603_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v___x_1604_ = lean_box(0);
                                                        v_kind_x3f_1531_ = v___x_1604_;
                                                        state = 1;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_args_1567_);
                                                    v___x_1605_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9;
                                                    v_kind_x3f_1531_ = v___x_1605_;
                                                    state = 1;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            v___x_1606_ = lean_unsigned_to_nat(1);
                                            v___x_1607_ = lean_unsigned_to_nat(2);
                                            v___x_1608_ =
                                                l_Lean_Syntax_getArg(v_stx_1528_, v___x_1607_);
                                            v___x_1609_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__11;
                                            v___x_1610_ =
                                                l_Lean_Syntax_isOfKind(v___x_1608_, v___x_1609_);
                                            if v___x_1610_ == 0 {
                                                lean_dec_ref_known(v_stx_1528_, 3);
                                                v___x_1611_ = lean_array_get_size(v_args_1567_);
                                                lean_dec_ref(v_args_1567_);
                                                v___x_1612_ =
                                                    lean_nat_dec_le(v___x_1611_, v___x_1606_);
                                                if v___x_1612_ == 0 {
                                                    v___x_1613_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9;
                                                    v_kind_x3f_1531_ = v___x_1613_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___x_1614_ = lean_box(0);
                                                    v_kind_x3f_1531_ = v___x_1614_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                v___x_1615_ = lean_unsigned_to_nat(0);
                                                v___x_1616_ = lean_unsigned_to_nat(3);
                                                v___x_1617_ =
                                                    l_Lean_Syntax_getArg(v_stx_1528_, v___x_1616_);
                                                lean_dec_ref_known(v_stx_1528_, 3);
                                                v___x_1618_ = l_Lean_Syntax_matchesNull(
                                                    v___x_1617_,
                                                    v___x_1615_,
                                                );
                                                if v___x_1618_ == 0 {
                                                    v___x_1619_ = lean_array_get_size(v_args_1567_);
                                                    lean_dec_ref(v_args_1567_);
                                                    v___x_1620_ =
                                                        lean_nat_dec_le(v___x_1619_, v___x_1606_);
                                                    if v___x_1620_ == 0 {
                                                        v___x_1621_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__9;
                                                        v_kind_x3f_1531_ = v___x_1621_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v___x_1622_ = lean_box(0);
                                                        v_kind_x3f_1531_ = v___x_1622_;
                                                        state = 1;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_args_1567_);
                                                    v___x_1623_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20;
                                                    v_kind_x3f_1531_ = v___x_1623_;
                                                    state = 1;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v_args_1567_);
                                        lean_dec_ref_known(v_stx_1528_, 3);
                                        v___x_1624_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20;
                                        v_kind_x3f_1531_ = v___x_1624_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v_args_1567_);
                                    lean_dec_ref_known(v_stx_1528_, 3);
                                    v___x_1625_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__20;
                                    v_kind_x3f_1531_ = v___x_1625_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v_args_1567_);
                                lean_dec_ref_known(v_stx_1528_, 3);
                                v___x_1626_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__21;
                                v_kind_x3f_1531_ = v___x_1626_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_args_1567_);
                            lean_dec_ref_known(v_stx_1528_, 3);
                            v___x_1627_ = lean_box(0);
                            v_kind_x3f_1531_ = v___x_1627_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_stx_1528_);
                        v___x_1628_ = lean_box(0);
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
                            lean_dec(v_parent_1529_);
                            lean_dec(v_stx_1528_);
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
                lean_inc_ref(v_text_1525_);
                v___x_1641_ = l_Lean_FileMap_toPosition(v_text_1525_, v_requestedPos_1527_);
                v_line_1642_ = lean_ctor_get(v___x_1641_, 0);
                lean_inc(v_line_1642_);
                lean_dec_ref(v___x_1641_);
                v___x_1643_ = l_Lean_FileMap_toPosition(v_text_1525_, v_val_1636_);
                lean_dec(v_val_1636_);
                v_line_1644_ = lean_ctor_get(v___x_1643_, 0);
                lean_inc(v_line_1644_);
                lean_dec_ref(v___x_1643_);
                v___x_1645_ = lean_nat_dec_eq(v_line_1642_, v_line_1644_);
                lean_dec(v_line_1644_);
                lean_dec(v_line_1642_);
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
                if lean_obj_tag(v_ctx_x3f_1526_) == 0 {
                    v___y_1639_ = v___y_1647_;
                    v___y_1640_ = v___x_1637_;
                    state = 4;
                    continue;
                } else {
                    v_val_1648_ = lean_ctor_get(v_ctx_x3f_1526_, 0);
                    v_isRetrigger_1649_ = lean_ctor_get_uint8(
                        v_val_1648_,
                        (core::mem::size_of::<*mut LeanObject>() * 2 + 1) as u32,
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
    mut v_text_1654_: *mut LeanObject,
    mut v_ctx_x3f_1655_: *mut LeanObject,
    mut v_requestedPos_1656_: *mut LeanObject,
    mut v_stx_1657_: *mut LeanObject,
    mut v_parent_1658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1659_: *mut LeanObject = core::ptr::null_mut();
    v_res_1659_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(v_text_1654_, v_ctx_x3f_1655_, v_requestedPos_1656_, v_stx_1657_, v_parent_1658_);
    lean_dec(v_requestedPos_1656_);
    lean_dec(v_ctx_x3f_1655_);
    return v_res_1659_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0(
    mut v___x_1660_: u8,
    mut v_stx_1661_: *mut LeanObject,
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
    mut v___x_1664_: *mut LeanObject,
    mut v_stx_1665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3193__boxed_1666_: u8 = 0;
    let mut v_res_1667_: u8 = 0;
    let mut v_r_1668_: *mut LeanObject = core::ptr::null_mut();
    v___x_3193__boxed_1666_ = (lean_unbox(v___x_1664_) as u8);
    v_res_1667_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0(
        v___x_3193__boxed_1666_,
        v_stx_1665_,
    );
    lean_dec(v_stx_1665_);
    v_r_1668_ = lean_box((v_res_1667_) as usize);
    return v_r_1668_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1(
    mut v___x_1669_: u8,
    mut v_requestedPos_1670_: *mut LeanObject,
    mut v___x_1671_: u8,
    mut v_stx_1672_: *mut LeanObject,
) -> u8 {
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    v___x_1673_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_1672_, v___x_1669_);
    if lean_obj_tag(v___x_1673_) == 1 {
        let mut v_val_1674_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1675_: u8 = 0;
        v_val_1674_ = lean_ctor_get(v___x_1673_, 0);
        lean_inc(v_val_1674_);
        lean_dec_ref_known(v___x_1673_, 1);
        v___x_1675_ = l_Lean_Syntax_Range_contains(v_val_1674_, v_requestedPos_1670_, v___x_1669_);
        lean_dec(v_val_1674_);
        return v___x_1675_;
    } else {
        lean_dec(v___x_1673_);
        return v___x_1671_;
    }
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1___boxed(
    mut v___x_1676_: *mut LeanObject,
    mut v_requestedPos_1677_: *mut LeanObject,
    mut v___x_1678_: *mut LeanObject,
    mut v_stx_1679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3200__boxed_1680_: u8 = 0;
    let mut v___x_3201__boxed_1681_: u8 = 0;
    let mut v_res_1682_: u8 = 0;
    let mut v_r_1683_: *mut LeanObject = core::ptr::null_mut();
    v___x_3200__boxed_1680_ = (lean_unbox(v___x_1676_) as u8);
    v___x_3201__boxed_1681_ = (lean_unbox(v___x_1678_) as u8);
    v_res_1682_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1(
        v___x_3200__boxed_1680_,
        v_requestedPos_1677_,
        v___x_3201__boxed_1681_,
        v_stx_1679_,
    );
    lean_dec(v_stx_1679_);
    lean_dec(v_requestedPos_1677_);
    v_r_1683_ = lean_box((v_res_1682_) as usize);
    return v_r_1683_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2(
    mut v_c1_1684_: *mut LeanObject,
    mut v_c2_1685_: *mut LeanObject,
) -> u8 {
    let mut v_kind_1686_: u8 = 0;
    let mut v_kind_1687_: u8 = 0;
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: u8 = 0;
    v_kind_1686_ = lean_ctor_get_uint8(
        v_c2_1685_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v_kind_1687_ = lean_ctor_get_uint8(
        v_c1_1684_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v___x_1688_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_kind_1686_);
    v___x_1689_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_kind_1687_);
    v___x_1690_ = lean_nat_dec_le(v___x_1688_, v___x_1689_);
    lean_dec(v___x_1689_);
    lean_dec(v___x_1688_);
    return v___x_1690_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2___boxed(
    mut v_c1_1691_: *mut LeanObject,
    mut v_c2_1692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1693_: u8 = 0;
    let mut v_r_1694_: *mut LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__2(
        v_c1_1691_, v_c2_1692_,
    );
    lean_dec_ref(v_c2_1692_);
    lean_dec_ref(v_c1_1691_);
    v_r_1694_ = lean_box((v_res_1693_) as usize);
    return v_r_1694_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(
    mut v_tree_1703_: *mut LeanObject,
    mut v___y_1704_: u8,
    mut v___x_1705_: u8,
    mut v_as_1706_: *mut LeanObject,
    mut v_sz_1707_: usize,
    mut v_i_1708_: usize,
    mut v_b_1709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1711_: u8 = 0;
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_1714_: u8 = 0;
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_appStx_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1723_: u8 = 0;
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: usize = 0;
    let mut v___x_1730_: usize = 0;
    let mut v_isSharedCheck_1732_: u8 = 0;
    let mut v_a_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1736_: u8 = 0;
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1740_: u8 = 0;
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1711_ = lean_usize_dec_lt(v_i_1708_, v_sz_1707_);
                if v___x_1711_ == 0 {
                    lean_dec_ref(v_tree_1703_);
                    v___x_1712_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1712_, 0, v_b_1709_);
                    return v___x_1712_;
                } else {
                    lean_dec_ref(v_b_1709_);
                    v_a_1713_ = lean_array_uget_borrowed(v_as_1706_, v_i_1708_);
                    v_kind_1714_ = lean_ctor_get_uint8(
                        v_a_1713_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v___x_1715_ = lean_box(0);
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
                v_appStx_1718_ = lean_ctor_get(v_a_1713_, 0);
                lean_inc(v_appStx_1718_);
                lean_inc_ref(v_tree_1703_);
                v___x_1719_ = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp(
                    v_tree_1703_,
                    v_appStx_1718_,
                );
                if lean_obj_tag(v___x_1719_) == 0 {
                    v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
                    v_isSharedCheck_1732_ = (!lean_is_exclusive(v___x_1719_)) as u8;
                    if v_isSharedCheck_1732_ == 0 {
                        v___x_1722_ = v___x_1719_;
                        v_isShared_1723_ = v_isSharedCheck_1732_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1720_);
                        lean_dec(v___x_1719_);
                        v___x_1722_ = lean_box(0);
                        v_isShared_1723_ = v_isSharedCheck_1732_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_tree_1703_);
                    v_a_1733_ = lean_ctor_get(v___x_1719_, 0);
                    v_isSharedCheck_1740_ = (!lean_is_exclusive(v___x_1719_)) as u8;
                    if v_isSharedCheck_1740_ == 0 {
                        v___x_1735_ = v___x_1719_;
                        v_isShared_1736_ = v_isSharedCheck_1740_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1733_);
                        lean_dec(v___x_1719_);
                        v___x_1735_ = lean_box(0);
                        v_isShared_1736_ = v_isSharedCheck_1740_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_1720_) == 1 {
                    lean_dec_ref(v_tree_1703_);
                    v___x_1724_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1724_, 0, v_a_1720_);
                    v___x_1725_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1725_, 0, v___x_1724_);
                    lean_ctor_set(v___x_1725_, 1, v___x_1715_);
                    if v_isShared_1723_ == 0 {
                        lean_ctor_set(v___x_1722_, 0, v___x_1725_);
                        v___x_1727_ = v___x_1722_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1725_);
                        v___x_1727_ = v_reuseFailAlloc_1728_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1722_);
                    lean_dec(v_a_1720_);
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
                    v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
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
                    lean_dec_ref(v_tree_1703_);
                    v___x_1742_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__2;
                    v___x_1743_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1743_, 0, v___x_1742_);
                    return v___x_1743_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___boxed(
    mut v_tree_1744_: *mut LeanObject,
    mut v___y_1745_: *mut LeanObject,
    mut v___x_1746_: *mut LeanObject,
    mut v_as_1747_: *mut LeanObject,
    mut v_sz_1748_: *mut LeanObject,
    mut v_i_1749_: *mut LeanObject,
    mut v_b_1750_: *mut LeanObject,
    mut v___y_1751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3234__boxed_1752_: u8 = 0;
    let mut v___x_3235__boxed_1753_: u8 = 0;
    let mut v_sz_boxed_1754_: usize = 0;
    let mut v_i_boxed_1755_: usize = 0;
    let mut v_res_1756_: *mut LeanObject = core::ptr::null_mut();
    v___y_3234__boxed_1752_ = (lean_unbox(v___y_1745_) as u8);
    v___x_3235__boxed_1753_ = (lean_unbox(v___x_1746_) as u8);
    v_sz_boxed_1754_ = lean_unbox_usize(v_sz_1748_);
    lean_dec(v_sz_1748_);
    v_i_boxed_1755_ = lean_unbox_usize(v_i_1749_);
    lean_dec(v_i_1749_);
    v_res_1756_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(v_tree_1744_, v___y_3234__boxed_1752_, v___x_3235__boxed_1753_, v_as_1747_, v_sz_boxed_1754_, v_i_boxed_1755_, v_b_1750_);
    lean_dec_ref(v_as_1747_);
    return v_res_1756_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0()
-> *mut LeanObject {
    let mut v___x_1757_: u8 = 0;
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    v___x_1757_ = 1;
    v___x_1758_ = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v___x_1757_);
    return v___x_1758_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(
    mut v_as_1759_: *mut LeanObject,
    mut v_i_1760_: usize,
    mut v_stop_1761_: usize,
) -> u8 {
    let mut v___x_1762_: u8 = 0;
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_1764_: u8 = 0;
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
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
                    v_kind_1764_ = lean_ctor_get_uint8(
                        v___x_1763_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v___x_1765_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2___closed__0);
                    v___x_1766_ =
                        l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(v_kind_1764_);
                    v___x_1767_ = lean_nat_dec_lt(v___x_1765_, v___x_1766_);
                    lean_dec(v___x_1766_);
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
    mut v_as_1772_: *mut LeanObject,
    mut v_i_1773_: *mut LeanObject,
    mut v_stop_1774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1775_: usize = 0;
    let mut v_stop_boxed_1776_: usize = 0;
    let mut v_res_1777_: u8 = 0;
    let mut v_r_1778_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1775_ = lean_unbox_usize(v_i_1773_);
    lean_dec(v_i_1773_);
    v_stop_boxed_1776_ = lean_unbox_usize(v_stop_1774_);
    lean_dec(v_stop_1774_);
    v_res_1777_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__2(v_as_1772_, v_i_boxed_1775_, v_stop_boxed_1776_);
    lean_dec_ref(v_as_1772_);
    v_r_1778_ = lean_box((v_res_1777_) as usize);
    return v_r_1778_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(
    mut v_snd_1779_: u8,
    mut v___x_1780_: u8,
    mut v_____r_1781_: *mut LeanObject,
    mut v_candidates_1782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_snd_1779_ == 1 {
                    state = 1;
                    continue;
                } else {
                    if v___x_1780_ == 0 {
                        v___x_1787_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1787_, 0, v_candidates_1782_);
                        v___x_1788_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1788_, 0, v___x_1787_);
                        return v___x_1788_;
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1785_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1785_, 0, v_candidates_1782_);
                v___x_1786_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1786_, 0, v___x_1785_);
                return v___x_1786_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0___boxed(
    mut v_snd_1789_: *mut LeanObject,
    mut v___x_1790_: *mut LeanObject,
    mut v_____r_1791_: *mut LeanObject,
    mut v_candidates_1792_: *mut LeanObject,
    mut v___y_1793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_3336__boxed_1794_: u8 = 0;
    let mut v___x_3337__boxed_1795_: u8 = 0;
    let mut v_res_1796_: *mut LeanObject = core::ptr::null_mut();
    v_snd_3336__boxed_1794_ = (lean_unbox(v_snd_1789_) as u8);
    v___x_3337__boxed_1795_ = (lean_unbox(v___x_1790_) as u8);
    v_res_1796_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(v_snd_3336__boxed_1794_, v___x_3337__boxed_1795_, v_____r_1791_, v_candidates_1792_);
    return v_res_1796_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(
    mut v_upperBound_1797_: *mut LeanObject,
    mut v_stack_1798_: *mut LeanObject,
    mut v_text_1799_: *mut LeanObject,
    mut v_ctx_x3f_1800_: *mut LeanObject,
    mut v_requestedPos_1801_: *mut LeanObject,
    mut v___x_1802_: u8,
    mut v_a_1803_: *mut LeanObject,
    mut v_b_1804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1811_: u8 = 0;
    let mut v_a_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1820_: u8 = 0;
    let mut v_a_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1824_: u8 = 0;
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1828_: u8 = 0;
    let mut v___x_1829_: u8 = 0;
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: u8 = 0;
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: u8 = 0;
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: u8 = 0;
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: u8 = 0;
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1829_ = lean_nat_dec_lt(v_a_1803_, v_upperBound_1797_);
                if v___x_1829_ == 0 {
                    lean_dec(v_a_1803_);
                    lean_dec_ref(v_text_1799_);
                    v___x_1830_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1830_, 0, v_b_1804_);
                    return v___x_1830_;
                } else {
                    v___x_1831_ = lean_array_fget_borrowed(v_stack_1798_, v_a_1803_);
                    v___x_1848_ = lean_unsigned_to_nat(1);
                    v___x_1849_ = lean_nat_add(v_a_1803_, v___x_1848_);
                    v___x_1850_ = lean_array_get_size(v_stack_1798_);
                    v___x_1851_ = lean_nat_dec_lt(v___x_1849_, v___x_1850_);
                    if v___x_1851_ == 0 {
                        lean_dec(v___x_1849_);
                        v___x_1852_ = lean_box(0);
                        v___y_1833_ = v___x_1852_;
                        state = 6;
                        continue;
                    } else {
                        v___x_1853_ = lean_array_fget_borrowed(v_stack_1798_, v___x_1849_);
                        lean_dec(v___x_1849_);
                        lean_inc(v___x_1853_);
                        v___y_1833_ = v___x_1853_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_1807_) == 0 {
                    v_a_1808_ = lean_ctor_get(v___y_1807_, 0);
                    v_isSharedCheck_1820_ = (!lean_is_exclusive(v___y_1807_)) as u8;
                    if v_isSharedCheck_1820_ == 0 {
                        v___x_1810_ = v___y_1807_;
                        v_isShared_1811_ = v_isSharedCheck_1820_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1808_);
                        lean_dec(v___y_1807_);
                        v___x_1810_ = lean_box(0);
                        v_isShared_1811_ = v_isSharedCheck_1820_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1803_);
                    lean_dec_ref(v_text_1799_);
                    v_a_1821_ = lean_ctor_get(v___y_1807_, 0);
                    v_isSharedCheck_1828_ = (!lean_is_exclusive(v___y_1807_)) as u8;
                    if v_isSharedCheck_1828_ == 0 {
                        v___x_1823_ = v___y_1807_;
                        v_isShared_1824_ = v_isSharedCheck_1828_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1821_);
                        lean_dec(v___y_1807_);
                        v___x_1823_ = lean_box(0);
                        v_isShared_1824_ = v_isSharedCheck_1828_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_1808_) == 0 {
                    lean_dec(v_a_1803_);
                    lean_dec_ref(v_text_1799_);
                    v_a_1812_ = lean_ctor_get(v_a_1808_, 0);
                    lean_inc(v_a_1812_);
                    lean_dec_ref_known(v_a_1808_, 1);
                    if v_isShared_1811_ == 0 {
                        lean_ctor_set(v___x_1810_, 0, v_a_1812_);
                        v___x_1814_ = v___x_1810_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1812_);
                        v___x_1814_ = v_reuseFailAlloc_1815_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1810_);
                    v_a_1816_ = lean_ctor_get(v_a_1808_, 0);
                    lean_inc(v_a_1816_);
                    lean_dec_ref_known(v_a_1808_, 1);
                    v___x_1817_ = lean_unsigned_to_nat(1);
                    v___x_1818_ = lean_nat_add(v_a_1803_, v___x_1817_);
                    lean_dec(v_a_1803_);
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
                    v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
                    v___x_1826_ = v_reuseFailAlloc_1827_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1826_;
            }
            6 => {
                lean_inc(v___x_1831_);
                lean_inc_ref(v_text_1799_);
                v___x_1834_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(v_text_1799_, v_ctx_x3f_1800_, v_requestedPos_1801_, v___x_1831_, v___y_1833_);
                v_fst_1835_ = lean_ctor_get(v___x_1834_, 0);
                lean_inc(v_fst_1835_);
                if lean_obj_tag(v_fst_1835_) == 1 {
                    v_snd_1836_ = lean_ctor_get(v___x_1834_, 1);
                    lean_inc(v_snd_1836_);
                    lean_dec_ref(v___x_1834_);
                    v_val_1837_ = lean_ctor_get(v_fst_1835_, 0);
                    lean_inc(v_val_1837_);
                    lean_dec_ref_known(v_fst_1835_, 1);
                    lean_inc(v___x_1831_);
                    v___x_1838_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_1838_, 0, v___x_1831_);
                    v___x_1839_ = (lean_unbox(v_val_1837_) as u8);
                    lean_dec(v_val_1837_);
                    lean_ctor_set_uint8(
                        v___x_1838_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_1839_,
                    );
                    v___x_1840_ = lean_array_push(v_b_1804_, v___x_1838_);
                    v___x_1841_ = lean_box(0);
                    v___x_1842_ = (lean_unbox(v_snd_1836_) as u8);
                    lean_dec(v_snd_1836_);
                    v___x_1843_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg___lam__0(v___x_1842_, v___x_1802_, v___x_1841_, v___x_1840_);
                    v___y_1807_ = v___x_1843_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_fst_1835_);
                    v_snd_1844_ = lean_ctor_get(v___x_1834_, 1);
                    lean_inc(v_snd_1844_);
                    lean_dec_ref(v___x_1834_);
                    v___x_1845_ = lean_box(0);
                    v___x_1846_ = (lean_unbox(v_snd_1844_) as u8);
                    lean_dec(v_snd_1844_);
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
    mut v_upperBound_1854_: *mut LeanObject,
    mut v_stack_1855_: *mut LeanObject,
    mut v_text_1856_: *mut LeanObject,
    mut v_ctx_x3f_1857_: *mut LeanObject,
    mut v_requestedPos_1858_: *mut LeanObject,
    mut v___x_1859_: *mut LeanObject,
    mut v_a_1860_: *mut LeanObject,
    mut v_b_1861_: *mut LeanObject,
    mut v___y_1862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3359__boxed_1863_: u8 = 0;
    let mut v_res_1864_: *mut LeanObject = core::ptr::null_mut();
    v___x_3359__boxed_1863_ = (lean_unbox(v___x_1859_) as u8);
    v_res_1864_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(v_upperBound_1854_, v_stack_1855_, v_text_1856_, v_ctx_x3f_1857_, v_requestedPos_1858_, v___x_3359__boxed_1863_, v_a_1860_, v_b_1861_);
    lean_dec(v_requestedPos_1858_);
    lean_dec(v_ctx_x3f_1857_);
    lean_dec_ref(v_stack_1855_);
    lean_dec(v_upperBound_1854_);
    return v_res_1864_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(
    mut v_sz_1865_: usize,
    mut v_i_1866_: usize,
    mut v_bs_1867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1868_: u8 = 0;
    let mut v_v_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: usize = 0;
    let mut v___x_1874_: usize = 0;
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1868_ = lean_usize_dec_lt(v_i_1866_, v_sz_1865_);
                if v___x_1868_ == 0 {
                    return v_bs_1867_;
                } else {
                    v_v_1869_ = lean_array_uget_borrowed(v_bs_1867_, v_i_1866_);
                    v_fst_1870_ = lean_ctor_get(v_v_1869_, 0);
                    lean_inc(v_fst_1870_);
                    v___x_1871_ = lean_unsigned_to_nat(0);
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
    mut v_sz_1877_: *mut LeanObject,
    mut v_i_1878_: *mut LeanObject,
    mut v_bs_1879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1880_: usize = 0;
    let mut v_i_boxed_1881_: usize = 0;
    let mut v_res_1882_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1880_ = lean_unbox_usize(v_sz_1877_);
    lean_dec(v_sz_1877_);
    v_i_boxed_1881_ = lean_unbox_usize(v_i_1878_);
    lean_dec(v_i_1878_);
    v_res_1882_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(v_sz_boxed_1880_, v_i_boxed_1881_, v_bs_1879_);
    return v_res_1882_;
}
pub unsafe fn l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f(
    mut v_text_1886_: *mut LeanObject,
    mut v_ctx_x3f_1887_: *mut LeanObject,
    mut v_cmdStx_1888_: *mut LeanObject,
    mut v_tree_1889_: *mut LeanObject,
    mut v_requestedPos_1890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1892_: u8 = 0;
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: u8 = 0;
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stack_x3f_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1902_: usize = 0;
    let mut v___x_1903_: usize = 0;
    let mut v_stack_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_candidates_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1915_: u8 = 0;
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1918_: usize = 0;
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1923_: u8 = 0;
    let mut v_fst_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1932_: u8 = 0;
    let mut v_a_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1936_: u8 = 0;
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1940_: u8 = 0;
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: u8 = 0;
    let mut v___x_1943_: usize = 0;
    let mut v___x_1944_: u8 = 0;
    let mut v_a_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1948_: u8 = 0;
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1952_: u8 = 0;
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_text_1886_);
                v___x_1892_ = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(v_text_1886_, v_requestedPos_1890_);
                if v___x_1892_ == 0 {
                    v___x_1893_ = lean_box((v___x_1892_) as usize);
                    v___f_1894_ = lean_alloc_closure(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                    lean_closure_set(v___f_1894_, 0, v___x_1893_);
                    v___x_1895_ = 1;
                    v___x_1896_ = lean_box((v___x_1895_) as usize);
                    v___x_1897_ = lean_box((v___x_1892_) as usize);
                    lean_inc(v_requestedPos_1890_);
                    v___f_1898_ = lean_alloc_closure(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lam__1___boxed as *mut core::ffi::c_void, 4, 3);
                    lean_closure_set(v___f_1898_, 0, v___x_1896_);
                    lean_closure_set(v___f_1898_, 1, v_requestedPos_1890_);
                    lean_closure_set(v___f_1898_, 2, v___x_1897_);
                    v_stack_x3f_1899_ =
                        l_Lean_Syntax_findStack_x3f(v_cmdStx_1888_, v___f_1898_, v___f_1894_);
                    if lean_obj_tag(v_stack_x3f_1899_) == 1 {
                        v_val_1900_ = lean_ctor_get(v_stack_x3f_1899_, 0);
                        lean_inc(v_val_1900_);
                        lean_dec_ref_known(v_stack_x3f_1899_, 1);
                        v___x_1901_ = lean_array_mk(v_val_1900_);
                        v_sz_1902_ = lean_array_size(v___x_1901_);
                        v___x_1903_ = 0usize;
                        v_stack_1904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__0(v_sz_1902_, v___x_1903_, v___x_1901_);
                        v___x_1905_ = lean_array_get_size(v_stack_1904_);
                        v___x_1906_ = lean_unsigned_to_nat(0);
                        v_candidates_1907_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___closed__0;
                        v___x_1908_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(v___x_1905_, v_stack_1904_, v_text_1886_, v_ctx_x3f_1887_, v_requestedPos_1890_, v___x_1892_, v___x_1906_, v_candidates_1907_);
                        lean_dec(v_requestedPos_1890_);
                        lean_dec_ref(v_stack_1904_);
                        if lean_obj_tag(v___x_1908_) == 0 {
                            v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
                            lean_inc(v_a_1909_);
                            lean_dec_ref_known(v___x_1908_, 1);
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
                            lean_dec_ref(v_tree_1889_);
                            v_a_1945_ = lean_ctor_get(v___x_1908_, 0);
                            v_isSharedCheck_1952_ = (!lean_is_exclusive(v___x_1908_)) as u8;
                            if v_isSharedCheck_1952_ == 0 {
                                v___x_1947_ = v___x_1908_;
                                v_isShared_1948_ = v_isSharedCheck_1952_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_1945_);
                                lean_dec(v___x_1908_);
                                v___x_1947_ = lean_box(0);
                                v_isShared_1948_ = v_isSharedCheck_1952_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_stack_x3f_1899_);
                        lean_dec(v_requestedPos_1890_);
                        lean_dec_ref(v_tree_1889_);
                        lean_dec_ref(v_text_1886_);
                        v___x_1953_ = lean_box(0);
                        v___x_1954_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1954_, 0, v___x_1953_);
                        return v___x_1954_;
                    }
                } else {
                    lean_dec(v_requestedPos_1890_);
                    lean_dec_ref(v_tree_1889_);
                    lean_dec(v_cmdStx_1888_);
                    lean_dec_ref(v_text_1886_);
                    v___x_1955_ = lean_box(0);
                    v___x_1956_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1956_, 0, v___x_1955_);
                    return v___x_1956_;
                }
            }
            1 => {
                v___x_1916_ = lean_box(0);
                v___x_1917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1___closed__0;
                v_sz_1918_ = lean_array_size(v___x_1913_);
                v___x_1919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__1(v_tree_1889_, v___y_1915_, v___x_1892_, v___x_1913_, v_sz_1918_, v___x_1903_, v___x_1917_);
                lean_dec_ref(v___x_1913_);
                if lean_obj_tag(v___x_1919_) == 0 {
                    v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
                    v_isSharedCheck_1932_ = (!lean_is_exclusive(v___x_1919_)) as u8;
                    if v_isSharedCheck_1932_ == 0 {
                        v___x_1922_ = v___x_1919_;
                        v_isShared_1923_ = v_isSharedCheck_1932_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1920_);
                        lean_dec(v___x_1919_);
                        v___x_1922_ = lean_box(0);
                        v_isShared_1923_ = v_isSharedCheck_1932_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1933_ = lean_ctor_get(v___x_1919_, 0);
                    v_isSharedCheck_1940_ = (!lean_is_exclusive(v___x_1919_)) as u8;
                    if v_isSharedCheck_1940_ == 0 {
                        v___x_1935_ = v___x_1919_;
                        v_isShared_1936_ = v_isSharedCheck_1940_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1933_);
                        lean_dec(v___x_1919_);
                        v___x_1935_ = lean_box(0);
                        v_isShared_1936_ = v_isSharedCheck_1940_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_1924_ = lean_ctor_get(v_a_1920_, 0);
                lean_inc(v_fst_1924_);
                lean_dec(v_a_1920_);
                if lean_obj_tag(v_fst_1924_) == 0 {
                    if v_isShared_1923_ == 0 {
                        lean_ctor_set(v___x_1922_, 0, v___x_1916_);
                        v___x_1926_ = v___x_1922_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1916_);
                        v___x_1926_ = v_reuseFailAlloc_1927_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_val_1928_ = lean_ctor_get(v_fst_1924_, 0);
                    lean_inc(v_val_1928_);
                    lean_dec_ref_known(v_fst_1924_, 1);
                    if v_isShared_1923_ == 0 {
                        lean_ctor_set(v___x_1922_, 0, v_val_1928_);
                        v___x_1930_ = v___x_1922_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_val_1928_);
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
                    v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
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
                    v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
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
    mut v_text_1957_: *mut LeanObject,
    mut v_ctx_x3f_1958_: *mut LeanObject,
    mut v_cmdStx_1959_: *mut LeanObject,
    mut v_tree_1960_: *mut LeanObject,
    mut v_requestedPos_1961_: *mut LeanObject,
    mut v_a_1962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1963_: *mut LeanObject = core::ptr::null_mut();
    v_res_1963_ = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f(
        v_text_1957_,
        v_ctx_x3f_1958_,
        v_cmdStx_1959_,
        v_tree_1960_,
        v_requestedPos_1961_,
    );
    lean_dec(v_ctx_x3f_1958_);
    return v_res_1963_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3(
    mut v_upperBound_1964_: *mut LeanObject,
    mut v_stack_1965_: *mut LeanObject,
    mut v_text_1966_: *mut LeanObject,
    mut v_ctx_x3f_1967_: *mut LeanObject,
    mut v_requestedPos_1968_: *mut LeanObject,
    mut v___x_1969_: u8,
    mut v_inst_1970_: *mut LeanObject,
    mut v_R_1971_: *mut LeanObject,
    mut v_a_1972_: *mut LeanObject,
    mut v_b_1973_: *mut LeanObject,
    mut v_c_1974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    v___x_1976_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___redArg(v_upperBound_1964_, v_stack_1965_, v_text_1966_, v_ctx_x3f_1967_, v_requestedPos_1968_, v___x_1969_, v_a_1972_, v_b_1973_);
    return v___x_1976_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3___boxed(
    mut v_upperBound_1977_: *mut LeanObject,
    mut v_stack_1978_: *mut LeanObject,
    mut v_text_1979_: *mut LeanObject,
    mut v_ctx_x3f_1980_: *mut LeanObject,
    mut v_requestedPos_1981_: *mut LeanObject,
    mut v___x_1982_: *mut LeanObject,
    mut v_inst_1983_: *mut LeanObject,
    mut v_R_1984_: *mut LeanObject,
    mut v_a_1985_: *mut LeanObject,
    mut v_b_1986_: *mut LeanObject,
    mut v_c_1987_: *mut LeanObject,
    mut v___y_1988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3606__boxed_1989_: u8 = 0;
    let mut v_res_1990_: *mut LeanObject = core::ptr::null_mut();
    v___x_3606__boxed_1989_ = (lean_unbox(v___x_1982_) as u8);
    v_res_1990_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_spec__3(v_upperBound_1977_, v_stack_1978_, v_text_1979_, v_ctx_x3f_1980_, v_requestedPos_1981_, v___x_3606__boxed_1989_, v_inst_1983_, v_R_1984_, v_a_1985_, v_b_1986_, v_c_1987_);
    lean_dec(v_requestedPos_1981_);
    lean_dec(v_ctx_x3f_1980_);
    lean_dec_ref(v_stack_1978_);
    lean_dec(v_upperBound_1977_);
    return v_res_1990_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_FileWorker_SignatureHelp(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_InfoUtils(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sort_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_FileWorker_SignatureHelp(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_FileWorker_SignatureHelp(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_InfoUtils(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_Lsp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Sort_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_PrettyPrinter_Delaborator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_FileWorker_SignatureHelp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Server_FileWorker_SignatureHelp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Server_FileWorker_SignatureHelp(builtin);
}

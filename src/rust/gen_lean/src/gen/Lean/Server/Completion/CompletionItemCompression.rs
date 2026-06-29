// Lean compiler output
// Module: Lean.Server.Completion.CompletionItemCompression
// Imports: Lean.Data.Lsp.LanguageFeatures Init.Omega
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Iterate::l_String_Slice_positions;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::r#gen::Lean::Data::Json::Printer::{
    l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux,
    l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape,
};
use crate::r#gen::Lean::Data::Lsp::LanguageFeatures::{
    initialize_Lean_Data_Lsp_LanguageFeatures, l_Lean_Lsp_CompletionItemKind_ctorIdx,
    runtime_initialize_Lean_Data_Lsp_LanguageFeatures,
};
use crate::ffi::{
    lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::ffi::lean_string_append;
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
    lean_nat_sub, lean_string_utf8_byte_size,
};
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [34, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__2_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [34, 99, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__3_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [34, 102, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__5_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [125, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__1_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [123, 34, 107, 105, 110, 100, 34, 58, 34, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__2_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [34, 44, 34, 118, 97, 108, 117, 101, 34, 58, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__3_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [112, 108, 97, 105, 110, 116, 101, 120, 116, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__4_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 97, 114, 107, 100, 111, 119, 110, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [123, 34, 99, 104, 97, 114, 97, 99, 116, 101, 114, 34, 58, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [44, 34, 108, 105, 110, 101, 34, 58, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [123, 34, 101, 110, 100, 34, 58, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__1_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [44, 34, 115, 116, 97, 114, 116, 34, 58, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [123, 34, 105, 110, 115, 101, 114, 116, 34, 58, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__1_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [44, 34, 110, 101, 119, 84, 101, 120, 116, 34, 58, 34, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__2_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [44, 34, 114, 101, 112, 108, 97, 99, 101, 34, 58, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [44, 34, 116, 97, 103, 115, 34, 58, 91, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__1_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [44, 34, 100, 97, 116, 97, 34, 58, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__2_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [44, 34, 115, 111, 114, 116, 84, 101, 120, 116, 34, 58, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__3_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [44, 34, 116, 101, 120, 116, 69, 100, 105, 116, 34, 58, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__4_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [44, 34, 107, 105, 110, 100, 34, 58, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__5_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [44, 34, 100, 111, 99, 117, 109, 101, 110, 116, 97, 116, 105, 111, 110, 34, 58, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__6_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [44, 34, 100, 101, 116, 97, 105, 108, 34, 58, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__7_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [123, 34, 108, 97, 98, 101, 108, 34, 58, 0]};
static mut l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__0_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        123, 34, 105, 115, 73, 110, 99, 111, 109, 112, 108, 101, 116, 101, 34, 58, 0,
    ],
};
static mut l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__1_value:
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
    m_data: [44, 34, 105, 116, 101, 109, 115, 34, 58, 91, 0],
};
static mut l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__2_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [93, 125, 0],
};
static mut l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__3_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [102, 97, 108, 115, 101, 0],
};
static mut l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__4_value:
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
    m_data: [116, 114, 117, 101, 0],
};
static mut l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0(
    mut v___x_976_: *mut crate::leanh::LeanObject,
    mut v___x_977_: *mut crate::leanh::LeanObject,
    mut v_it_978_: *mut crate::leanh::LeanObject,
    mut v_acc_979_: *mut crate::leanh::LeanObject,
    mut v_hP_980_: *mut crate::leanh::LeanObject,
    mut v_recur_981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_982_: u8 = 0;
    v___x_982_ = lean_nat_dec_eq(v_it_978_, v___x_976_);
    if v___x_982_ == 0 {
        let mut v___x_983_: u32 = 0;
        let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_983_ = lean_string_utf8_get_fast(v___x_977_, v_it_978_);
        v___x_984_ = lean_string_utf8_next_fast(v___x_977_, v_it_978_);
        v___x_985_ =
            l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_acc_979_, v___x_983_);
        v___x_986_ = crate::leanh::lean_apply_4(
            v_recur_981_,
            v___x_984_,
            v___x_985_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_986_;
    } else {
        crate::leanh::lean_dec_ref(v_recur_981_);
        return v_acc_979_;
    }
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0___boxed(
    mut v___x_987_: *mut crate::leanh::LeanObject,
    mut v___x_988_: *mut crate::leanh::LeanObject,
    mut v_it_989_: *mut crate::leanh::LeanObject,
    mut v_acc_990_: *mut crate::leanh::LeanObject,
    mut v_hP_991_: *mut crate::leanh::LeanObject,
    mut v_recur_992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_993_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0(v___x_987_, v___x_988_, v_it_989_, v_acc_990_, v_hP_991_, v_recur_992_);
    crate::leanh::lean_dec(v_it_989_);
    crate::leanh::lean_dec_ref(v___x_988_);
    crate::leanh::lean_dec(v___x_987_);
    return v_res_993_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__2(
    mut v___x_994_: *mut crate::leanh::LeanObject,
    mut v_uri_995_: *mut crate::leanh::LeanObject,
    mut v_it_996_: *mut crate::leanh::LeanObject,
    mut v_acc_997_: *mut crate::leanh::LeanObject,
    mut v_hP_998_: *mut crate::leanh::LeanObject,
    mut v_recur_999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1000_: u8 = 0;
    v___x_1000_ = lean_nat_dec_eq(v_it_996_, v___x_994_);
    if v___x_1000_ == 0 {
        let mut v___x_1001_: u32 = 0;
        let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1001_ = lean_string_utf8_get_fast(v_uri_995_, v_it_996_);
        v___x_1002_ = lean_string_utf8_next_fast(v_uri_995_, v_it_996_);
        v___x_1003_ =
            l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_acc_997_, v___x_1001_);
        v___x_1004_ = crate::leanh::lean_apply_4(
            v_recur_999_,
            v___x_1002_,
            v___x_1003_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_1004_;
    } else {
        crate::leanh::lean_dec_ref(v_recur_999_);
        return v_acc_997_;
    }
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__2___boxed(
    mut v___x_1005_: *mut crate::leanh::LeanObject,
    mut v_uri_1006_: *mut crate::leanh::LeanObject,
    mut v_it_1007_: *mut crate::leanh::LeanObject,
    mut v_acc_1008_: *mut crate::leanh::LeanObject,
    mut v_hP_1009_: *mut crate::leanh::LeanObject,
    mut v_recur_1010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1011_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__2(v___x_1005_, v_uri_1006_, v_it_1007_, v_acc_1008_, v_hP_1009_, v_recur_1010_);
    crate::leanh::lean_dec(v_it_1007_);
    crate::leanh::lean_dec_ref(v_uri_1006_);
    crate::leanh::lean_dec(v___x_1005_);
    return v_res_1011_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast(
    mut v_acc_1018_: *mut crate::leanh::LeanObject,
    mut v_data_1019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_acc_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uri_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cPos_x3f_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_x3f_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: u8 = 0;
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: u8 = 0;
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: u8 = 0;
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: u8 = 0;
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: u8 = 0;
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_uri_1032_ = crate::leanh::lean_ctor_get(v_data_1019_, 0);
                crate::leanh::lean_inc_ref(v_uri_1032_);
                v_pos_1033_ = crate::leanh::lean_ctor_get(v_data_1019_, 1);
                crate::leanh::lean_inc_ref(v_pos_1033_);
                v_cPos_x3f_1034_ = crate::leanh::lean_ctor_get(v_data_1019_, 2);
                crate::leanh::lean_inc(v_cPos_x3f_1034_);
                v_id_x3f_1035_ = crate::leanh::lean_ctor_get(v_data_1019_, 3);
                crate::leanh::lean_inc(v_id_x3f_1035_);
                crate::leanh::lean_dec_ref(v_data_1019_);
                v___x_1082_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__5;
                v_acc_1083_ = lean_string_append(v_acc_1018_, v___x_1082_);
                v___x_1084_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1;
                v_acc_1085_ = lean_string_append(v_acc_1083_, v___x_1084_);
                v___x_1086_ =
                    l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_uri_1032_);
                if v___x_1086_ == 0 {
                    v___x_1087_ = lean_string_append(v_acc_1085_, v_uri_1032_);
                    crate::leanh::lean_dec_ref(v_uri_1032_);
                    v___x_1088_ = lean_string_append(v___x_1087_, v___x_1084_);
                    v___y_1068_ = v___x_1088_;
                    state = 5;
                    continue;
                } else {
                    v___x_1089_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1090_ = lean_string_utf8_byte_size(v_uri_1032_);
                    crate::leanh::lean_inc_ref(v_uri_1032_);
                    v___f_1091_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__2___boxed as *mut core::ffi::c_void, 6, 2);
                    crate::leanh::lean_closure_set(v___f_1091_, 0, v___x_1090_);
                    crate::leanh::lean_closure_set(v___f_1091_, 1, v_uri_1032_);
                    v___x_1092_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1092_, 0, v_uri_1032_);
                    crate::leanh::lean_ctor_set(v___x_1092_, 1, v___x_1089_);
                    crate::leanh::lean_ctor_set(v___x_1092_, 2, v___x_1090_);
                    v___x_1093_ = l_String_Slice_positions(v___x_1092_);
                    crate::leanh::lean_dec_ref_known(v___x_1092_, 3);
                    v___x_1094_ = l_WellFounded_opaqueFix_u2083___redArg(
                        v___f_1091_,
                        v___x_1093_,
                        v_acc_1085_,
                        crate::leanh::lean_box(0),
                    );
                    v___x_1095_ = lean_string_append(v___x_1094_, v___x_1084_);
                    v___y_1068_ = v___x_1095_;
                    state = 5;
                    continue;
                }
            }
            1 => {
                v___x_1022_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0;
                v___x_1023_ = lean_string_append(v_acc_1021_, v___x_1022_);
                return v___x_1023_;
            }
            2 => {
                v___x_1026_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1;
                v_acc_1027_ = lean_string_append(v___y_1025_, v___x_1026_);
                v_acc_1021_ = v_acc_1027_;
                state = 1;
                continue;
            }
            3 => {
                v___x_1030_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1;
                v_acc_1031_ = lean_string_append(v___y_1029_, v___x_1030_);
                v_acc_1021_ = v_acc_1031_;
                state = 1;
                continue;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_id_x3f_1035_) == 1 {
                    v_val_1039_ = crate::leanh::lean_ctor_get(v_id_x3f_1035_, 0);
                    crate::leanh::lean_inc(v_val_1039_);
                    crate::leanh::lean_dec_ref_known(v_id_x3f_1035_, 1);
                    v_acc_1040_ = lean_string_append(v_acc_1038_, v___y_1037_);
                    if crate::leanh::lean_obj_tag(v_val_1039_) == 0 {
                        v_declName_1041_ = crate::leanh::lean_ctor_get(v_val_1039_, 0);
                        crate::leanh::lean_inc(v_declName_1041_);
                        crate::leanh::lean_dec_ref_known(v_val_1039_, 1);
                        v___x_1042_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__2;
                        v_acc_1043_ = lean_string_append(v_acc_1040_, v___x_1042_);
                        v___x_1044_ = 1;
                        v___x_1045_ = l_Lean_Name_toString(v_declName_1041_, v___x_1044_);
                        v___x_1046_ =
                            l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v___x_1045_);
                        if v___x_1046_ == 0 {
                            v___x_1047_ = lean_string_append(v_acc_1043_, v___x_1045_);
                            crate::leanh::lean_dec_ref(v___x_1045_);
                            v___y_1025_ = v___x_1047_;
                            state = 2;
                            continue;
                        } else {
                            v___x_1048_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_1049_ = lean_string_utf8_byte_size(v___x_1045_);
                            crate::leanh::lean_inc_ref(v___x_1045_);
                            v___f_1050_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0___boxed as *mut core::ffi::c_void, 6, 2);
                            crate::leanh::lean_closure_set(v___f_1050_, 0, v___x_1049_);
                            crate::leanh::lean_closure_set(v___f_1050_, 1, v___x_1045_);
                            v___x_1051_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1051_, 0, v___x_1045_);
                            crate::leanh::lean_ctor_set(v___x_1051_, 1, v___x_1048_);
                            crate::leanh::lean_ctor_set(v___x_1051_, 2, v___x_1049_);
                            v___x_1052_ = l_String_Slice_positions(v___x_1051_);
                            crate::leanh::lean_dec_ref_known(v___x_1051_, 3);
                            v___x_1053_ = l_WellFounded_opaqueFix_u2083___redArg(
                                v___f_1050_,
                                v___x_1052_,
                                v_acc_1043_,
                                crate::leanh::lean_box(0),
                            );
                            v___y_1025_ = v___x_1053_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_id_1054_ = crate::leanh::lean_ctor_get(v_val_1039_, 0);
                        crate::leanh::lean_inc(v_id_1054_);
                        crate::leanh::lean_dec_ref_known(v_val_1039_, 1);
                        v___x_1055_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__3;
                        v_acc_1056_ = lean_string_append(v_acc_1040_, v___x_1055_);
                        v___x_1057_ = 1;
                        v___x_1058_ = l_Lean_Name_toString(v_id_1054_, v___x_1057_);
                        v___x_1059_ =
                            l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v___x_1058_);
                        if v___x_1059_ == 0 {
                            v___x_1060_ = lean_string_append(v_acc_1056_, v___x_1058_);
                            crate::leanh::lean_dec_ref(v___x_1058_);
                            v___y_1029_ = v___x_1060_;
                            state = 3;
                            continue;
                        } else {
                            v___x_1061_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_1062_ = lean_string_utf8_byte_size(v___x_1058_);
                            crate::leanh::lean_inc_ref(v___x_1058_);
                            v___f_1063_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0___boxed as *mut core::ffi::c_void, 6, 2);
                            crate::leanh::lean_closure_set(v___f_1063_, 0, v___x_1062_);
                            crate::leanh::lean_closure_set(v___f_1063_, 1, v___x_1058_);
                            v___x_1064_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1064_, 0, v___x_1058_);
                            crate::leanh::lean_ctor_set(v___x_1064_, 1, v___x_1061_);
                            crate::leanh::lean_ctor_set(v___x_1064_, 2, v___x_1062_);
                            v___x_1065_ = l_String_Slice_positions(v___x_1064_);
                            crate::leanh::lean_dec_ref_known(v___x_1064_, 3);
                            v___x_1066_ = l_WellFounded_opaqueFix_u2083___redArg(
                                v___f_1063_,
                                v___x_1065_,
                                v_acc_1056_,
                                crate::leanh::lean_box(0),
                            );
                            v___y_1029_ = v___x_1066_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_id_x3f_1035_);
                    v_acc_1021_ = v_acc_1038_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                v_line_1069_ = crate::leanh::lean_ctor_get(v_pos_1033_, 0);
                crate::leanh::lean_inc(v_line_1069_);
                v_character_1070_ = crate::leanh::lean_ctor_get(v_pos_1033_, 1);
                crate::leanh::lean_inc(v_character_1070_);
                crate::leanh::lean_dec_ref(v_pos_1033_);
                v___x_1071_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4;
                v___x_1072_ = lean_string_append(v___y_1068_, v___x_1071_);
                v___x_1073_ = l_Nat_reprFast(v_line_1069_);
                v_acc_1074_ = lean_string_append(v___x_1072_, v___x_1073_);
                crate::leanh::lean_dec_ref(v___x_1073_);
                v___x_1075_ = lean_string_append(v_acc_1074_, v___x_1071_);
                v___x_1076_ = l_Nat_reprFast(v_character_1070_);
                v_acc_1077_ = lean_string_append(v___x_1075_, v___x_1076_);
                crate::leanh::lean_dec_ref(v___x_1076_);
                if crate::leanh::lean_obj_tag(v_cPos_x3f_1034_) == 1 {
                    v_val_1078_ = crate::leanh::lean_ctor_get(v_cPos_x3f_1034_, 0);
                    crate::leanh::lean_inc(v_val_1078_);
                    crate::leanh::lean_dec_ref_known(v_cPos_x3f_1034_, 1);
                    v___x_1079_ = lean_string_append(v_acc_1077_, v___x_1071_);
                    v___x_1080_ = l_Nat_reprFast(v_val_1078_);
                    v_acc_1081_ = lean_string_append(v___x_1079_, v___x_1080_);
                    crate::leanh::lean_dec_ref(v___x_1080_);
                    v___y_1037_ = v___x_1071_;
                    v_acc_1038_ = v_acc_1081_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_cPos_x3f_1034_);
                    v___y_1037_ = v___x_1071_;
                    v_acc_1038_ = v_acc_1077_;
                    state = 4;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___lam__0(
    mut v___x_1096_: *mut crate::leanh::LeanObject,
    mut v_value_1097_: *mut crate::leanh::LeanObject,
    mut v_it_1098_: *mut crate::leanh::LeanObject,
    mut v_acc_1099_: *mut crate::leanh::LeanObject,
    mut v_hP_1100_: *mut crate::leanh::LeanObject,
    mut v_recur_1101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1102_: u8 = 0;
    v___x_1102_ = lean_nat_dec_eq(v_it_1098_, v___x_1096_);
    if v___x_1102_ == 0 {
        let mut v___x_1103_: u32 = 0;
        let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1103_ = lean_string_utf8_get_fast(v_value_1097_, v_it_1098_);
        v___x_1104_ = lean_string_utf8_next_fast(v_value_1097_, v_it_1098_);
        v___x_1105_ =
            l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_acc_1099_, v___x_1103_);
        v___x_1106_ = crate::leanh::lean_apply_4(
            v_recur_1101_,
            v___x_1104_,
            v___x_1105_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_1106_;
    } else {
        crate::leanh::lean_dec_ref(v_recur_1101_);
        return v_acc_1099_;
    }
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___lam__0___boxed(
    mut v___x_1107_: *mut crate::leanh::LeanObject,
    mut v_value_1108_: *mut crate::leanh::LeanObject,
    mut v_it_1109_: *mut crate::leanh::LeanObject,
    mut v_acc_1110_: *mut crate::leanh::LeanObject,
    mut v_hP_1111_: *mut crate::leanh::LeanObject,
    mut v_recur_1112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1113_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___lam__0(v___x_1107_, v_value_1108_, v_it_1109_, v_acc_1110_, v_hP_1111_, v_recur_1112_);
    crate::leanh::lean_dec(v_it_1109_);
    crate::leanh::lean_dec_ref(v_value_1108_);
    crate::leanh::lean_dec(v___x_1107_);
    return v_res_1113_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast(
    mut v_acc_1119_: *mut crate::leanh::LeanObject,
    mut v_c_1120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1125_: u8 = 0;
    let mut v_value_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: u8 = 0;
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_kind_1125_ = crate::leanh::lean_ctor_get_uint8(
                    v_c_1120_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_value_1126_ = crate::leanh::lean_ctor_get(v_c_1120_, 0);
                crate::leanh::lean_inc_ref(v_value_1126_);
                crate::leanh::lean_dec_ref(v_c_1120_);
                if v_kind_1125_ == 0 {
                    v___x_1146_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__3;
                    v___y_1128_ = v___x_1146_;
                    state = 2;
                    continue;
                } else {
                    v___x_1147_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__4;
                    v___y_1128_ = v___x_1147_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1123_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0;
                v___x_1124_ = lean_string_append(v___y_1122_, v___x_1123_);
                return v___x_1124_;
            }
            2 => {
                v___x_1129_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__1;
                v___x_1130_ = lean_string_append(v_acc_1119_, v___x_1129_);
                v___x_1131_ = lean_string_append(v___x_1130_, v___y_1128_);
                v___x_1132_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__2;
                v_acc_1133_ = lean_string_append(v___x_1131_, v___x_1132_);
                v___x_1134_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1;
                v_acc_1135_ = lean_string_append(v_acc_1133_, v___x_1134_);
                v___x_1136_ =
                    l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_value_1126_);
                if v___x_1136_ == 0 {
                    v___x_1137_ = lean_string_append(v_acc_1135_, v_value_1126_);
                    crate::leanh::lean_dec_ref(v_value_1126_);
                    v___x_1138_ = lean_string_append(v___x_1137_, v___x_1134_);
                    v___y_1122_ = v___x_1138_;
                    state = 1;
                    continue;
                } else {
                    v___x_1139_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1140_ = lean_string_utf8_byte_size(v_value_1126_);
                    crate::leanh::lean_inc_ref(v_value_1126_);
                    v___f_1141_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___lam__0___boxed as *mut core::ffi::c_void, 6, 2);
                    crate::leanh::lean_closure_set(v___f_1141_, 0, v___x_1140_);
                    crate::leanh::lean_closure_set(v___f_1141_, 1, v_value_1126_);
                    v___x_1142_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1142_, 0, v_value_1126_);
                    crate::leanh::lean_ctor_set(v___x_1142_, 1, v___x_1139_);
                    crate::leanh::lean_ctor_set(v___x_1142_, 2, v___x_1140_);
                    v___x_1143_ = l_String_Slice_positions(v___x_1142_);
                    crate::leanh::lean_dec_ref_known(v___x_1142_, 3);
                    v___x_1144_ = l_WellFounded_opaqueFix_u2083___redArg(
                        v___f_1141_,
                        v___x_1143_,
                        v_acc_1135_,
                        crate::leanh::lean_box(0),
                    );
                    v___x_1145_ = lean_string_append(v___x_1144_, v___x_1134_);
                    v___y_1122_ = v___x_1145_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast(
    mut v_acc_1150_: *mut crate::leanh::LeanObject,
    mut v_p_1151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_line_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_line_1152_ = crate::leanh::lean_ctor_get(v_p_1151_, 0);
    crate::leanh::lean_inc(v_line_1152_);
    v_character_1153_ = crate::leanh::lean_ctor_get(v_p_1151_, 1);
    crate::leanh::lean_inc(v_character_1153_);
    crate::leanh::lean_dec_ref(v_p_1151_);
    v___x_1154_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0;
    v___x_1155_ = lean_string_append(v_acc_1150_, v___x_1154_);
    v___x_1156_ = l_Nat_reprFast(v_character_1153_);
    v___x_1157_ = lean_string_append(v___x_1155_, v___x_1156_);
    crate::leanh::lean_dec_ref(v___x_1156_);
    v___x_1158_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1;
    v___x_1159_ = lean_string_append(v___x_1157_, v___x_1158_);
    v___x_1160_ = l_Nat_reprFast(v_line_1152_);
    v___x_1161_ = lean_string_append(v___x_1159_, v___x_1160_);
    crate::leanh::lean_dec_ref(v___x_1160_);
    v___x_1162_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0;
    v___x_1163_ = lean_string_append(v___x_1161_, v___x_1162_);
    return v___x_1163_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast(
    mut v_acc_1166_: *mut crate::leanh::LeanObject,
    mut v_range_1167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_end_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_end_1168_ = crate::leanh::lean_ctor_get(v_range_1167_, 1);
    crate::leanh::lean_inc_ref(v_end_1168_);
    v_start_1169_ = crate::leanh::lean_ctor_get(v_range_1167_, 0);
    crate::leanh::lean_inc_ref(v_start_1169_);
    crate::leanh::lean_dec_ref(v_range_1167_);
    v_line_1170_ = crate::leanh::lean_ctor_get(v_end_1168_, 0);
    crate::leanh::lean_inc(v_line_1170_);
    v_character_1171_ = crate::leanh::lean_ctor_get(v_end_1168_, 1);
    crate::leanh::lean_inc(v_character_1171_);
    crate::leanh::lean_dec_ref(v_end_1168_);
    v_line_1172_ = crate::leanh::lean_ctor_get(v_start_1169_, 0);
    crate::leanh::lean_inc(v_line_1172_);
    v_character_1173_ = crate::leanh::lean_ctor_get(v_start_1169_, 1);
    crate::leanh::lean_inc(v_character_1173_);
    crate::leanh::lean_dec_ref(v_start_1169_);
    v___x_1174_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__0;
    v_acc_1175_ = lean_string_append(v_acc_1166_, v___x_1174_);
    v___x_1176_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0;
    v___x_1177_ = lean_string_append(v_acc_1175_, v___x_1176_);
    v___x_1178_ = l_Nat_reprFast(v_character_1171_);
    v___x_1179_ = lean_string_append(v___x_1177_, v___x_1178_);
    crate::leanh::lean_dec_ref(v___x_1178_);
    v___x_1180_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1;
    v___x_1181_ = lean_string_append(v___x_1179_, v___x_1180_);
    v___x_1182_ = l_Nat_reprFast(v_line_1170_);
    v___x_1183_ = lean_string_append(v___x_1181_, v___x_1182_);
    crate::leanh::lean_dec_ref(v___x_1182_);
    v___x_1184_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0;
    v_acc_1185_ = lean_string_append(v___x_1183_, v___x_1184_);
    v___x_1186_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__1;
    v_acc_1187_ = lean_string_append(v_acc_1185_, v___x_1186_);
    v___x_1188_ = lean_string_append(v_acc_1187_, v___x_1176_);
    v___x_1189_ = l_Nat_reprFast(v_character_1173_);
    v___x_1190_ = lean_string_append(v___x_1188_, v___x_1189_);
    crate::leanh::lean_dec_ref(v___x_1189_);
    v___x_1191_ = lean_string_append(v___x_1190_, v___x_1180_);
    v___x_1192_ = l_Nat_reprFast(v_line_1172_);
    v___x_1193_ = lean_string_append(v___x_1191_, v___x_1192_);
    crate::leanh::lean_dec_ref(v___x_1192_);
    v_acc_1194_ = lean_string_append(v___x_1193_, v___x_1184_);
    v___x_1195_ = lean_string_append(v_acc_1194_, v___x_1184_);
    return v___x_1195_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast(
    mut v_acc_1199_: *mut crate::leanh::LeanObject,
    mut v_edit_1200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_insert_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_end_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_replace_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_end_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newText_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_insert_1201_ = crate::leanh::lean_ctor_get(v_edit_1200_, 1);
    v_end_1202_ = crate::leanh::lean_ctor_get(v_insert_1201_, 1);
    crate::leanh::lean_inc_ref(v_end_1202_);
    v_start_1203_ = crate::leanh::lean_ctor_get(v_insert_1201_, 0);
    crate::leanh::lean_inc_ref(v_start_1203_);
    v_replace_1204_ = crate::leanh::lean_ctor_get(v_edit_1200_, 2);
    v_end_1205_ = crate::leanh::lean_ctor_get(v_replace_1204_, 1);
    crate::leanh::lean_inc_ref(v_end_1205_);
    v_start_1206_ = crate::leanh::lean_ctor_get(v_replace_1204_, 0);
    crate::leanh::lean_inc_ref(v_start_1206_);
    v_newText_1207_ = crate::leanh::lean_ctor_get(v_edit_1200_, 0);
    crate::leanh::lean_inc_ref(v_newText_1207_);
    crate::leanh::lean_dec_ref(v_edit_1200_);
    v_line_1208_ = crate::leanh::lean_ctor_get(v_end_1202_, 0);
    crate::leanh::lean_inc(v_line_1208_);
    v_character_1209_ = crate::leanh::lean_ctor_get(v_end_1202_, 1);
    crate::leanh::lean_inc(v_character_1209_);
    crate::leanh::lean_dec_ref(v_end_1202_);
    v_line_1210_ = crate::leanh::lean_ctor_get(v_start_1203_, 0);
    crate::leanh::lean_inc(v_line_1210_);
    v_character_1211_ = crate::leanh::lean_ctor_get(v_start_1203_, 1);
    crate::leanh::lean_inc(v_character_1211_);
    crate::leanh::lean_dec_ref(v_start_1203_);
    v_line_1212_ = crate::leanh::lean_ctor_get(v_end_1205_, 0);
    crate::leanh::lean_inc(v_line_1212_);
    v_character_1213_ = crate::leanh::lean_ctor_get(v_end_1205_, 1);
    crate::leanh::lean_inc(v_character_1213_);
    crate::leanh::lean_dec_ref(v_end_1205_);
    v_line_1214_ = crate::leanh::lean_ctor_get(v_start_1206_, 0);
    crate::leanh::lean_inc(v_line_1214_);
    v_character_1215_ = crate::leanh::lean_ctor_get(v_start_1206_, 1);
    crate::leanh::lean_inc(v_character_1215_);
    crate::leanh::lean_dec_ref(v_start_1206_);
    v___x_1216_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__0;
    v_acc_1217_ = lean_string_append(v_acc_1199_, v___x_1216_);
    v___x_1218_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__0;
    v_acc_1219_ = lean_string_append(v_acc_1217_, v___x_1218_);
    v___x_1220_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0;
    v___x_1221_ = lean_string_append(v_acc_1219_, v___x_1220_);
    v___x_1222_ = l_Nat_reprFast(v_character_1209_);
    v___x_1223_ = lean_string_append(v___x_1221_, v___x_1222_);
    crate::leanh::lean_dec_ref(v___x_1222_);
    v___x_1224_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1;
    v___x_1225_ = lean_string_append(v___x_1223_, v___x_1224_);
    v___x_1226_ = l_Nat_reprFast(v_line_1208_);
    v___x_1227_ = lean_string_append(v___x_1225_, v___x_1226_);
    crate::leanh::lean_dec_ref(v___x_1226_);
    v___x_1228_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0;
    v_acc_1229_ = lean_string_append(v___x_1227_, v___x_1228_);
    v___x_1230_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__1;
    v_acc_1231_ = lean_string_append(v_acc_1229_, v___x_1230_);
    v___x_1232_ = lean_string_append(v_acc_1231_, v___x_1220_);
    v___x_1233_ = l_Nat_reprFast(v_character_1211_);
    v___x_1234_ = lean_string_append(v___x_1232_, v___x_1233_);
    crate::leanh::lean_dec_ref(v___x_1233_);
    v___x_1235_ = lean_string_append(v___x_1234_, v___x_1224_);
    v___x_1236_ = l_Nat_reprFast(v_line_1210_);
    v___x_1237_ = lean_string_append(v___x_1235_, v___x_1236_);
    crate::leanh::lean_dec_ref(v___x_1236_);
    v_acc_1238_ = lean_string_append(v___x_1237_, v___x_1228_);
    v_acc_1239_ = lean_string_append(v_acc_1238_, v___x_1228_);
    v___x_1240_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__1;
    v___x_1241_ = lean_string_append(v_acc_1239_, v___x_1240_);
    v___x_1242_ = lean_string_append(v___x_1241_, v_newText_1207_);
    crate::leanh::lean_dec_ref(v_newText_1207_);
    v___x_1243_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1;
    v_acc_1244_ = lean_string_append(v___x_1242_, v___x_1243_);
    v___x_1245_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__2;
    v_acc_1246_ = lean_string_append(v_acc_1244_, v___x_1245_);
    v_acc_1247_ = lean_string_append(v_acc_1246_, v___x_1218_);
    v___x_1248_ = lean_string_append(v_acc_1247_, v___x_1220_);
    v___x_1249_ = l_Nat_reprFast(v_character_1213_);
    v___x_1250_ = lean_string_append(v___x_1248_, v___x_1249_);
    crate::leanh::lean_dec_ref(v___x_1249_);
    v___x_1251_ = lean_string_append(v___x_1250_, v___x_1224_);
    v___x_1252_ = l_Nat_reprFast(v_line_1212_);
    v___x_1253_ = lean_string_append(v___x_1251_, v___x_1252_);
    crate::leanh::lean_dec_ref(v___x_1252_);
    v_acc_1254_ = lean_string_append(v___x_1253_, v___x_1228_);
    v_acc_1255_ = lean_string_append(v_acc_1254_, v___x_1230_);
    v___x_1256_ = lean_string_append(v_acc_1255_, v___x_1220_);
    v___x_1257_ = l_Nat_reprFast(v_character_1215_);
    v___x_1258_ = lean_string_append(v___x_1256_, v___x_1257_);
    crate::leanh::lean_dec_ref(v___x_1257_);
    v___x_1259_ = lean_string_append(v___x_1258_, v___x_1224_);
    v___x_1260_ = l_Nat_reprFast(v_line_1214_);
    v___x_1261_ = lean_string_append(v___x_1259_, v___x_1260_);
    crate::leanh::lean_dec_ref(v___x_1260_);
    v_acc_1262_ = lean_string_append(v___x_1261_, v___x_1228_);
    v_acc_1263_ = lean_string_append(v_acc_1262_, v___x_1228_);
    v___x_1264_ = lean_string_append(v_acc_1263_, v___x_1228_);
    return v___x_1264_;
}
pub unsafe fn _init_l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1265_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1266_ = l_Nat_reprFast(v___x_1265_);
    return v___x_1266_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast(
    mut v_acc_1267_: *mut crate::leanh::LeanObject,
    mut v_tags_1268_: *mut crate::leanh::LeanObject,
    mut v_i_1269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: u8 = 0;
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: u8 = 0;
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1270_ = lean_array_get_size(v_tags_1268_);
                v___x_1271_ = lean_nat_dec_lt(v_i_1269_, v___x_1270_);
                if v___x_1271_ == 0 {
                    crate::leanh::lean_dec(v_i_1269_);
                    return v_acc_1267_;
                } else {
                    v___x_1272_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1277_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0_once), _init_l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0);
                    v_acc_1278_ = lean_string_append(v_acc_1267_, v___x_1277_);
                    v___x_1279_ = lean_nat_sub(v___x_1270_, v___x_1272_);
                    v___x_1280_ = lean_nat_dec_lt(v_i_1269_, v___x_1279_);
                    crate::leanh::lean_dec(v___x_1279_);
                    if v___x_1280_ == 0 {
                        v___y_1274_ = v_acc_1278_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1281_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4;
                        v___x_1282_ = lean_string_append(v_acc_1278_, v___x_1281_);
                        v___y_1274_ = v___x_1282_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1275_ = lean_nat_add(v_i_1269_, v___x_1272_);
                crate::leanh::lean_dec(v_i_1269_);
                v_acc_1267_ = v___y_1274_;
                v_i_1269_ = v___x_1275_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___boxed(
    mut v_acc_1283_: *mut crate::leanh::LeanObject,
    mut v_tags_1284_: *mut crate::leanh::LeanObject,
    mut v_i_1285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1286_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast(v_acc_1283_, v_tags_1284_, v_i_1285_);
    crate::leanh::lean_dec_ref(v_tags_1284_);
    return v_res_1286_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3(
    mut v___x_1287_: *mut crate::leanh::LeanObject,
    mut v_val_1288_: *mut crate::leanh::LeanObject,
    mut v_it_1289_: *mut crate::leanh::LeanObject,
    mut v_acc_1290_: *mut crate::leanh::LeanObject,
    mut v_hP_1291_: *mut crate::leanh::LeanObject,
    mut v_recur_1292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1293_: u8 = 0;
    v___x_1293_ = lean_nat_dec_eq(v_it_1289_, v___x_1287_);
    if v___x_1293_ == 0 {
        let mut v___x_1294_: u32 = 0;
        let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1294_ = lean_string_utf8_get_fast(v_val_1288_, v_it_1289_);
        v___x_1295_ = lean_string_utf8_next_fast(v_val_1288_, v_it_1289_);
        v___x_1296_ =
            l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_acc_1290_, v___x_1294_);
        v___x_1297_ = crate::leanh::lean_apply_4(
            v_recur_1292_,
            v___x_1295_,
            v___x_1296_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_1297_;
    } else {
        crate::leanh::lean_dec_ref(v_recur_1292_);
        return v_acc_1290_;
    }
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3___boxed(
    mut v___x_1298_: *mut crate::leanh::LeanObject,
    mut v_val_1299_: *mut crate::leanh::LeanObject,
    mut v_it_1300_: *mut crate::leanh::LeanObject,
    mut v_acc_1301_: *mut crate::leanh::LeanObject,
    mut v_hP_1302_: *mut crate::leanh::LeanObject,
    mut v_recur_1303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1304_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3(v___x_1298_, v_val_1299_, v_it_1300_, v_acc_1301_, v_hP_1302_, v_recur_1303_);
    crate::leanh::lean_dec(v_it_1300_);
    crate::leanh::lean_dec_ref(v_val_1299_);
    crate::leanh::lean_dec(v___x_1298_);
    return v_res_1304_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__2(
    mut v___x_1305_: *mut crate::leanh::LeanObject,
    mut v_label_1306_: *mut crate::leanh::LeanObject,
    mut v_it_1307_: *mut crate::leanh::LeanObject,
    mut v_acc_1308_: *mut crate::leanh::LeanObject,
    mut v_hP_1309_: *mut crate::leanh::LeanObject,
    mut v_recur_1310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1311_: u8 = 0;
    v___x_1311_ = lean_nat_dec_eq(v_it_1307_, v___x_1305_);
    if v___x_1311_ == 0 {
        let mut v___x_1312_: u32 = 0;
        let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1312_ = lean_string_utf8_get_fast(v_label_1306_, v_it_1307_);
        v___x_1313_ = lean_string_utf8_next_fast(v_label_1306_, v_it_1307_);
        v___x_1314_ =
            l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_acc_1308_, v___x_1312_);
        v___x_1315_ = crate::leanh::lean_apply_4(
            v_recur_1310_,
            v___x_1313_,
            v___x_1314_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_1315_;
    } else {
        crate::leanh::lean_dec_ref(v_recur_1310_);
        return v_acc_1308_;
    }
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__2___boxed(
    mut v___x_1316_: *mut crate::leanh::LeanObject,
    mut v_label_1317_: *mut crate::leanh::LeanObject,
    mut v_it_1318_: *mut crate::leanh::LeanObject,
    mut v_acc_1319_: *mut crate::leanh::LeanObject,
    mut v_hP_1320_: *mut crate::leanh::LeanObject,
    mut v_recur_1321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1322_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__2(v___x_1316_, v_label_1317_, v_it_1318_, v_acc_1319_, v_hP_1320_, v_recur_1321_);
    crate::leanh::lean_dec(v_it_1318_);
    crate::leanh::lean_dec_ref(v_label_1317_);
    crate::leanh::lean_dec(v___x_1316_);
    return v_res_1322_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast(
    mut v_acc_1331_: *mut crate::leanh::LeanObject,
    mut v_item_1332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_acc_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_label_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_detail_x3f_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_documentation_x3f_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_x3f_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_textEdit_x3f_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sortText_x3f_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tags_x3f_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: u8 = 0;
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: u8 = 0;
    let mut v_acc_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_x3f_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: u8 = 0;
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: u8 = 0;
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: u8 = 0;
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: u8 = 0;
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cPos_x3f_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_x3f_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uri_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cPos_x3f_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_x3f_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: u8 = 0;
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: u8 = 0;
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_insert_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_end_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_replace_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_end_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newText_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: u8 = 0;
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: u8 = 0;
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1572_: u8 = 0;
    let mut v_value_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: u8 = 0;
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: u8 = 0;
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_label_1341_ = crate::leanh::lean_ctor_get(v_item_1332_, 0);
                crate::leanh::lean_inc_ref(v_label_1341_);
                v_detail_x3f_1342_ = crate::leanh::lean_ctor_get(v_item_1332_, 1);
                crate::leanh::lean_inc(v_detail_x3f_1342_);
                v_documentation_x3f_1343_ = crate::leanh::lean_ctor_get(v_item_1332_, 2);
                crate::leanh::lean_inc(v_documentation_x3f_1343_);
                v_kind_x3f_1344_ = crate::leanh::lean_ctor_get(v_item_1332_, 3);
                crate::leanh::lean_inc(v_kind_x3f_1344_);
                v_textEdit_x3f_1345_ = crate::leanh::lean_ctor_get(v_item_1332_, 4);
                crate::leanh::lean_inc(v_textEdit_x3f_1345_);
                v_sortText_x3f_1346_ = crate::leanh::lean_ctor_get(v_item_1332_, 5);
                crate::leanh::lean_inc(v_sortText_x3f_1346_);
                v_data_x3f_1347_ = crate::leanh::lean_ctor_get(v_item_1332_, 6);
                crate::leanh::lean_inc(v_data_x3f_1347_);
                v_tags_x3f_1348_ = crate::leanh::lean_ctor_get(v_item_1332_, 7);
                crate::leanh::lean_inc(v_tags_x3f_1348_);
                crate::leanh::lean_dec_ref(v_item_1332_);
                v___x_1595_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__7;
                v_acc_1596_ = lean_string_append(v_acc_1331_, v___x_1595_);
                v___x_1597_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1;
                v_acc_1598_ = lean_string_append(v_acc_1596_, v___x_1597_);
                v___x_1599_ =
                    l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_label_1341_);
                if v___x_1599_ == 0 {
                    v___x_1600_ = lean_string_append(v_acc_1598_, v_label_1341_);
                    crate::leanh::lean_dec_ref(v_label_1341_);
                    v___x_1601_ = lean_string_append(v___x_1600_, v___x_1597_);
                    v___y_1579_ = v___x_1601_;
                    state = 16;
                    continue;
                } else {
                    v___x_1602_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1603_ = lean_string_utf8_byte_size(v_label_1341_);
                    crate::leanh::lean_inc_ref(v_label_1341_);
                    v___f_1604_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__2___boxed as *mut core::ffi::c_void, 6, 2);
                    crate::leanh::lean_closure_set(v___f_1604_, 0, v___x_1603_);
                    crate::leanh::lean_closure_set(v___f_1604_, 1, v_label_1341_);
                    v___x_1605_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1605_, 0, v_label_1341_);
                    crate::leanh::lean_ctor_set(v___x_1605_, 1, v___x_1602_);
                    crate::leanh::lean_ctor_set(v___x_1605_, 2, v___x_1603_);
                    v___x_1606_ = l_String_Slice_positions(v___x_1605_);
                    crate::leanh::lean_dec_ref_known(v___x_1605_, 3);
                    v___x_1607_ = l_WellFounded_opaqueFix_u2083___redArg(
                        v___f_1604_,
                        v___x_1606_,
                        v_acc_1598_,
                        crate::leanh::lean_box(0),
                    );
                    v___x_1608_ = lean_string_append(v___x_1607_, v___x_1597_);
                    v___y_1579_ = v___x_1608_;
                    state = 16;
                    continue;
                }
            }
            1 => {
                v___x_1335_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0;
                v___x_1336_ = lean_string_append(v_acc_1334_, v___x_1335_);
                return v___x_1336_;
            }
            2 => {
                v___x_1339_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0;
                v_acc_1340_ = lean_string_append(v_acc_1338_, v___x_1339_);
                v_acc_1334_ = v_acc_1340_;
                state = 1;
                continue;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_tags_x3f_1348_) == 1 {
                    v_val_1351_ = crate::leanh::lean_ctor_get(v_tags_x3f_1348_, 0);
                    crate::leanh::lean_inc(v_val_1351_);
                    crate::leanh::lean_dec_ref_known(v_tags_x3f_1348_, 1);
                    v___x_1352_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1353_ = lean_array_get_size(v_val_1351_);
                    v___x_1354_ = lean_nat_dec_lt(v___x_1352_, v___x_1353_);
                    if v___x_1354_ == 0 {
                        crate::leanh::lean_dec(v_val_1351_);
                        v_acc_1334_ = v_acc_1350_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1355_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__0;
                        v_acc_1356_ = lean_string_append(v_acc_1350_, v___x_1355_);
                        v___x_1357_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1358_ = lean_nat_dec_eq(v___x_1353_, v___x_1357_);
                        if v___x_1358_ == 0 {
                            v_acc_1359_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast(v_acc_1356_, v_val_1351_, v___x_1352_);
                            crate::leanh::lean_dec(v_val_1351_);
                            v_acc_1338_ = v_acc_1359_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_val_1351_);
                            v___x_1360_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0_once), _init_l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0);
                            v_acc_1361_ = lean_string_append(v_acc_1356_, v___x_1360_);
                            v_acc_1338_ = v_acc_1361_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_tags_x3f_1348_);
                    v_acc_1334_ = v_acc_1350_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                v___x_1364_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0;
                v___x_1365_ = lean_string_append(v_acc_1363_, v___x_1364_);
                v_acc_1350_ = v___x_1365_;
                state = 3;
                continue;
            }
            5 => {
                v___x_1368_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1;
                v_acc_1369_ = lean_string_append(v___y_1367_, v___x_1368_);
                v_acc_1363_ = v_acc_1369_;
                state = 4;
                continue;
            }
            6 => {
                v___x_1372_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1;
                v_acc_1373_ = lean_string_append(v___y_1371_, v___x_1372_);
                v_acc_1363_ = v_acc_1373_;
                state = 4;
                continue;
            }
            7 => {
                if crate::leanh::lean_obj_tag(v_id_x3f_1376_) == 1 {
                    v_val_1378_ = crate::leanh::lean_ctor_get(v_id_x3f_1376_, 0);
                    crate::leanh::lean_inc(v_val_1378_);
                    crate::leanh::lean_dec_ref_known(v_id_x3f_1376_, 1);
                    v_acc_1379_ = lean_string_append(v_acc_1377_, v___y_1375_);
                    if crate::leanh::lean_obj_tag(v_val_1378_) == 0 {
                        v_declName_1380_ = crate::leanh::lean_ctor_get(v_val_1378_, 0);
                        crate::leanh::lean_inc(v_declName_1380_);
                        crate::leanh::lean_dec_ref_known(v_val_1378_, 1);
                        v___x_1381_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__2;
                        v_acc_1382_ = lean_string_append(v_acc_1379_, v___x_1381_);
                        v___x_1383_ = 1;
                        v___x_1384_ = l_Lean_Name_toString(v_declName_1380_, v___x_1383_);
                        v___x_1385_ =
                            l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v___x_1384_);
                        if v___x_1385_ == 0 {
                            v___x_1386_ = lean_string_append(v_acc_1382_, v___x_1384_);
                            crate::leanh::lean_dec_ref(v___x_1384_);
                            v___y_1371_ = v___x_1386_;
                            state = 6;
                            continue;
                        } else {
                            v___x_1387_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_1388_ = lean_string_utf8_byte_size(v___x_1384_);
                            crate::leanh::lean_inc_ref(v___x_1384_);
                            v___f_1389_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0___boxed as *mut core::ffi::c_void, 6, 2);
                            crate::leanh::lean_closure_set(v___f_1389_, 0, v___x_1388_);
                            crate::leanh::lean_closure_set(v___f_1389_, 1, v___x_1384_);
                            v___x_1390_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1390_, 0, v___x_1384_);
                            crate::leanh::lean_ctor_set(v___x_1390_, 1, v___x_1387_);
                            crate::leanh::lean_ctor_set(v___x_1390_, 2, v___x_1388_);
                            v___x_1391_ = l_String_Slice_positions(v___x_1390_);
                            crate::leanh::lean_dec_ref_known(v___x_1390_, 3);
                            v___x_1392_ = l_WellFounded_opaqueFix_u2083___redArg(
                                v___f_1389_,
                                v___x_1391_,
                                v_acc_1382_,
                                crate::leanh::lean_box(0),
                            );
                            v___y_1371_ = v___x_1392_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_id_1393_ = crate::leanh::lean_ctor_get(v_val_1378_, 0);
                        crate::leanh::lean_inc(v_id_1393_);
                        crate::leanh::lean_dec_ref_known(v_val_1378_, 1);
                        v___x_1394_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__3;
                        v_acc_1395_ = lean_string_append(v_acc_1379_, v___x_1394_);
                        v___x_1396_ = 1;
                        v___x_1397_ = l_Lean_Name_toString(v_id_1393_, v___x_1396_);
                        v___x_1398_ =
                            l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v___x_1397_);
                        if v___x_1398_ == 0 {
                            v___x_1399_ = lean_string_append(v_acc_1395_, v___x_1397_);
                            crate::leanh::lean_dec_ref(v___x_1397_);
                            v___y_1367_ = v___x_1399_;
                            state = 5;
                            continue;
                        } else {
                            v___x_1400_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_1401_ = lean_string_utf8_byte_size(v___x_1397_);
                            crate::leanh::lean_inc_ref(v___x_1397_);
                            v___f_1402_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0___boxed as *mut core::ffi::c_void, 6, 2);
                            crate::leanh::lean_closure_set(v___f_1402_, 0, v___x_1401_);
                            crate::leanh::lean_closure_set(v___f_1402_, 1, v___x_1397_);
                            v___x_1403_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1403_, 0, v___x_1397_);
                            crate::leanh::lean_ctor_set(v___x_1403_, 1, v___x_1400_);
                            crate::leanh::lean_ctor_set(v___x_1403_, 2, v___x_1401_);
                            v___x_1404_ = l_String_Slice_positions(v___x_1403_);
                            crate::leanh::lean_dec_ref_known(v___x_1403_, 3);
                            v___x_1405_ = l_WellFounded_opaqueFix_u2083___redArg(
                                v___f_1402_,
                                v___x_1404_,
                                v_acc_1395_,
                                crate::leanh::lean_box(0),
                            );
                            v___y_1367_ = v___x_1405_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_id_x3f_1376_);
                    v_acc_1363_ = v_acc_1377_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_line_1411_ = crate::leanh::lean_ctor_get(v_pos_1407_, 0);
                crate::leanh::lean_inc(v_line_1411_);
                v_character_1412_ = crate::leanh::lean_ctor_get(v_pos_1407_, 1);
                crate::leanh::lean_inc(v_character_1412_);
                crate::leanh::lean_dec_ref(v_pos_1407_);
                v___x_1413_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4;
                v___x_1414_ = lean_string_append(v___y_1410_, v___x_1413_);
                v___x_1415_ = l_Nat_reprFast(v_line_1411_);
                v_acc_1416_ = lean_string_append(v___x_1414_, v___x_1415_);
                crate::leanh::lean_dec_ref(v___x_1415_);
                v___x_1417_ = lean_string_append(v_acc_1416_, v___x_1413_);
                v___x_1418_ = l_Nat_reprFast(v_character_1412_);
                v_acc_1419_ = lean_string_append(v___x_1417_, v___x_1418_);
                crate::leanh::lean_dec_ref(v___x_1418_);
                if crate::leanh::lean_obj_tag(v_cPos_x3f_1408_) == 1 {
                    v_val_1420_ = crate::leanh::lean_ctor_get(v_cPos_x3f_1408_, 0);
                    crate::leanh::lean_inc(v_val_1420_);
                    crate::leanh::lean_dec_ref_known(v_cPos_x3f_1408_, 1);
                    v___x_1421_ = lean_string_append(v_acc_1419_, v___x_1413_);
                    v___x_1422_ = l_Nat_reprFast(v_val_1420_);
                    v_acc_1423_ = lean_string_append(v___x_1421_, v___x_1422_);
                    crate::leanh::lean_dec_ref(v___x_1422_);
                    v___y_1375_ = v___x_1413_;
                    v_id_x3f_1376_ = v_id_x3f_1409_;
                    v_acc_1377_ = v_acc_1423_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_cPos_x3f_1408_);
                    v___y_1375_ = v___x_1413_;
                    v_id_x3f_1376_ = v_id_x3f_1409_;
                    v_acc_1377_ = v_acc_1419_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if crate::leanh::lean_obj_tag(v_data_x3f_1347_) == 1 {
                    v_val_1426_ = crate::leanh::lean_ctor_get(v_data_x3f_1347_, 0);
                    crate::leanh::lean_inc(v_val_1426_);
                    crate::leanh::lean_dec_ref_known(v_data_x3f_1347_, 1);
                    v_uri_1427_ = crate::leanh::lean_ctor_get(v_val_1426_, 0);
                    crate::leanh::lean_inc_ref(v_uri_1427_);
                    v_pos_1428_ = crate::leanh::lean_ctor_get(v_val_1426_, 1);
                    crate::leanh::lean_inc_ref(v_pos_1428_);
                    v_cPos_x3f_1429_ = crate::leanh::lean_ctor_get(v_val_1426_, 2);
                    crate::leanh::lean_inc(v_cPos_x3f_1429_);
                    v_id_x3f_1430_ = crate::leanh::lean_ctor_get(v_val_1426_, 3);
                    crate::leanh::lean_inc(v_id_x3f_1430_);
                    crate::leanh::lean_dec(v_val_1426_);
                    v___x_1431_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__1;
                    v_acc_1432_ = lean_string_append(v_acc_1425_, v___x_1431_);
                    v___x_1433_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__5;
                    v_acc_1434_ = lean_string_append(v_acc_1432_, v___x_1433_);
                    v___x_1435_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1;
                    v_acc_1436_ = lean_string_append(v_acc_1434_, v___x_1435_);
                    v___x_1437_ =
                        l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_uri_1427_);
                    if v___x_1437_ == 0 {
                        v___x_1438_ = lean_string_append(v_acc_1436_, v_uri_1427_);
                        crate::leanh::lean_dec_ref(v_uri_1427_);
                        v___x_1439_ = lean_string_append(v___x_1438_, v___x_1435_);
                        v_pos_1407_ = v_pos_1428_;
                        v_cPos_x3f_1408_ = v_cPos_x3f_1429_;
                        v_id_x3f_1409_ = v_id_x3f_1430_;
                        v___y_1410_ = v___x_1439_;
                        state = 8;
                        continue;
                    } else {
                        v___x_1440_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1441_ = lean_string_utf8_byte_size(v_uri_1427_);
                        crate::leanh::lean_inc_ref(v_uri_1427_);
                        v___f_1442_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__2___boxed as *mut core::ffi::c_void, 6, 2);
                        crate::leanh::lean_closure_set(v___f_1442_, 0, v___x_1441_);
                        crate::leanh::lean_closure_set(v___f_1442_, 1, v_uri_1427_);
                        v___x_1443_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1443_, 0, v_uri_1427_);
                        crate::leanh::lean_ctor_set(v___x_1443_, 1, v___x_1440_);
                        crate::leanh::lean_ctor_set(v___x_1443_, 2, v___x_1441_);
                        v___x_1444_ = l_String_Slice_positions(v___x_1443_);
                        crate::leanh::lean_dec_ref_known(v___x_1443_, 3);
                        v___x_1445_ = l_WellFounded_opaqueFix_u2083___redArg(
                            v___f_1442_,
                            v___x_1444_,
                            v_acc_1436_,
                            crate::leanh::lean_box(0),
                        );
                        v___x_1446_ = lean_string_append(v___x_1445_, v___x_1435_);
                        v_pos_1407_ = v_pos_1428_;
                        v_cPos_x3f_1408_ = v_cPos_x3f_1429_;
                        v_id_x3f_1409_ = v_id_x3f_1430_;
                        v___y_1410_ = v___x_1446_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_data_x3f_1347_);
                    v_acc_1350_ = v_acc_1425_;
                    state = 3;
                    continue;
                }
            }
            10 => {
                if crate::leanh::lean_obj_tag(v_sortText_x3f_1346_) == 1 {
                    v_val_1449_ = crate::leanh::lean_ctor_get(v_sortText_x3f_1346_, 0);
                    crate::leanh::lean_inc(v_val_1449_);
                    crate::leanh::lean_dec_ref_known(v_sortText_x3f_1346_, 1);
                    v___x_1450_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__2;
                    v_acc_1451_ = lean_string_append(v_acc_1448_, v___x_1450_);
                    v___x_1452_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1;
                    v_acc_1453_ = lean_string_append(v_acc_1451_, v___x_1452_);
                    v___x_1454_ =
                        l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_val_1449_);
                    if v___x_1454_ == 0 {
                        v___x_1455_ = lean_string_append(v_acc_1453_, v_val_1449_);
                        crate::leanh::lean_dec(v_val_1449_);
                        v___x_1456_ = lean_string_append(v___x_1455_, v___x_1452_);
                        v_acc_1425_ = v___x_1456_;
                        state = 9;
                        continue;
                    } else {
                        v___x_1457_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1458_ = lean_string_utf8_byte_size(v_val_1449_);
                        crate::leanh::lean_inc(v_val_1449_);
                        v___f_1459_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3___boxed as *mut core::ffi::c_void, 6, 2);
                        crate::leanh::lean_closure_set(v___f_1459_, 0, v___x_1458_);
                        crate::leanh::lean_closure_set(v___f_1459_, 1, v_val_1449_);
                        v___x_1460_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1460_, 0, v_val_1449_);
                        crate::leanh::lean_ctor_set(v___x_1460_, 1, v___x_1457_);
                        crate::leanh::lean_ctor_set(v___x_1460_, 2, v___x_1458_);
                        v___x_1461_ = l_String_Slice_positions(v___x_1460_);
                        crate::leanh::lean_dec_ref_known(v___x_1460_, 3);
                        v___x_1462_ = l_WellFounded_opaqueFix_u2083___redArg(
                            v___f_1459_,
                            v___x_1461_,
                            v_acc_1453_,
                            crate::leanh::lean_box(0),
                        );
                        v___x_1463_ = lean_string_append(v___x_1462_, v___x_1452_);
                        v_acc_1425_ = v___x_1463_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_sortText_x3f_1346_);
                    v_acc_1425_ = v_acc_1448_;
                    state = 9;
                    continue;
                }
            }
            11 => {
                if crate::leanh::lean_obj_tag(v_textEdit_x3f_1345_) == 1 {
                    v_val_1466_ = crate::leanh::lean_ctor_get(v_textEdit_x3f_1345_, 0);
                    crate::leanh::lean_inc(v_val_1466_);
                    crate::leanh::lean_dec_ref_known(v_textEdit_x3f_1345_, 1);
                    v_insert_1467_ = crate::leanh::lean_ctor_get(v_val_1466_, 1);
                    v_end_1468_ = crate::leanh::lean_ctor_get(v_insert_1467_, 1);
                    crate::leanh::lean_inc_ref(v_end_1468_);
                    v_start_1469_ = crate::leanh::lean_ctor_get(v_insert_1467_, 0);
                    crate::leanh::lean_inc_ref(v_start_1469_);
                    v_replace_1470_ = crate::leanh::lean_ctor_get(v_val_1466_, 2);
                    v_end_1471_ = crate::leanh::lean_ctor_get(v_replace_1470_, 1);
                    crate::leanh::lean_inc_ref(v_end_1471_);
                    v_start_1472_ = crate::leanh::lean_ctor_get(v_replace_1470_, 0);
                    crate::leanh::lean_inc_ref(v_start_1472_);
                    v_newText_1473_ = crate::leanh::lean_ctor_get(v_val_1466_, 0);
                    crate::leanh::lean_inc_ref(v_newText_1473_);
                    crate::leanh::lean_dec(v_val_1466_);
                    v_line_1474_ = crate::leanh::lean_ctor_get(v_end_1468_, 0);
                    crate::leanh::lean_inc(v_line_1474_);
                    v_character_1475_ = crate::leanh::lean_ctor_get(v_end_1468_, 1);
                    crate::leanh::lean_inc(v_character_1475_);
                    crate::leanh::lean_dec_ref(v_end_1468_);
                    v_line_1476_ = crate::leanh::lean_ctor_get(v_start_1469_, 0);
                    crate::leanh::lean_inc(v_line_1476_);
                    v_character_1477_ = crate::leanh::lean_ctor_get(v_start_1469_, 1);
                    crate::leanh::lean_inc(v_character_1477_);
                    crate::leanh::lean_dec_ref(v_start_1469_);
                    v_line_1478_ = crate::leanh::lean_ctor_get(v_end_1471_, 0);
                    crate::leanh::lean_inc(v_line_1478_);
                    v_character_1479_ = crate::leanh::lean_ctor_get(v_end_1471_, 1);
                    crate::leanh::lean_inc(v_character_1479_);
                    crate::leanh::lean_dec_ref(v_end_1471_);
                    v_line_1480_ = crate::leanh::lean_ctor_get(v_start_1472_, 0);
                    crate::leanh::lean_inc(v_line_1480_);
                    v_character_1481_ = crate::leanh::lean_ctor_get(v_start_1472_, 1);
                    crate::leanh::lean_inc(v_character_1481_);
                    crate::leanh::lean_dec_ref(v_start_1472_);
                    v___x_1482_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__3;
                    v_acc_1483_ = lean_string_append(v_acc_1465_, v___x_1482_);
                    v___x_1484_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__0;
                    v_acc_1485_ = lean_string_append(v_acc_1483_, v___x_1484_);
                    v___x_1486_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__0;
                    v_acc_1487_ = lean_string_append(v_acc_1485_, v___x_1486_);
                    v___x_1488_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0;
                    v___x_1489_ = lean_string_append(v_acc_1487_, v___x_1488_);
                    v___x_1490_ = l_Nat_reprFast(v_character_1475_);
                    v___x_1491_ = lean_string_append(v___x_1489_, v___x_1490_);
                    crate::leanh::lean_dec_ref(v___x_1490_);
                    v___x_1492_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1;
                    v___x_1493_ = lean_string_append(v___x_1491_, v___x_1492_);
                    v___x_1494_ = l_Nat_reprFast(v_line_1474_);
                    v___x_1495_ = lean_string_append(v___x_1493_, v___x_1494_);
                    crate::leanh::lean_dec_ref(v___x_1494_);
                    v___x_1496_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0;
                    v_acc_1497_ = lean_string_append(v___x_1495_, v___x_1496_);
                    v___x_1498_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__1;
                    v_acc_1499_ = lean_string_append(v_acc_1497_, v___x_1498_);
                    v___x_1500_ = lean_string_append(v_acc_1499_, v___x_1488_);
                    v___x_1501_ = l_Nat_reprFast(v_character_1477_);
                    v___x_1502_ = lean_string_append(v___x_1500_, v___x_1501_);
                    crate::leanh::lean_dec_ref(v___x_1501_);
                    v___x_1503_ = lean_string_append(v___x_1502_, v___x_1492_);
                    v___x_1504_ = l_Nat_reprFast(v_line_1476_);
                    v___x_1505_ = lean_string_append(v___x_1503_, v___x_1504_);
                    crate::leanh::lean_dec_ref(v___x_1504_);
                    v_acc_1506_ = lean_string_append(v___x_1505_, v___x_1496_);
                    v_acc_1507_ = lean_string_append(v_acc_1506_, v___x_1496_);
                    v___x_1508_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__1;
                    v___x_1509_ = lean_string_append(v_acc_1507_, v___x_1508_);
                    v___x_1510_ = lean_string_append(v___x_1509_, v_newText_1473_);
                    crate::leanh::lean_dec_ref(v_newText_1473_);
                    v___x_1511_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1;
                    v_acc_1512_ = lean_string_append(v___x_1510_, v___x_1511_);
                    v___x_1513_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__2;
                    v_acc_1514_ = lean_string_append(v_acc_1512_, v___x_1513_);
                    v_acc_1515_ = lean_string_append(v_acc_1514_, v___x_1486_);
                    v___x_1516_ = lean_string_append(v_acc_1515_, v___x_1488_);
                    v___x_1517_ = l_Nat_reprFast(v_character_1479_);
                    v___x_1518_ = lean_string_append(v___x_1516_, v___x_1517_);
                    crate::leanh::lean_dec_ref(v___x_1517_);
                    v___x_1519_ = lean_string_append(v___x_1518_, v___x_1492_);
                    v___x_1520_ = l_Nat_reprFast(v_line_1478_);
                    v___x_1521_ = lean_string_append(v___x_1519_, v___x_1520_);
                    crate::leanh::lean_dec_ref(v___x_1520_);
                    v_acc_1522_ = lean_string_append(v___x_1521_, v___x_1496_);
                    v_acc_1523_ = lean_string_append(v_acc_1522_, v___x_1498_);
                    v___x_1524_ = lean_string_append(v_acc_1523_, v___x_1488_);
                    v___x_1525_ = l_Nat_reprFast(v_character_1481_);
                    v___x_1526_ = lean_string_append(v___x_1524_, v___x_1525_);
                    crate::leanh::lean_dec_ref(v___x_1525_);
                    v___x_1527_ = lean_string_append(v___x_1526_, v___x_1492_);
                    v___x_1528_ = l_Nat_reprFast(v_line_1480_);
                    v___x_1529_ = lean_string_append(v___x_1527_, v___x_1528_);
                    crate::leanh::lean_dec_ref(v___x_1528_);
                    v_acc_1530_ = lean_string_append(v___x_1529_, v___x_1496_);
                    v_acc_1531_ = lean_string_append(v_acc_1530_, v___x_1496_);
                    v_acc_1532_ = lean_string_append(v_acc_1531_, v___x_1496_);
                    v_acc_1448_ = v_acc_1532_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_textEdit_x3f_1345_);
                    v_acc_1448_ = v_acc_1465_;
                    state = 10;
                    continue;
                }
            }
            12 => {
                if crate::leanh::lean_obj_tag(v_kind_x3f_1344_) == 1 {
                    v_val_1535_ = crate::leanh::lean_ctor_get(v_kind_x3f_1344_, 0);
                    crate::leanh::lean_inc(v_val_1535_);
                    crate::leanh::lean_dec_ref_known(v_kind_x3f_1344_, 1);
                    v___x_1536_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__4;
                    v___x_1537_ = lean_string_append(v_acc_1534_, v___x_1536_);
                    v___x_1538_ = (crate::leanh::lean_unbox(v_val_1535_) as u8);
                    crate::leanh::lean_dec(v_val_1535_);
                    v___x_1539_ = l_Lean_Lsp_CompletionItemKind_ctorIdx(v___x_1538_);
                    v___x_1540_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1541_ = lean_nat_add(v___x_1539_, v___x_1540_);
                    crate::leanh::lean_dec(v___x_1539_);
                    v___x_1542_ = l_Nat_reprFast(v___x_1541_);
                    v_acc_1543_ = lean_string_append(v___x_1537_, v___x_1542_);
                    crate::leanh::lean_dec_ref(v___x_1542_);
                    v_acc_1465_ = v_acc_1543_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_kind_x3f_1344_);
                    v_acc_1465_ = v_acc_1534_;
                    state = 11;
                    continue;
                }
            }
            13 => {
                v___x_1546_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0;
                v___x_1547_ = lean_string_append(v___y_1545_, v___x_1546_);
                v_acc_1534_ = v___x_1547_;
                state = 12;
                continue;
            }
            14 => {
                v___x_1552_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__1;
                v___x_1553_ = lean_string_append(v___y_1550_, v___x_1552_);
                v___x_1554_ = lean_string_append(v___x_1553_, v___y_1551_);
                v___x_1555_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__2;
                v_acc_1556_ = lean_string_append(v___x_1554_, v___x_1555_);
                v___x_1557_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1;
                v_acc_1558_ = lean_string_append(v_acc_1556_, v___x_1557_);
                v___x_1559_ =
                    l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_value_1549_);
                if v___x_1559_ == 0 {
                    v___x_1560_ = lean_string_append(v_acc_1558_, v_value_1549_);
                    crate::leanh::lean_dec_ref(v_value_1549_);
                    v___x_1561_ = lean_string_append(v___x_1560_, v___x_1557_);
                    v___y_1545_ = v___x_1561_;
                    state = 13;
                    continue;
                } else {
                    v___x_1562_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1563_ = lean_string_utf8_byte_size(v_value_1549_);
                    crate::leanh::lean_inc_ref(v_value_1549_);
                    v___f_1564_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___lam__0___boxed as *mut core::ffi::c_void, 6, 2);
                    crate::leanh::lean_closure_set(v___f_1564_, 0, v___x_1563_);
                    crate::leanh::lean_closure_set(v___f_1564_, 1, v_value_1549_);
                    v___x_1565_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1565_, 0, v_value_1549_);
                    crate::leanh::lean_ctor_set(v___x_1565_, 1, v___x_1562_);
                    crate::leanh::lean_ctor_set(v___x_1565_, 2, v___x_1563_);
                    v___x_1566_ = l_String_Slice_positions(v___x_1565_);
                    crate::leanh::lean_dec_ref_known(v___x_1565_, 3);
                    v___x_1567_ = l_WellFounded_opaqueFix_u2083___redArg(
                        v___f_1564_,
                        v___x_1566_,
                        v_acc_1558_,
                        crate::leanh::lean_box(0),
                    );
                    v___x_1568_ = lean_string_append(v___x_1567_, v___x_1557_);
                    v___y_1545_ = v___x_1568_;
                    state = 13;
                    continue;
                }
            }
            15 => {
                if crate::leanh::lean_obj_tag(v_documentation_x3f_1343_) == 1 {
                    v_val_1571_ = crate::leanh::lean_ctor_get(v_documentation_x3f_1343_, 0);
                    crate::leanh::lean_inc(v_val_1571_);
                    crate::leanh::lean_dec_ref_known(v_documentation_x3f_1343_, 1);
                    v_kind_1572_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_1571_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v_value_1573_ = crate::leanh::lean_ctor_get(v_val_1571_, 0);
                    crate::leanh::lean_inc_ref(v_value_1573_);
                    crate::leanh::lean_dec(v_val_1571_);
                    v___x_1574_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__5;
                    v_acc_1575_ = lean_string_append(v_acc_1570_, v___x_1574_);
                    if v_kind_1572_ == 0 {
                        v___x_1576_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__3;
                        v_value_1549_ = v_value_1573_;
                        v___y_1550_ = v_acc_1575_;
                        v___y_1551_ = v___x_1576_;
                        state = 14;
                        continue;
                    } else {
                        v___x_1577_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__4;
                        v_value_1549_ = v_value_1573_;
                        v___y_1550_ = v_acc_1575_;
                        v___y_1551_ = v___x_1577_;
                        state = 14;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_documentation_x3f_1343_);
                    v_acc_1534_ = v_acc_1570_;
                    state = 12;
                    continue;
                }
            }
            16 => {
                if crate::leanh::lean_obj_tag(v_detail_x3f_1342_) == 1 {
                    v_val_1580_ = crate::leanh::lean_ctor_get(v_detail_x3f_1342_, 0);
                    crate::leanh::lean_inc(v_val_1580_);
                    crate::leanh::lean_dec_ref_known(v_detail_x3f_1342_, 1);
                    v___x_1581_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__6;
                    v_acc_1582_ = lean_string_append(v___y_1579_, v___x_1581_);
                    v___x_1583_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1;
                    v_acc_1584_ = lean_string_append(v_acc_1582_, v___x_1583_);
                    v___x_1585_ =
                        l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_val_1580_);
                    if v___x_1585_ == 0 {
                        v___x_1586_ = lean_string_append(v_acc_1584_, v_val_1580_);
                        crate::leanh::lean_dec(v_val_1580_);
                        v___x_1587_ = lean_string_append(v___x_1586_, v___x_1583_);
                        v_acc_1570_ = v___x_1587_;
                        state = 15;
                        continue;
                    } else {
                        v___x_1588_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1589_ = lean_string_utf8_byte_size(v_val_1580_);
                        crate::leanh::lean_inc(v_val_1580_);
                        v___f_1590_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3___boxed as *mut core::ffi::c_void, 6, 2);
                        crate::leanh::lean_closure_set(v___f_1590_, 0, v___x_1589_);
                        crate::leanh::lean_closure_set(v___f_1590_, 1, v_val_1580_);
                        v___x_1591_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1591_, 0, v_val_1580_);
                        crate::leanh::lean_ctor_set(v___x_1591_, 1, v___x_1588_);
                        crate::leanh::lean_ctor_set(v___x_1591_, 2, v___x_1589_);
                        v___x_1592_ = l_String_Slice_positions(v___x_1591_);
                        crate::leanh::lean_dec_ref_known(v___x_1591_, 3);
                        v___x_1593_ = l_WellFounded_opaqueFix_u2083___redArg(
                            v___f_1590_,
                            v___x_1592_,
                            v_acc_1584_,
                            crate::leanh::lean_box(0),
                        );
                        v___x_1594_ = lean_string_append(v___x_1593_, v___x_1583_);
                        v_acc_1570_ = v___x_1594_;
                        state = 15;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_detail_x3f_1342_);
                    v_acc_1570_ = v___y_1579_;
                    state = 15;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(
    mut v___x_1609_: *mut crate::leanh::LeanObject,
    mut v___x_1610_: *mut crate::leanh::LeanObject,
    mut v_a_1611_: *mut crate::leanh::LeanObject,
    mut v_b_1612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: u8 = 0;
    let mut v___x_1617_: u32 = 0;
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_1613_ = crate::leanh::lean_ctor_get(v___x_1609_, 1);
                v_endExclusive_1614_ = crate::leanh::lean_ctor_get(v___x_1609_, 2);
                v___x_1615_ = lean_nat_sub(v_endExclusive_1614_, v_startInclusive_1613_);
                v___x_1616_ = lean_nat_dec_eq(v_a_1611_, v___x_1615_);
                crate::leanh::lean_dec(v___x_1615_);
                if v___x_1616_ == 0 {
                    v___x_1617_ = lean_string_utf8_get_fast(v___x_1610_, v_a_1611_);
                    v___x_1618_ = lean_string_utf8_next_fast(v___x_1610_, v_a_1611_);
                    crate::leanh::lean_dec(v_a_1611_);
                    v___x_1619_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(
                        v_b_1612_,
                        v___x_1617_,
                    );
                    v_a_1611_ = v___x_1618_;
                    v_b_1612_ = v___x_1619_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_1611_);
                    return v_b_1612_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg___boxed(
    mut v___x_1621_: *mut crate::leanh::LeanObject,
    mut v___x_1622_: *mut crate::leanh::LeanObject,
    mut v_a_1623_: *mut crate::leanh::LeanObject,
    mut v_b_1624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1625_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_1621_, v___x_1622_, v_a_1623_, v_b_1624_);
    crate::leanh::lean_dec_ref(v___x_1622_);
    crate::leanh::lean_dec_ref(v___x_1621_);
    return v_res_1625_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast(
    mut v_acc_1626_: *mut crate::leanh::LeanObject,
    mut v_items_1627_: *mut crate::leanh::LeanObject,
    mut v_i_1628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: u8 = 0;
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: u8 = 0;
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tags_x3f_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: u8 = 0;
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: u8 = 0;
    let mut v_acc_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_x3f_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: u8 = 0;
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: u8 = 0;
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cPos_x3f_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_x3f_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uri_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cPos_x3f_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_x3f_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: u8 = 0;
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sortText_x3f_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: u8 = 0;
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_textEdit_x3f_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_insert_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_end_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_replace_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_end_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newText_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_x3f_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: u8 = 0;
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: u8 = 0;
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_documentation_x3f_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1872_: u8 = 0;
    let mut v_value_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_detail_x3f_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: u8 = 0;
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_label_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: u8 = 0;
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1634_ = lean_array_get_size(v_items_1627_);
                v___x_1648_ = lean_nat_dec_lt(v_i_1628_, v___x_1634_);
                if v___x_1648_ == 0 {
                    crate::leanh::lean_dec(v_i_1628_);
                    return v_acc_1626_;
                } else {
                    v___x_1649_ = lean_array_fget_borrowed(v_items_1627_, v_i_1628_);
                    v_label_1895_ = crate::leanh::lean_ctor_get(v___x_1649_, 0);
                    v___x_1896_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__7;
                    v_acc_1897_ = lean_string_append(v_acc_1626_, v___x_1896_);
                    v___x_1898_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1;
                    v_acc_1899_ = lean_string_append(v_acc_1897_, v___x_1898_);
                    v___x_1900_ =
                        l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_label_1895_);
                    if v___x_1900_ == 0 {
                        v___x_1901_ = lean_string_append(v_acc_1899_, v_label_1895_);
                        v___x_1902_ = lean_string_append(v___x_1901_, v___x_1898_);
                        v___y_1879_ = v___x_1902_;
                        state = 17;
                        continue;
                    } else {
                        v___x_1903_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1904_ = lean_string_utf8_byte_size(v_label_1895_);
                        crate::leanh::lean_inc_ref(v_label_1895_);
                        v___x_1905_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1905_, 0, v_label_1895_);
                        crate::leanh::lean_ctor_set(v___x_1905_, 1, v___x_1903_);
                        crate::leanh::lean_ctor_set(v___x_1905_, 2, v___x_1904_);
                        v___x_1906_ = l_String_Slice_positions(v___x_1905_);
                        v___x_1907_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_1905_, v_label_1895_, v___x_1906_, v_acc_1899_);
                        crate::leanh::lean_dec_ref_known(v___x_1905_, 3);
                        v___x_1908_ = lean_string_append(v___x_1907_, v___x_1898_);
                        v___y_1879_ = v___x_1908_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1632_ = lean_nat_add(v_i_1628_, v___y_1630_);
                crate::leanh::lean_dec(v_i_1628_);
                v_acc_1626_ = v___y_1631_;
                v_i_1628_ = v___x_1632_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1637_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0;
                v___x_1638_ = lean_string_append(v_acc_1636_, v___x_1637_);
                v___x_1639_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1640_ = lean_nat_sub(v___x_1634_, v___x_1639_);
                v___x_1641_ = lean_nat_dec_lt(v_i_1628_, v___x_1640_);
                crate::leanh::lean_dec(v___x_1640_);
                if v___x_1641_ == 0 {
                    v___y_1630_ = v___x_1639_;
                    v___y_1631_ = v___x_1638_;
                    state = 1;
                    continue;
                } else {
                    v___x_1642_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4;
                    v___x_1643_ = lean_string_append(v___x_1638_, v___x_1642_);
                    v___y_1630_ = v___x_1639_;
                    v___y_1631_ = v___x_1643_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1646_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0;
                v_acc_1647_ = lean_string_append(v_acc_1645_, v___x_1646_);
                v_acc_1636_ = v_acc_1647_;
                state = 2;
                continue;
            }
            4 => {
                v_tags_x3f_1652_ = crate::leanh::lean_ctor_get(v___x_1649_, 7);
                if crate::leanh::lean_obj_tag(v_tags_x3f_1652_) == 1 {
                    v_val_1653_ = crate::leanh::lean_ctor_get(v_tags_x3f_1652_, 0);
                    v___x_1654_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1655_ = lean_array_get_size(v_val_1653_);
                    v___x_1656_ = lean_nat_dec_lt(v___x_1654_, v___x_1655_);
                    if v___x_1656_ == 0 {
                        v_acc_1636_ = v_acc_1651_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1657_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__0;
                        v_acc_1658_ = lean_string_append(v_acc_1651_, v___x_1657_);
                        v___x_1659_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1660_ = lean_nat_dec_eq(v___x_1655_, v___x_1659_);
                        if v___x_1660_ == 0 {
                            v_acc_1661_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast(v_acc_1658_, v_val_1653_, v___x_1654_);
                            v_acc_1645_ = v_acc_1661_;
                            state = 3;
                            continue;
                        } else {
                            v___x_1662_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0_once), _init_l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0);
                            v_acc_1663_ = lean_string_append(v_acc_1658_, v___x_1662_);
                            v_acc_1645_ = v_acc_1663_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_acc_1636_ = v_acc_1651_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_1666_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0;
                v___x_1667_ = lean_string_append(v_acc_1665_, v___x_1666_);
                v_acc_1651_ = v___x_1667_;
                state = 4;
                continue;
            }
            6 => {
                v___x_1670_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1;
                v_acc_1671_ = lean_string_append(v___y_1669_, v___x_1670_);
                v_acc_1665_ = v_acc_1671_;
                state = 5;
                continue;
            }
            7 => {
                v___x_1674_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1;
                v_acc_1675_ = lean_string_append(v___y_1673_, v___x_1674_);
                v_acc_1665_ = v_acc_1675_;
                state = 5;
                continue;
            }
            8 => {
                if crate::leanh::lean_obj_tag(v_id_x3f_1678_) == 1 {
                    v_val_1680_ = crate::leanh::lean_ctor_get(v_id_x3f_1678_, 0);
                    crate::leanh::lean_inc(v_val_1680_);
                    crate::leanh::lean_dec_ref_known(v_id_x3f_1678_, 1);
                    v_acc_1681_ = lean_string_append(v_acc_1679_, v___y_1677_);
                    if crate::leanh::lean_obj_tag(v_val_1680_) == 0 {
                        v_declName_1682_ = crate::leanh::lean_ctor_get(v_val_1680_, 0);
                        crate::leanh::lean_inc(v_declName_1682_);
                        crate::leanh::lean_dec_ref_known(v_val_1680_, 1);
                        v___x_1683_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__2;
                        v_acc_1684_ = lean_string_append(v_acc_1681_, v___x_1683_);
                        v___x_1685_ = l_Lean_Name_toString(v_declName_1682_, v___x_1648_);
                        v___x_1686_ =
                            l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v___x_1685_);
                        if v___x_1686_ == 0 {
                            v___x_1687_ = lean_string_append(v_acc_1684_, v___x_1685_);
                            crate::leanh::lean_dec_ref(v___x_1685_);
                            v___y_1669_ = v___x_1687_;
                            state = 6;
                            continue;
                        } else {
                            v___x_1688_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_1689_ = lean_string_utf8_byte_size(v___x_1685_);
                            crate::leanh::lean_inc_ref(v___x_1685_);
                            v___x_1690_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1690_, 0, v___x_1685_);
                            crate::leanh::lean_ctor_set(v___x_1690_, 1, v___x_1688_);
                            crate::leanh::lean_ctor_set(v___x_1690_, 2, v___x_1689_);
                            v___x_1691_ = l_String_Slice_positions(v___x_1690_);
                            v___x_1692_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_1690_, v___x_1685_, v___x_1691_, v_acc_1684_);
                            crate::leanh::lean_dec_ref(v___x_1685_);
                            crate::leanh::lean_dec_ref_known(v___x_1690_, 3);
                            v___y_1669_ = v___x_1692_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_id_1693_ = crate::leanh::lean_ctor_get(v_val_1680_, 0);
                        crate::leanh::lean_inc(v_id_1693_);
                        crate::leanh::lean_dec_ref_known(v_val_1680_, 1);
                        v___x_1694_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__3;
                        v_acc_1695_ = lean_string_append(v_acc_1681_, v___x_1694_);
                        v___x_1696_ = l_Lean_Name_toString(v_id_1693_, v___x_1648_);
                        v___x_1697_ =
                            l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v___x_1696_);
                        if v___x_1697_ == 0 {
                            v___x_1698_ = lean_string_append(v_acc_1695_, v___x_1696_);
                            crate::leanh::lean_dec_ref(v___x_1696_);
                            v___y_1673_ = v___x_1698_;
                            state = 7;
                            continue;
                        } else {
                            v___x_1699_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_1700_ = lean_string_utf8_byte_size(v___x_1696_);
                            crate::leanh::lean_inc_ref(v___x_1696_);
                            v___x_1701_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1701_, 0, v___x_1696_);
                            crate::leanh::lean_ctor_set(v___x_1701_, 1, v___x_1699_);
                            crate::leanh::lean_ctor_set(v___x_1701_, 2, v___x_1700_);
                            v___x_1702_ = l_String_Slice_positions(v___x_1701_);
                            v___x_1703_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_1701_, v___x_1696_, v___x_1702_, v_acc_1695_);
                            crate::leanh::lean_dec_ref(v___x_1696_);
                            crate::leanh::lean_dec_ref_known(v___x_1701_, 3);
                            v___y_1673_ = v___x_1703_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_id_x3f_1678_);
                    v_acc_1665_ = v_acc_1679_;
                    state = 5;
                    continue;
                }
            }
            9 => {
                v_line_1709_ = crate::leanh::lean_ctor_get(v_pos_1705_, 0);
                crate::leanh::lean_inc(v_line_1709_);
                v_character_1710_ = crate::leanh::lean_ctor_get(v_pos_1705_, 1);
                crate::leanh::lean_inc(v_character_1710_);
                crate::leanh::lean_dec_ref(v_pos_1705_);
                v___x_1711_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4;
                v___x_1712_ = lean_string_append(v___y_1708_, v___x_1711_);
                v___x_1713_ = l_Nat_reprFast(v_line_1709_);
                v_acc_1714_ = lean_string_append(v___x_1712_, v___x_1713_);
                crate::leanh::lean_dec_ref(v___x_1713_);
                v___x_1715_ = lean_string_append(v_acc_1714_, v___x_1711_);
                v___x_1716_ = l_Nat_reprFast(v_character_1710_);
                v_acc_1717_ = lean_string_append(v___x_1715_, v___x_1716_);
                crate::leanh::lean_dec_ref(v___x_1716_);
                if crate::leanh::lean_obj_tag(v_cPos_x3f_1706_) == 1 {
                    v_val_1718_ = crate::leanh::lean_ctor_get(v_cPos_x3f_1706_, 0);
                    crate::leanh::lean_inc(v_val_1718_);
                    crate::leanh::lean_dec_ref_known(v_cPos_x3f_1706_, 1);
                    v___x_1719_ = lean_string_append(v_acc_1717_, v___x_1711_);
                    v___x_1720_ = l_Nat_reprFast(v_val_1718_);
                    v_acc_1721_ = lean_string_append(v___x_1719_, v___x_1720_);
                    crate::leanh::lean_dec_ref(v___x_1720_);
                    v___y_1677_ = v___x_1711_;
                    v_id_x3f_1678_ = v_id_x3f_1707_;
                    v_acc_1679_ = v_acc_1721_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_cPos_x3f_1706_);
                    v___y_1677_ = v___x_1711_;
                    v_id_x3f_1678_ = v_id_x3f_1707_;
                    v_acc_1679_ = v_acc_1717_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                v_data_x3f_1724_ = crate::leanh::lean_ctor_get(v___x_1649_, 6);
                if crate::leanh::lean_obj_tag(v_data_x3f_1724_) == 1 {
                    v_val_1725_ = crate::leanh::lean_ctor_get(v_data_x3f_1724_, 0);
                    v_uri_1726_ = crate::leanh::lean_ctor_get(v_val_1725_, 0);
                    v_pos_1727_ = crate::leanh::lean_ctor_get(v_val_1725_, 1);
                    v_cPos_x3f_1728_ = crate::leanh::lean_ctor_get(v_val_1725_, 2);
                    v_id_x3f_1729_ = crate::leanh::lean_ctor_get(v_val_1725_, 3);
                    v___x_1730_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__1;
                    v_acc_1731_ = lean_string_append(v_acc_1723_, v___x_1730_);
                    v___x_1732_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__5;
                    v_acc_1733_ = lean_string_append(v_acc_1731_, v___x_1732_);
                    v___x_1734_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1;
                    v_acc_1735_ = lean_string_append(v_acc_1733_, v___x_1734_);
                    v___x_1736_ =
                        l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_uri_1726_);
                    if v___x_1736_ == 0 {
                        v___x_1737_ = lean_string_append(v_acc_1735_, v_uri_1726_);
                        v___x_1738_ = lean_string_append(v___x_1737_, v___x_1734_);
                        crate::leanh::lean_inc(v_id_x3f_1729_);
                        crate::leanh::lean_inc(v_cPos_x3f_1728_);
                        crate::leanh::lean_inc_ref(v_pos_1727_);
                        v_pos_1705_ = v_pos_1727_;
                        v_cPos_x3f_1706_ = v_cPos_x3f_1728_;
                        v_id_x3f_1707_ = v_id_x3f_1729_;
                        v___y_1708_ = v___x_1738_;
                        state = 9;
                        continue;
                    } else {
                        v___x_1739_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1740_ = lean_string_utf8_byte_size(v_uri_1726_);
                        crate::leanh::lean_inc_ref(v_uri_1726_);
                        v___x_1741_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1741_, 0, v_uri_1726_);
                        crate::leanh::lean_ctor_set(v___x_1741_, 1, v___x_1739_);
                        crate::leanh::lean_ctor_set(v___x_1741_, 2, v___x_1740_);
                        v___x_1742_ = l_String_Slice_positions(v___x_1741_);
                        v___x_1743_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_1741_, v_uri_1726_, v___x_1742_, v_acc_1735_);
                        crate::leanh::lean_dec_ref_known(v___x_1741_, 3);
                        v___x_1744_ = lean_string_append(v___x_1743_, v___x_1734_);
                        crate::leanh::lean_inc(v_id_x3f_1729_);
                        crate::leanh::lean_inc(v_cPos_x3f_1728_);
                        crate::leanh::lean_inc_ref(v_pos_1727_);
                        v_pos_1705_ = v_pos_1727_;
                        v_cPos_x3f_1706_ = v_cPos_x3f_1728_;
                        v_id_x3f_1707_ = v_id_x3f_1729_;
                        v___y_1708_ = v___x_1744_;
                        state = 9;
                        continue;
                    }
                } else {
                    v_acc_1651_ = v_acc_1723_;
                    state = 4;
                    continue;
                }
            }
            11 => {
                v_sortText_x3f_1747_ = crate::leanh::lean_ctor_get(v___x_1649_, 5);
                if crate::leanh::lean_obj_tag(v_sortText_x3f_1747_) == 1 {
                    v_val_1748_ = crate::leanh::lean_ctor_get(v_sortText_x3f_1747_, 0);
                    v___x_1749_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__2;
                    v_acc_1750_ = lean_string_append(v_acc_1746_, v___x_1749_);
                    v___x_1751_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1;
                    v_acc_1752_ = lean_string_append(v_acc_1750_, v___x_1751_);
                    v___x_1753_ =
                        l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_val_1748_);
                    if v___x_1753_ == 0 {
                        v___x_1754_ = lean_string_append(v_acc_1752_, v_val_1748_);
                        v___x_1755_ = lean_string_append(v___x_1754_, v___x_1751_);
                        v_acc_1723_ = v___x_1755_;
                        state = 10;
                        continue;
                    } else {
                        v___x_1756_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1757_ = lean_string_utf8_byte_size(v_val_1748_);
                        crate::leanh::lean_inc(v_val_1748_);
                        v___x_1758_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1758_, 0, v_val_1748_);
                        crate::leanh::lean_ctor_set(v___x_1758_, 1, v___x_1756_);
                        crate::leanh::lean_ctor_set(v___x_1758_, 2, v___x_1757_);
                        v___x_1759_ = l_String_Slice_positions(v___x_1758_);
                        v___x_1760_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_1758_, v_val_1748_, v___x_1759_, v_acc_1752_);
                        crate::leanh::lean_dec_ref_known(v___x_1758_, 3);
                        v___x_1761_ = lean_string_append(v___x_1760_, v___x_1751_);
                        v_acc_1723_ = v___x_1761_;
                        state = 10;
                        continue;
                    }
                } else {
                    v_acc_1723_ = v_acc_1746_;
                    state = 10;
                    continue;
                }
            }
            12 => {
                v_textEdit_x3f_1764_ = crate::leanh::lean_ctor_get(v___x_1649_, 4);
                if crate::leanh::lean_obj_tag(v_textEdit_x3f_1764_) == 1 {
                    v_val_1765_ = crate::leanh::lean_ctor_get(v_textEdit_x3f_1764_, 0);
                    v_insert_1766_ = crate::leanh::lean_ctor_get(v_val_1765_, 1);
                    v_end_1767_ = crate::leanh::lean_ctor_get(v_insert_1766_, 1);
                    v_start_1768_ = crate::leanh::lean_ctor_get(v_insert_1766_, 0);
                    v_replace_1769_ = crate::leanh::lean_ctor_get(v_val_1765_, 2);
                    v_end_1770_ = crate::leanh::lean_ctor_get(v_replace_1769_, 1);
                    v_start_1771_ = crate::leanh::lean_ctor_get(v_replace_1769_, 0);
                    v_newText_1772_ = crate::leanh::lean_ctor_get(v_val_1765_, 0);
                    v_line_1773_ = crate::leanh::lean_ctor_get(v_end_1767_, 0);
                    v_character_1774_ = crate::leanh::lean_ctor_get(v_end_1767_, 1);
                    v_line_1775_ = crate::leanh::lean_ctor_get(v_start_1768_, 0);
                    v_character_1776_ = crate::leanh::lean_ctor_get(v_start_1768_, 1);
                    v_line_1777_ = crate::leanh::lean_ctor_get(v_end_1770_, 0);
                    v_character_1778_ = crate::leanh::lean_ctor_get(v_end_1770_, 1);
                    v_line_1779_ = crate::leanh::lean_ctor_get(v_start_1771_, 0);
                    v_character_1780_ = crate::leanh::lean_ctor_get(v_start_1771_, 1);
                    v___x_1781_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__3;
                    v_acc_1782_ = lean_string_append(v_acc_1763_, v___x_1781_);
                    v___x_1783_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__0;
                    v_acc_1784_ = lean_string_append(v_acc_1782_, v___x_1783_);
                    v___x_1785_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__0;
                    v_acc_1786_ = lean_string_append(v_acc_1784_, v___x_1785_);
                    v___x_1787_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0;
                    v___x_1788_ = lean_string_append(v_acc_1786_, v___x_1787_);
                    crate::leanh::lean_inc(v_character_1774_);
                    v___x_1789_ = l_Nat_reprFast(v_character_1774_);
                    v___x_1790_ = lean_string_append(v___x_1788_, v___x_1789_);
                    crate::leanh::lean_dec_ref(v___x_1789_);
                    v___x_1791_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1;
                    v___x_1792_ = lean_string_append(v___x_1790_, v___x_1791_);
                    crate::leanh::lean_inc(v_line_1773_);
                    v___x_1793_ = l_Nat_reprFast(v_line_1773_);
                    v___x_1794_ = lean_string_append(v___x_1792_, v___x_1793_);
                    crate::leanh::lean_dec_ref(v___x_1793_);
                    v___x_1795_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0;
                    v_acc_1796_ = lean_string_append(v___x_1794_, v___x_1795_);
                    v___x_1797_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__1;
                    v_acc_1798_ = lean_string_append(v_acc_1796_, v___x_1797_);
                    v___x_1799_ = lean_string_append(v_acc_1798_, v___x_1787_);
                    crate::leanh::lean_inc(v_character_1776_);
                    v___x_1800_ = l_Nat_reprFast(v_character_1776_);
                    v___x_1801_ = lean_string_append(v___x_1799_, v___x_1800_);
                    crate::leanh::lean_dec_ref(v___x_1800_);
                    v___x_1802_ = lean_string_append(v___x_1801_, v___x_1791_);
                    crate::leanh::lean_inc(v_line_1775_);
                    v___x_1803_ = l_Nat_reprFast(v_line_1775_);
                    v___x_1804_ = lean_string_append(v___x_1802_, v___x_1803_);
                    crate::leanh::lean_dec_ref(v___x_1803_);
                    v_acc_1805_ = lean_string_append(v___x_1804_, v___x_1795_);
                    v_acc_1806_ = lean_string_append(v_acc_1805_, v___x_1795_);
                    v___x_1807_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__1;
                    v___x_1808_ = lean_string_append(v_acc_1806_, v___x_1807_);
                    v___x_1809_ = lean_string_append(v___x_1808_, v_newText_1772_);
                    v___x_1810_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1;
                    v_acc_1811_ = lean_string_append(v___x_1809_, v___x_1810_);
                    v___x_1812_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__2;
                    v_acc_1813_ = lean_string_append(v_acc_1811_, v___x_1812_);
                    v_acc_1814_ = lean_string_append(v_acc_1813_, v___x_1785_);
                    v___x_1815_ = lean_string_append(v_acc_1814_, v___x_1787_);
                    crate::leanh::lean_inc(v_character_1778_);
                    v___x_1816_ = l_Nat_reprFast(v_character_1778_);
                    v___x_1817_ = lean_string_append(v___x_1815_, v___x_1816_);
                    crate::leanh::lean_dec_ref(v___x_1816_);
                    v___x_1818_ = lean_string_append(v___x_1817_, v___x_1791_);
                    crate::leanh::lean_inc(v_line_1777_);
                    v___x_1819_ = l_Nat_reprFast(v_line_1777_);
                    v___x_1820_ = lean_string_append(v___x_1818_, v___x_1819_);
                    crate::leanh::lean_dec_ref(v___x_1819_);
                    v_acc_1821_ = lean_string_append(v___x_1820_, v___x_1795_);
                    v_acc_1822_ = lean_string_append(v_acc_1821_, v___x_1797_);
                    v___x_1823_ = lean_string_append(v_acc_1822_, v___x_1787_);
                    crate::leanh::lean_inc(v_character_1780_);
                    v___x_1824_ = l_Nat_reprFast(v_character_1780_);
                    v___x_1825_ = lean_string_append(v___x_1823_, v___x_1824_);
                    crate::leanh::lean_dec_ref(v___x_1824_);
                    v___x_1826_ = lean_string_append(v___x_1825_, v___x_1791_);
                    crate::leanh::lean_inc(v_line_1779_);
                    v___x_1827_ = l_Nat_reprFast(v_line_1779_);
                    v___x_1828_ = lean_string_append(v___x_1826_, v___x_1827_);
                    crate::leanh::lean_dec_ref(v___x_1827_);
                    v_acc_1829_ = lean_string_append(v___x_1828_, v___x_1795_);
                    v_acc_1830_ = lean_string_append(v_acc_1829_, v___x_1795_);
                    v_acc_1831_ = lean_string_append(v_acc_1830_, v___x_1795_);
                    v_acc_1746_ = v_acc_1831_;
                    state = 11;
                    continue;
                } else {
                    v_acc_1746_ = v_acc_1763_;
                    state = 11;
                    continue;
                }
            }
            13 => {
                v_kind_x3f_1834_ = crate::leanh::lean_ctor_get(v___x_1649_, 3);
                if crate::leanh::lean_obj_tag(v_kind_x3f_1834_) == 1 {
                    v_val_1835_ = crate::leanh::lean_ctor_get(v_kind_x3f_1834_, 0);
                    v___x_1836_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__4;
                    v___x_1837_ = lean_string_append(v_acc_1833_, v___x_1836_);
                    v___x_1838_ = (crate::leanh::lean_unbox(v_val_1835_) as u8);
                    v___x_1839_ = l_Lean_Lsp_CompletionItemKind_ctorIdx(v___x_1838_);
                    v___x_1840_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1841_ = lean_nat_add(v___x_1839_, v___x_1840_);
                    crate::leanh::lean_dec(v___x_1839_);
                    v___x_1842_ = l_Nat_reprFast(v___x_1841_);
                    v_acc_1843_ = lean_string_append(v___x_1837_, v___x_1842_);
                    crate::leanh::lean_dec_ref(v___x_1842_);
                    v_acc_1763_ = v_acc_1843_;
                    state = 12;
                    continue;
                } else {
                    v_acc_1763_ = v_acc_1833_;
                    state = 12;
                    continue;
                }
            }
            14 => {
                v___x_1846_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0;
                v___x_1847_ = lean_string_append(v___y_1845_, v___x_1846_);
                v_acc_1833_ = v___x_1847_;
                state = 13;
                continue;
            }
            15 => {
                v___x_1852_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__1;
                v___x_1853_ = lean_string_append(v___y_1849_, v___x_1852_);
                v___x_1854_ = lean_string_append(v___x_1853_, v___y_1851_);
                v___x_1855_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__2;
                v_acc_1856_ = lean_string_append(v___x_1854_, v___x_1855_);
                v___x_1857_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1;
                v_acc_1858_ = lean_string_append(v_acc_1856_, v___x_1857_);
                v___x_1859_ =
                    l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_value_1850_);
                if v___x_1859_ == 0 {
                    v___x_1860_ = lean_string_append(v_acc_1858_, v_value_1850_);
                    crate::leanh::lean_dec_ref(v_value_1850_);
                    v___x_1861_ = lean_string_append(v___x_1860_, v___x_1857_);
                    v___y_1845_ = v___x_1861_;
                    state = 14;
                    continue;
                } else {
                    v___x_1862_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1863_ = lean_string_utf8_byte_size(v_value_1850_);
                    crate::leanh::lean_inc_ref(v_value_1850_);
                    v___x_1864_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1864_, 0, v_value_1850_);
                    crate::leanh::lean_ctor_set(v___x_1864_, 1, v___x_1862_);
                    crate::leanh::lean_ctor_set(v___x_1864_, 2, v___x_1863_);
                    v___x_1865_ = l_String_Slice_positions(v___x_1864_);
                    v___x_1866_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_1864_, v_value_1850_, v___x_1865_, v_acc_1858_);
                    crate::leanh::lean_dec_ref(v_value_1850_);
                    crate::leanh::lean_dec_ref_known(v___x_1864_, 3);
                    v___x_1867_ = lean_string_append(v___x_1866_, v___x_1857_);
                    v___y_1845_ = v___x_1867_;
                    state = 14;
                    continue;
                }
            }
            16 => {
                v_documentation_x3f_1870_ = crate::leanh::lean_ctor_get(v___x_1649_, 2);
                if crate::leanh::lean_obj_tag(v_documentation_x3f_1870_) == 1 {
                    v_val_1871_ = crate::leanh::lean_ctor_get(v_documentation_x3f_1870_, 0);
                    v_kind_1872_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_1871_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v_value_1873_ = crate::leanh::lean_ctor_get(v_val_1871_, 0);
                    v___x_1874_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__5;
                    v_acc_1875_ = lean_string_append(v_acc_1869_, v___x_1874_);
                    if v_kind_1872_ == 0 {
                        v___x_1876_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__3;
                        crate::leanh::lean_inc_ref(v_value_1873_);
                        v___y_1849_ = v_acc_1875_;
                        v_value_1850_ = v_value_1873_;
                        v___y_1851_ = v___x_1876_;
                        state = 15;
                        continue;
                    } else {
                        v___x_1877_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__4;
                        crate::leanh::lean_inc_ref(v_value_1873_);
                        v___y_1849_ = v_acc_1875_;
                        v_value_1850_ = v_value_1873_;
                        v___y_1851_ = v___x_1877_;
                        state = 15;
                        continue;
                    }
                } else {
                    v_acc_1833_ = v_acc_1869_;
                    state = 13;
                    continue;
                }
            }
            17 => {
                v_detail_x3f_1880_ = crate::leanh::lean_ctor_get(v___x_1649_, 1);
                if crate::leanh::lean_obj_tag(v_detail_x3f_1880_) == 1 {
                    v_val_1881_ = crate::leanh::lean_ctor_get(v_detail_x3f_1880_, 0);
                    v___x_1882_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__6;
                    v_acc_1883_ = lean_string_append(v___y_1879_, v___x_1882_);
                    v___x_1884_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1;
                    v_acc_1885_ = lean_string_append(v_acc_1883_, v___x_1884_);
                    v___x_1886_ =
                        l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_val_1881_);
                    if v___x_1886_ == 0 {
                        v___x_1887_ = lean_string_append(v_acc_1885_, v_val_1881_);
                        v___x_1888_ = lean_string_append(v___x_1887_, v___x_1884_);
                        v_acc_1869_ = v___x_1888_;
                        state = 16;
                        continue;
                    } else {
                        v___x_1889_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1890_ = lean_string_utf8_byte_size(v_val_1881_);
                        crate::leanh::lean_inc(v_val_1881_);
                        v___x_1891_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1891_, 0, v_val_1881_);
                        crate::leanh::lean_ctor_set(v___x_1891_, 1, v___x_1889_);
                        crate::leanh::lean_ctor_set(v___x_1891_, 2, v___x_1890_);
                        v___x_1892_ = l_String_Slice_positions(v___x_1891_);
                        v___x_1893_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_1891_, v_val_1881_, v___x_1892_, v_acc_1885_);
                        crate::leanh::lean_dec_ref_known(v___x_1891_, 3);
                        v___x_1894_ = lean_string_append(v___x_1893_, v___x_1884_);
                        v_acc_1869_ = v___x_1894_;
                        state = 16;
                        continue;
                    }
                } else {
                    v_acc_1869_ = v___y_1879_;
                    state = 16;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast___boxed(
    mut v_acc_1909_: *mut crate::leanh::LeanObject,
    mut v_items_1910_: *mut crate::leanh::LeanObject,
    mut v_i_1911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1912_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast(v_acc_1909_, v_items_1910_, v_i_1911_);
    crate::leanh::lean_dec_ref(v_items_1910_);
    return v_res_1912_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0(
    mut v___x_1913_: *mut crate::leanh::LeanObject,
    mut v___x_1914_: *mut crate::leanh::LeanObject,
    mut v_inst_1915_: *mut crate::leanh::LeanObject,
    mut v_R_1916_: *mut crate::leanh::LeanObject,
    mut v_a_1917_: *mut crate::leanh::LeanObject,
    mut v_b_1918_: *mut crate::leanh::LeanObject,
    mut v_c_1919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1920_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_1913_, v___x_1914_, v_a_1917_, v_b_1918_);
    return v___x_1920_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___boxed(
    mut v___x_1921_: *mut crate::leanh::LeanObject,
    mut v___x_1922_: *mut crate::leanh::LeanObject,
    mut v_inst_1923_: *mut crate::leanh::LeanObject,
    mut v_R_1924_: *mut crate::leanh::LeanObject,
    mut v_a_1925_: *mut crate::leanh::LeanObject,
    mut v_b_1926_: *mut crate::leanh::LeanObject,
    mut v_c_1927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1928_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0(v___x_1921_, v___x_1922_, v_inst_1923_, v_R_1924_, v_a_1925_, v_b_1926_, v_c_1927_);
    crate::leanh::lean_dec_ref(v___x_1922_);
    crate::leanh::lean_dec_ref(v___x_1921_);
    return v_res_1928_;
}
pub unsafe fn l_Lean_Lsp_ResolvableCompletionList_compressFast(
    mut v_l_1934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isIncomplete_1935_: u8 = 0;
    let mut v_items_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isIncomplete_1935_ = crate::leanh::lean_ctor_get_uint8(
                    v_l_1934_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_items_1936_ = crate::leanh::lean_ctor_get(v_l_1934_, 0);
                v___x_1937_ = l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__0;
                if v_isIncomplete_1935_ == 0 {
                    v___x_1947_ = l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__3;
                    v___y_1939_ = v___x_1947_;
                    state = 1;
                    continue;
                } else {
                    v___x_1948_ = l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__4;
                    v___y_1939_ = v___x_1948_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1940_ = lean_string_append(v___x_1937_, v___y_1939_);
                v___x_1941_ = l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__1;
                v_acc_1942_ = lean_string_append(v___x_1940_, v___x_1941_);
                v___x_1943_ = crate::leanh::lean_unsigned_to_nat(0);
                v_acc_1944_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast(v_acc_1942_, v_items_1936_, v___x_1943_);
                v___x_1945_ = l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__2;
                v___x_1946_ = lean_string_append(v_acc_1944_, v___x_1945_);
                return v___x_1946_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_ResolvableCompletionList_compressFast___boxed(
    mut v_l_1949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1950_ = l_Lean_Lsp_ResolvableCompletionList_compressFast(v_l_1949_);
    crate::leanh::lean_dec_ref(v_l_1949_);
    return v_res_1950_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_Completion_CompletionItemCompression(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Lsp_LanguageFeatures(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_Completion_CompletionItemCompression(
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
pub unsafe fn initialize_Lean_Server_Completion_CompletionItemCompression(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Lsp_LanguageFeatures(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Completion_CompletionItemCompression(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_Completion_CompletionItemCompression(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Server_Completion_CompletionItemCompression(builtin);
}

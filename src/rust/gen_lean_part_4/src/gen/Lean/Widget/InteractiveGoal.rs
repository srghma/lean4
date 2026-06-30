// Lean compiler output
// Module: Lean.Widget.InteractiveGoal
// Imports: Lean.Widget.InteractiveCode Lean.Data.Lsp.Extra
use crate::ffi::{
    lean_array_get, lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_to_list, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv,
    lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_nat_to_int, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_string_append, lean_string_dec_eq, lean_usize_add,
    lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l_Array_append___redArg, l_List_foldl___at___00Array_appendList_spec__0___redArg,
};
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_isNil;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::String::Defs::l_String_intercalate;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::lean_erase_macro_scopes;
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getBool_x3f, l_Lean_Json_getObjValD, l_Lean_Json_getStr_x3f, l_Lean_Json_mkObj,
};
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::{
    l_Lean_Json_getTag_x3f, l_Lean_Json_parseCtorFields, l_Lean_Name_fromJson_x3f,
};
use crate::r#gen::Lean::Data::Json::Printer::l_Lean_Json_pretty;
use crate::r#gen::Lean::Data::Lsp::BasicAux::{
    l_Lean_Lsp_instFromJsonRange_fromJson, l_Lean_Lsp_instToJsonRange_toJson,
};
use crate::r#gen::Lean::Data::Lsp::Extra::{
    initialize_Lean_Data_Lsp_Extra, runtime_initialize_Lean_Data_Lsp_Extra,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Position::l_Lean_instInhabitedFileMap_default;
use crate::r#gen::Lean::Exception::l_Lean_throwError___redArg;
use crate::r#gen::Lean::Expr::{l_Lean_Expr_hasMVar, l_Lean_Expr_isSort};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_sanitizeNames, l_Lean_LocalDecl_isAuxDecl,
    l_Lean_LocalDecl_isImplementationDetail,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofName, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp, l_Lean_Meta_isClass_x3f,
    l_Lean_Meta_withLCtx___redArg,
};
use crate::r#gen::Lean::Meta::PPGoal::{
    l_Lean_Meta_getGoalPrefix, l_Lean_Meta_pp_auxDecls, l_Lean_Meta_pp_implementationDetailHyps,
    l_Lean_Meta_ppGoal_shouldShowLetValue___redArg,
};
use crate::r#gen::Lean::MetavarContext::{
    l_Lean_MetavarContext_findDecl_x3f, l_Lean_MetavarKind_isSyntheticOpaque,
    l_Lean_instantiateMVarsCore,
};
use crate::r#gen::Lean::PrettyPrinter::Delaborator::Basic::{
    l_Lean_PrettyPrinter_Delaborator_delab___boxed,
    l_Lean_PrettyPrinter_Delaborator_omission___boxed,
};
use crate::r#gen::Lean::Server::Rpc::Basic::{
    l_Lean_Server_WithRpcRef_mk___redArg,
    l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg,
    l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg,
};
use crate::r#gen::Lean::Widget::Basic::{
    l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_173954553____hygCtx___hyg_3_,
    l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_2318528980____hygCtx___hyg_3_,
};
use crate::r#gen::Lean::Widget::InteractiveCode::{
    initialize_Lean_Widget_InteractiveCode,
    l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1____boxed,
    l_Lean_Widget_instRpcEncodableSubexprInfo_enc_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_,
    l_Lean_Widget_ppExprTagged, runtime_initialize_Lean_Widget_InteractiveCode,
};
use crate::r#gen::Lean::Widget::TaggedText::{
    l_Lean_Widget_TaggedText_stripTags___redArg, l_Lean_Widget_instInhabitedTaggedText_default,
};
pub static l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__0_value:
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
static mut l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Widget_instInhabitedInteractiveHypothesisBundle:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1_spec__1___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [110, 97, 109, 101, 115, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [102, 118, 97, 114, 73, 100, 115, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 121, 112, 101, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [118, 97, 108, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 115, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 115, 84, 121, 112, 101, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 115, 73, 110, 115, 101, 114, 116, 101, 100, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 115, 82, 101, 109, 111, 118, 101, 100, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Widget_instToJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 101, 120, 116, 0]};
static mut l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 112, 112, 101, 110, 100, 0]};
static mut l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [116, 97, 103, 0]};
static mut l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc___closed__0_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableSubexprInfo_enc_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc___closed__0_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc___closed__0_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__value) as *mut leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0___closed__0_value: leanh::LeanStringObject<27> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 32, 97, 114, 114, 97, 121, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0___closed__1_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__0_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 97, 103, 32, 102, 111, 117, 110, 100, 0]};
static mut l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__2_value: leanh::LeanStringObject<33> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 109, 97, 116, 99, 104, 101, 100, 0]};
static mut l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__2_value) as *mut leanh::LeanObject] };
static mut l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec___closed__0_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec___closed__0_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec___closed__0_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle___closed__0_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle___closed__1_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle___closed__2_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 121, 112, 115, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [99, 116, 120, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [117, 115, 101, 114, 78, 97, 109, 101, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [103, 111, 97, 108, 80, 114, 101, 102, 105, 120, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 118, 97, 114, 73, 100, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_45__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_45____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_45_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_45__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Widget_instToJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_45_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_45__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveGoal___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableInteractiveGoal_enc_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableInteractiveGoal___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveGoal___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveGoal___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableInteractiveGoal_dec_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableInteractiveGoal___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveGoal___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveGoal___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveGoal___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveGoal___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instRpcEncodableInteractiveGoal___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveGoal___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Widget_instRpcEncodableInteractiveGoal: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveGoal___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [114, 97, 110, 103, 101, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 101, 114, 109, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_36__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_36____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_36_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_36__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Widget_instToJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_36_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_36__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveTermGoal___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableInteractiveTermGoal_enc_00___x40_Lean_Widget_InteractiveGoal_2553565095____hygCtx___hyg_1_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableInteractiveTermGoal___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveTermGoal___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveTermGoal___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableInteractiveTermGoal_dec_00___x40_Lean_Widget_InteractiveGoal_2553565095____hygCtx___hyg_1____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableInteractiveTermGoal___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveTermGoal___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveTermGoal___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveTermGoal___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveTermGoal___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instRpcEncodableInteractiveTermGoal___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveTermGoal___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Widget_instRpcEncodableInteractiveTermGoal: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveTermGoal___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_List_filterTR_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_filterTR_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__1_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__2_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__3_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 58, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__4_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__3_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__5_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 58, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__6_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__7_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 58, 61, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__8_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__7_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__9_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__10_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__9_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__10_value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_InteractiveGoalCore_pretty___closed__0_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [99, 97, 115, 101, 32, 0],
};
static mut l_Lean_Widget_InteractiveGoalCore_pretty___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_InteractiveGoalCore_pretty___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_InteractiveGoalCore_pretty___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_InteractiveGoalCore_pretty___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_InteractiveGoalCore_pretty___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_InteractiveGoalCore_pretty___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_InteractiveTermGoal_pretty___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 2,
    m_data: [226, 138, 162, 32, 0],
};
static mut l_Lean_Widget_InteractiveTermGoal_pretty___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_InteractiveTermGoal_pretty___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 111, 97, 108, 115, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_28__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_28_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_28_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_28__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Widget_instToJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_28_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_28__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveGoals___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableInteractiveGoals_enc_00___x40_Lean_Widget_InteractiveGoal_1490754142____hygCtx___hyg_1_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableInteractiveGoals___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveGoals___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveGoals___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableInteractiveGoals_dec_00___x40_Lean_Widget_InteractiveGoal_1490754142____hygCtx___hyg_1____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableInteractiveGoals___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveGoals___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveGoals___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveGoals___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveGoals___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instRpcEncodableInteractiveGoals___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveGoals___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Widget_instRpcEncodableInteractiveGoals: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveGoals___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instAppendInteractiveGoals___closed__0_value:
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
    m_fun: l_Lean_Widget_InteractiveGoals_append___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Widget_instAppendInteractiveGoals___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instAppendInteractiveGoals___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Widget_instAppendInteractiveGoals: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instAppendInteractiveGoals___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instEmptyCollectionInteractiveGoals___closed__0_value:
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
static mut l_Lean_Widget_instEmptyCollectionInteractiveGoals___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instEmptyCollectionInteractiveGoals___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Widget_instEmptyCollectionInteractiveGoals: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instEmptyCollectionInteractiveGoals___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged___closed__0_value: leanh::LeanStringObject<113> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 113, m_capacity: 113, m_length: 112, m_data: [86, 97, 108, 117, 101, 32, 111, 109, 105, 116, 116, 101, 100, 32, 115, 105, 110, 99, 101, 32, 96, 112, 112, 46, 115, 104, 111, 119, 76, 101, 116, 86, 97, 108, 117, 101, 115, 96, 32, 105, 115, 32, 102, 97, 108, 115, 101, 32, 97, 110, 100, 32, 116, 104, 101, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 39, 115, 32, 100, 101, 112, 116, 104, 32, 101, 120, 99, 101, 101, 100, 115, 32, 96, 112, 112, 46, 115, 104, 111, 119, 76, 101, 116, 86, 97, 108, 117, 101, 115, 46, 116, 104, 114, 101, 115, 104, 111, 108, 100, 96, 46, 0]};
static mut l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged___closed__1_value: leanh::LeanStringObject<158> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 158, m_capacity: 158, m_length: 157, m_data: [86, 97, 108, 117, 101, 32, 111, 109, 105, 116, 116, 101, 100, 32, 115, 105, 110, 99, 101, 32, 96, 112, 112, 46, 115, 104, 111, 119, 76, 101, 116, 86, 97, 108, 117, 101, 115, 96, 32, 105, 115, 32, 102, 97, 108, 115, 101, 32, 97, 110, 100, 32, 116, 104, 101, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 39, 115, 32, 100, 101, 112, 116, 104, 32, 101, 120, 99, 101, 101, 100, 115, 32, 98, 111, 116, 104, 32, 96, 112, 112, 46, 115, 104, 111, 119, 76, 101, 116, 86, 97, 108, 117, 101, 115, 46, 116, 97, 99, 116, 105, 99, 46, 116, 104, 114, 101, 115, 104, 111, 108, 100, 96, 32, 97, 110, 100, 32, 96, 112, 112, 46, 115, 104, 111, 119, 76, 101, 116, 86, 97, 108, 117, 101, 115, 46, 116, 104, 114, 101, 115, 104, 111, 108, 100, 96, 46, 0]};
static mut l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Delaborator_delab___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_addInteractiveHypothesisBundle___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Widget_addInteractiveHypothesisBundle___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_addInteractiveHypothesisBundle___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_addInteractiveHypothesisBundle___closed__1_value:
    leanh::LeanStringObject<72> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 72,
    m_capacity: 72,
    m_length: 71,
    m_data: [
        67, 97, 110, 32, 111, 110, 108, 121, 32, 97, 100, 100, 32, 97, 32, 110, 111, 110, 122, 101,
        114, 111, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 105, 100, 115, 32, 97, 115,
        32, 97, 110, 32, 73, 110, 116, 101, 114, 97, 99, 116, 105, 118, 101, 72, 121, 112, 111,
        116, 104, 101, 115, 105, 115, 66, 117, 110, 100, 108, 101, 46, 0,
    ],
};
static mut l_Lean_Widget_addInteractiveHypothesisBundle___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_addInteractiveHypothesisBundle___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Widget_addInteractiveHypothesisBundle___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_addInteractiveHypothesisBundle___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Widget_withGoalCtx___redArg___lam__1___closed__0_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        117, 110, 107, 110, 111, 119, 110, 32, 103, 111, 97, 108, 32, 0,
    ],
};
static mut l_Lean_Widget_withGoalCtx___redArg___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_withGoalCtx___redArg___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Widget_withGoalCtx___redArg___lam__1___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_withGoalCtx___redArg___lam__1___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4_spec__9___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4_spec__9___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4_spec__9___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_goalToInteractive___lam__0___closed__0_value:
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
static mut l_Lean_Widget_goalToInteractive___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_goalToInteractive___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_goalToInteractive___lam__0___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4_spec__9___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Widget_goalToInteractive___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_goalToInteractive___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_goalToInteractive___lam__0___closed__2_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4_spec__9___closed__0_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_goalToInteractive___lam__0___closed__1_value) as *mut leanh::LeanObject] };
static mut l_Lean_Widget_goalToInteractive___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_goalToInteractive___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3946_ = l_Lean_Widget_instInhabitedTaggedText_default(leanh::lean_box(0));
    return v___x_3946_;
}
pub unsafe fn _init_l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3947_ = leanh::lean_box(0);
    v___x_3948_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__1_once
        ),
        _init_l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__1,
    );
    v___x_3949_ = l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__0;
    v___x_3950_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
    leanh::lean_ctor_set(v___x_3950_, 0, v___x_3949_);
    leanh::lean_ctor_set(v___x_3950_, 1, v___x_3949_);
    leanh::lean_ctor_set(v___x_3950_, 2, v___x_3948_);
    leanh::lean_ctor_set(v___x_3950_, 3, v___x_3947_);
    leanh::lean_ctor_set(v___x_3950_, 4, v___x_3947_);
    leanh::lean_ctor_set(v___x_3950_, 5, v___x_3947_);
    leanh::lean_ctor_set(v___x_3950_, 6, v___x_3947_);
    leanh::lean_ctor_set(v___x_3950_, 7, v___x_3947_);
    return v___x_3950_;
}
pub unsafe fn _init_l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default()
-> *mut leanh::LeanObject {
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3951_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__2_once
        ),
        _init_l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__2,
    );
    return v___x_3951_;
}
pub unsafe fn _init_l_Lean_Widget_instInhabitedInteractiveHypothesisBundle()
-> *mut leanh::LeanObject {
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3952_ = l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default;
    return v___x_3952_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(
    mut v_j_3953_: *mut leanh::LeanObject,
    mut v_k_3954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3955_ = l_Lean_Json_getObjValD(v_j_3953_, v_k_3954_);
    v___x_3956_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3956_, 0, v___x_3955_);
    return v___x_3956_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0___boxed(
    mut v_j_3957_: *mut leanh::LeanObject,
    mut v_k_3958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3959_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_j_3957_, v_k_3958_);
    leanh::lean_dec_ref(v_k_3958_);
    return v_res_3959_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1_spec__1(
    mut v_x_3962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3962_) == 0 {
        let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3963_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1_spec__1___closed__0;
        return v___x_3963_;
    } else {
        let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3964_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3964_, 0, v_x_3962_);
        v___x_3965_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3965_, 0, v___x_3964_);
        return v___x_3965_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1(
    mut v_j_3966_: *mut leanh::LeanObject,
    mut v_k_3967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3968_ = l_Lean_Json_getObjValD(v_j_3966_, v_k_3967_);
    v___x_3969_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1_spec__1(v___x_3968_);
    return v___x_3969_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1___boxed(
    mut v_j_3970_: *mut leanh::LeanObject,
    mut v_k_3971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3972_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1(v_j_3970_, v_k_3971_);
    leanh::lean_dec_ref(v_k_3971_);
    return v_res_3972_;
}
pub unsafe fn l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_(
    mut v_json_3981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4008_: u8 = 0;
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4013_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3982_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
                leanh::lean_inc_n(v_json_3981_, 7);
                v___x_3983_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_3981_, v___x_3982_);
                v_a_3984_ = leanh::lean_ctor_get(v___x_3983_, 0);
                leanh::lean_inc(v_a_3984_);
                leanh::lean_dec_ref(v___x_3983_);
                v___x_3985_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
                v___x_3986_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_3981_, v___x_3985_);
                v_a_3987_ = leanh::lean_ctor_get(v___x_3986_, 0);
                leanh::lean_inc(v_a_3987_);
                leanh::lean_dec_ref(v___x_3986_);
                v___x_3988_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
                v___x_3989_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_3981_, v___x_3988_);
                v_a_3990_ = leanh::lean_ctor_get(v___x_3989_, 0);
                leanh::lean_inc(v_a_3990_);
                leanh::lean_dec_ref(v___x_3989_);
                v___x_3991_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
                v___x_3992_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1(v_json_3981_, v___x_3991_);
                v_a_3993_ = leanh::lean_ctor_get(v___x_3992_, 0);
                leanh::lean_inc(v_a_3993_);
                leanh::lean_dec_ref(v___x_3992_);
                v___x_3994_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
                v___x_3995_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1(v_json_3981_, v___x_3994_);
                v_a_3996_ = leanh::lean_ctor_get(v___x_3995_, 0);
                leanh::lean_inc(v_a_3996_);
                leanh::lean_dec_ref(v___x_3995_);
                v___x_3997_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
                v___x_3998_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1(v_json_3981_, v___x_3997_);
                v_a_3999_ = leanh::lean_ctor_get(v___x_3998_, 0);
                leanh::lean_inc(v_a_3999_);
                leanh::lean_dec_ref(v___x_3998_);
                v___x_4000_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
                v___x_4001_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1(v_json_3981_, v___x_4000_);
                v_a_4002_ = leanh::lean_ctor_get(v___x_4001_, 0);
                leanh::lean_inc(v_a_4002_);
                leanh::lean_dec_ref(v___x_4001_);
                v___x_4003_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
                v___x_4004_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1(v_json_3981_, v___x_4003_);
                v_a_4005_ = leanh::lean_ctor_get(v___x_4004_, 0);
                v_isSharedCheck_4013_ = (!leanh::lean_is_exclusive(v___x_4004_)) as u8;
                if v_isSharedCheck_4013_ == 0 {
                    v___x_4007_ = v___x_4004_;
                    v_isShared_4008_ = v_isSharedCheck_4013_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4005_);
                    leanh::lean_dec(v___x_4004_);
                    v___x_4007_ = leanh::lean_box(0);
                    v_isShared_4008_ = v_isSharedCheck_4013_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4009_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                leanh::lean_ctor_set(v___x_4009_, 0, v_a_3984_);
                leanh::lean_ctor_set(v___x_4009_, 1, v_a_3987_);
                leanh::lean_ctor_set(v___x_4009_, 2, v_a_3990_);
                leanh::lean_ctor_set(v___x_4009_, 3, v_a_3993_);
                leanh::lean_ctor_set(v___x_4009_, 4, v_a_3996_);
                leanh::lean_ctor_set(v___x_4009_, 5, v_a_3999_);
                leanh::lean_ctor_set(v___x_4009_, 6, v_a_4002_);
                leanh::lean_ctor_set(v___x_4009_, 7, v_a_4005_);
                if v_isShared_4008_ == 0 {
                    leanh::lean_ctor_set(v___x_4007_, 0, v___x_4009_);
                    v___x_4011_ = v___x_4007_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4012_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4012_, 0, v___x_4009_);
                    v___x_4011_ = v_reuseFailAlloc_4012_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4011_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__0(
    mut v_k_4016_: *mut leanh::LeanObject,
    mut v_x_4017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4017_) == 0 {
        let mut v___x_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_k_4016_);
        v___x_4018_ = leanh::lean_box(0);
        return v___x_4018_;
    } else {
        let mut v_val_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4019_ = leanh::lean_ctor_get(v_x_4017_, 0);
        leanh::lean_inc(v_val_4019_);
        v___x_4020_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4020_, 0, v_k_4016_);
        leanh::lean_ctor_set(v___x_4020_, 1, v_val_4019_);
        v___x_4021_ = leanh::lean_box(0);
        v___x_4022_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4022_, 0, v___x_4020_);
        leanh::lean_ctor_set(v___x_4022_, 1, v___x_4021_);
        return v___x_4022_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__0___boxed(
    mut v_k_4023_: *mut leanh::LeanObject,
    mut v_x_4024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4025_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__0(v_k_4023_, v_x_4024_);
    leanh::lean_dec(v_x_4024_);
    return v_res_4025_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__1(
    mut v_a_4026_: *mut leanh::LeanObject,
    mut v_a_4027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_4026_) == 0 {
                    v___x_4028_ = lean_array_to_list(v_a_4027_);
                    return v___x_4028_;
                } else {
                    v_head_4029_ = leanh::lean_ctor_get(v_a_4026_, 0);
                    leanh::lean_inc(v_head_4029_);
                    v_tail_4030_ = leanh::lean_ctor_get(v_a_4026_, 1);
                    leanh::lean_inc(v_tail_4030_);
                    leanh::lean_dec_ref_known(v_a_4026_, 2);
                    v___x_4031_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_4027_,
                        v_head_4029_,
                    );
                    v_a_4026_ = v_tail_4030_;
                    v_a_4027_ = v___x_4031_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47_(
    mut v_x_4035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_names_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarIds_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_x3f_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInstance_x3f_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isType_x3f_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInserted_x3f_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRemoved_x3f_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_names_4036_ = leanh::lean_ctor_get(v_x_4035_, 0);
    v_fvarIds_4037_ = leanh::lean_ctor_get(v_x_4035_, 1);
    v_type_4038_ = leanh::lean_ctor_get(v_x_4035_, 2);
    v_val_x3f_4039_ = leanh::lean_ctor_get(v_x_4035_, 3);
    v_isInstance_x3f_4040_ = leanh::lean_ctor_get(v_x_4035_, 4);
    v_isType_x3f_4041_ = leanh::lean_ctor_get(v_x_4035_, 5);
    v_isInserted_x3f_4042_ = leanh::lean_ctor_get(v_x_4035_, 6);
    v_isRemoved_x3f_4043_ = leanh::lean_ctor_get(v_x_4035_, 7);
    v___x_4044_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
    leanh::lean_inc(v_names_4036_);
    v___x_4045_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4045_, 0, v___x_4044_);
    leanh::lean_ctor_set(v___x_4045_, 1, v_names_4036_);
    v___x_4046_ = leanh::lean_box(0);
    v___x_4047_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4047_, 0, v___x_4045_);
    leanh::lean_ctor_set(v___x_4047_, 1, v___x_4046_);
    v___x_4048_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
    leanh::lean_inc(v_fvarIds_4037_);
    v___x_4049_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4049_, 0, v___x_4048_);
    leanh::lean_ctor_set(v___x_4049_, 1, v_fvarIds_4037_);
    v___x_4050_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4050_, 0, v___x_4049_);
    leanh::lean_ctor_set(v___x_4050_, 1, v___x_4046_);
    v___x_4051_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
    leanh::lean_inc(v_type_4038_);
    v___x_4052_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4052_, 0, v___x_4051_);
    leanh::lean_ctor_set(v___x_4052_, 1, v_type_4038_);
    v___x_4053_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4053_, 0, v___x_4052_);
    leanh::lean_ctor_set(v___x_4053_, 1, v___x_4046_);
    v___x_4054_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
    v___x_4055_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__0(v___x_4054_, v_val_x3f_4039_);
    v___x_4056_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
    v___x_4057_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__0(v___x_4056_, v_isInstance_x3f_4040_);
    v___x_4058_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
    v___x_4059_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__0(v___x_4058_, v_isType_x3f_4041_);
    v___x_4060_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
    v___x_4061_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__0(v___x_4060_, v_isInserted_x3f_4042_);
    v___x_4062_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
    v___x_4063_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__0(v___x_4062_, v_isRemoved_x3f_4043_);
    v___x_4064_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4064_, 0, v___x_4063_);
    leanh::lean_ctor_set(v___x_4064_, 1, v___x_4046_);
    v___x_4065_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4065_, 0, v___x_4061_);
    leanh::lean_ctor_set(v___x_4065_, 1, v___x_4064_);
    v___x_4066_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4066_, 0, v___x_4059_);
    leanh::lean_ctor_set(v___x_4066_, 1, v___x_4065_);
    v___x_4067_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4067_, 0, v___x_4057_);
    leanh::lean_ctor_set(v___x_4067_, 1, v___x_4066_);
    v___x_4068_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4068_, 0, v___x_4055_);
    leanh::lean_ctor_set(v___x_4068_, 1, v___x_4067_);
    v___x_4069_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4069_, 0, v___x_4053_);
    leanh::lean_ctor_set(v___x_4069_, 1, v___x_4068_);
    v___x_4070_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4070_, 0, v___x_4050_);
    leanh::lean_ctor_set(v___x_4070_, 1, v___x_4069_);
    v___x_4071_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4071_, 0, v___x_4047_);
    leanh::lean_ctor_set(v___x_4071_, 1, v___x_4070_);
    v___x_4072_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47_;
    v___x_4073_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__1(v___x_4071_, v___x_4072_);
    v___x_4074_ = l_Lean_Json_mkObj(v___x_4073_);
    leanh::lean_dec(v___x_4073_);
    return v___x_4074_;
}
pub unsafe fn l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47____boxed(
    mut v_x_4075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4076_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47_(v_x_4075_);
    leanh::lean_dec_ref(v_x_4075_);
    return v_res_4076_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3_spec__4(
    mut v_sz_4079_: usize,
    mut v_i_4080_: usize,
    mut v_bs_4081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4082_: u8 = 0;
    let mut v_v_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: usize = 0;
    let mut v___x_4087_: usize = 0;
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4082_ = lean_usize_dec_lt(v_i_4080_, v_sz_4079_);
                if v___x_4082_ == 0 {
                    return v_bs_4081_;
                } else {
                    v_v_4083_ = lean_array_uget(v_bs_4081_, v_i_4080_);
                    v___x_4084_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4085_ = lean_array_uset(v_bs_4081_, v_i_4080_, v___x_4084_);
                    v___x_4086_ = 1usize;
                    v___x_4087_ = lean_usize_add(v_i_4080_, v___x_4086_);
                    v___x_4088_ = lean_array_uset(v_bs_x27_4085_, v_i_4080_, v_v_4083_);
                    v_i_4080_ = v___x_4087_;
                    v_bs_4081_ = v___x_4088_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3_spec__4___boxed(
    mut v_sz_4090_: *mut leanh::LeanObject,
    mut v_i_4091_: *mut leanh::LeanObject,
    mut v_bs_4092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4093_: usize = 0;
    let mut v_i_boxed_4094_: usize = 0;
    let mut v_res_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4093_ = leanh::lean_unbox_usize(v_sz_4090_);
    leanh::lean_dec(v_sz_4090_);
    v_i_boxed_4094_ = leanh::lean_unbox_usize(v_i_4091_);
    leanh::lean_dec(v_i_4091_);
    v_res_4095_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3_spec__4(v_sz_boxed_4093_, v_i_boxed_4094_, v_bs_4092_);
    return v_res_4095_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3(
    mut v_a_4096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_4097_: usize = 0;
    let mut v___x_4098_: usize = 0;
    let mut v___x_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_4097_ = lean_array_size(v_a_4096_);
    v___x_4098_ = 0usize;
    v___x_4099_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3_spec__4(v_sz_4097_, v___x_4098_, v_a_4096_);
    v___x_4100_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4100_, 0, v___x_4099_);
    return v___x_4100_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0(
    mut v_sz_4101_: usize,
    mut v_i_4102_: usize,
    mut v_bs_4103_: *mut leanh::LeanObject,
    mut v___y_4104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4105_: u8 = 0;
    let mut v___x_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: usize = 0;
    let mut v___x_4112_: usize = 0;
    let mut v___x_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4105_ = lean_usize_dec_lt(v_i_4102_, v_sz_4101_);
                if v___x_4105_ == 0 {
                    v___x_4106_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4106_, 0, v_bs_4103_);
                    leanh::lean_ctor_set(v___x_4106_, 1, v___y_4104_);
                    return v___x_4106_;
                } else {
                    v_v_4107_ = lean_array_uget(v_bs_4103_, v_i_4102_);
                    v___x_4108_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4109_ = lean_array_uset(v_bs_4103_, v_i_4102_, v___x_4108_);
                    v___x_4110_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4110_, 0, v_v_4107_);
                    v___x_4111_ = 1usize;
                    v___x_4112_ = lean_usize_add(v_i_4102_, v___x_4111_);
                    v___x_4113_ = lean_array_uset(v_bs_x27_4109_, v_i_4102_, v___x_4110_);
                    v_i_4102_ = v___x_4112_;
                    v_bs_4103_ = v___x_4113_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0___boxed(
    mut v_sz_4115_: *mut leanh::LeanObject,
    mut v_i_4116_: *mut leanh::LeanObject,
    mut v_bs_4117_: *mut leanh::LeanObject,
    mut v___y_4118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4119_: usize = 0;
    let mut v_i_boxed_4120_: usize = 0;
    let mut v_res_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4119_ = leanh::lean_unbox_usize(v_sz_4115_);
    leanh::lean_dec(v_sz_4115_);
    v_i_boxed_4120_ = leanh::lean_unbox_usize(v_i_4116_);
    leanh::lean_dec(v_i_4116_);
    v_res_4121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0(v_sz_boxed_4119_, v_i_boxed_4120_, v_bs_4117_, v___y_4118_);
    return v_res_4121_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__1(
    mut v_sz_4122_: usize,
    mut v_i_4123_: usize,
    mut v_bs_4124_: *mut leanh::LeanObject,
    mut v___y_4125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4126_: u8 = 0;
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: usize = 0;
    let mut v___x_4134_: usize = 0;
    let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4126_ = lean_usize_dec_lt(v_i_4123_, v_sz_4122_);
                if v___x_4126_ == 0 {
                    v___x_4127_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4127_, 0, v_bs_4124_);
                    leanh::lean_ctor_set(v___x_4127_, 1, v___y_4125_);
                    return v___x_4127_;
                } else {
                    v_v_4128_ = lean_array_uget(v_bs_4124_, v_i_4123_);
                    v___x_4129_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4130_ = lean_array_uset(v_bs_4124_, v_i_4123_, v___x_4129_);
                    v___x_4131_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_v_4128_,
                        v___x_4126_,
                    );
                    v___x_4132_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4132_, 0, v___x_4131_);
                    v___x_4133_ = 1usize;
                    v___x_4134_ = lean_usize_add(v_i_4123_, v___x_4133_);
                    v___x_4135_ = lean_array_uset(v_bs_x27_4130_, v_i_4123_, v___x_4132_);
                    v_i_4123_ = v___x_4134_;
                    v_bs_4124_ = v___x_4135_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__1___boxed(
    mut v_sz_4137_: *mut leanh::LeanObject,
    mut v_i_4138_: *mut leanh::LeanObject,
    mut v_bs_4139_: *mut leanh::LeanObject,
    mut v___y_4140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4141_: usize = 0;
    let mut v_i_boxed_4142_: usize = 0;
    let mut v_res_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4141_ = leanh::lean_unbox_usize(v_sz_4137_);
    leanh::lean_dec(v_sz_4137_);
    v_i_boxed_4142_ = leanh::lean_unbox_usize(v_i_4138_);
    leanh::lean_dec(v_i_4138_);
    v_res_4143_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__1(v_sz_boxed_4141_, v_i_boxed_4142_, v_bs_4139_, v___y_4140_);
    return v_res_4143_;
}
pub unsafe fn l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(
    mut v_x_4147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4151_: u8 = 0;
    let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4160_: u8 = 0;
    let mut v_a_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4172_: u8 = 0;
    let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4186_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_4147_) {
                0 => {
                    v_a_4148_ = leanh::lean_ctor_get(v_x_4147_, 0);
                    v_isSharedCheck_4160_ = (!leanh::lean_is_exclusive(v_x_4147_)) as u8;
                    if v_isSharedCheck_4160_ == 0 {
                        v___x_4150_ = v_x_4147_;
                        v_isShared_4151_ = v_isSharedCheck_4160_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4148_);
                        leanh::lean_dec(v_x_4147_);
                        v___x_4150_ = leanh::lean_box(0);
                        v_isShared_4151_ = v_isSharedCheck_4160_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_4161_ = leanh::lean_ctor_get(v_x_4147_, 0);
                    leanh::lean_inc_ref(v_a_4161_);
                    leanh::lean_dec_ref_known(v_x_4147_, 1);
                    v___x_4162_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__1;
                    v___x_4163_ = l_Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4_spec__6(v_a_4161_);
                    v___x_4164_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4164_, 0, v___x_4162_);
                    leanh::lean_ctor_set(v___x_4164_, 1, v___x_4163_);
                    v___x_4165_ = leanh::lean_box(0);
                    v___x_4166_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4166_, 0, v___x_4164_);
                    leanh::lean_ctor_set(v___x_4166_, 1, v___x_4165_);
                    v___x_4167_ = l_Lean_Json_mkObj(v___x_4166_);
                    leanh::lean_dec_ref_known(v___x_4166_, 2);
                    return v___x_4167_;
                }
                _ => {
                    v_a_4168_ = leanh::lean_ctor_get(v_x_4147_, 0);
                    v_a_4169_ = leanh::lean_ctor_get(v_x_4147_, 1);
                    v_isSharedCheck_4186_ = (!leanh::lean_is_exclusive(v_x_4147_)) as u8;
                    if v_isSharedCheck_4186_ == 0 {
                        v___x_4171_ = v_x_4147_;
                        v_isShared_4172_ = v_isSharedCheck_4186_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4169_);
                        leanh::lean_inc(v_a_4168_);
                        leanh::lean_dec(v_x_4147_);
                        v___x_4171_ = leanh::lean_box(0);
                        v_isShared_4172_ = v_isSharedCheck_4186_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_4152_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__0;
                if v_isShared_4151_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4150_, 3);
                    v___x_4154_ = v___x_4150_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4159_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_a_4148_);
                    v___x_4154_ = v_reuseFailAlloc_4159_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4155_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4155_, 0, v___x_4152_);
                leanh::lean_ctor_set(v___x_4155_, 1, v___x_4154_);
                v___x_4156_ = leanh::lean_box(0);
                v___x_4157_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4157_, 0, v___x_4155_);
                leanh::lean_ctor_set(v___x_4157_, 1, v___x_4156_);
                v___x_4158_ = l_Lean_Json_mkObj(v___x_4157_);
                leanh::lean_dec_ref_known(v___x_4157_, 2);
                return v___x_4158_;
            }
            3 => {
                v___x_4173_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__2;
                v___x_4174_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(v_a_4169_);
                v___x_4175_ = leanh::lean_unsigned_to_nat(2);
                v___x_4176_ = lean_mk_empty_array_with_capacity(v___x_4175_);
                v___x_4177_ = lean_array_push(v___x_4176_, v_a_4168_);
                v___x_4178_ = lean_array_push(v___x_4177_, v___x_4174_);
                v___x_4179_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4179_, 0, v___x_4178_);
                if v_isShared_4172_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4171_, 0);
                    leanh::lean_ctor_set(v___x_4171_, 1, v___x_4179_);
                    leanh::lean_ctor_set(v___x_4171_, 0, v___x_4173_);
                    v___x_4181_ = v___x_4171_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4185_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4185_, 0, v___x_4173_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4185_, 1, v___x_4179_);
                    v___x_4181_ = v_reuseFailAlloc_4185_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4182_ = leanh::lean_box(0);
                v___x_4183_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4183_, 0, v___x_4181_);
                leanh::lean_ctor_set(v___x_4183_, 1, v___x_4182_);
                v___x_4184_ = l_Lean_Json_mkObj(v___x_4183_);
                leanh::lean_dec_ref_known(v___x_4183_, 2);
                return v___x_4184_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4_spec__6_spec__7(
    mut v_sz_4187_: usize,
    mut v_i_4188_: usize,
    mut v_bs_4189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4190_: u8 = 0;
    let mut v_v_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: usize = 0;
    let mut v___x_4196_: usize = 0;
    let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4190_ = lean_usize_dec_lt(v_i_4188_, v_sz_4187_);
                if v___x_4190_ == 0 {
                    return v_bs_4189_;
                } else {
                    v_v_4191_ = lean_array_uget(v_bs_4189_, v_i_4188_);
                    v___x_4192_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4193_ = lean_array_uset(v_bs_4189_, v_i_4188_, v___x_4192_);
                    v___x_4194_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(v_v_4191_);
                    v___x_4195_ = 1usize;
                    v___x_4196_ = lean_usize_add(v_i_4188_, v___x_4195_);
                    v___x_4197_ = lean_array_uset(v_bs_x27_4193_, v_i_4188_, v___x_4194_);
                    v_i_4188_ = v___x_4196_;
                    v_bs_4189_ = v___x_4197_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4_spec__6(
    mut v_a_4199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_4200_: usize = 0;
    let mut v___x_4201_: usize = 0;
    let mut v___x_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_4200_ = lean_array_size(v_a_4199_);
    v___x_4201_ = 0usize;
    v___x_4202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4_spec__6_spec__7(v_sz_4200_, v___x_4201_, v_a_4199_);
    v___x_4203_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4203_, 0, v___x_4202_);
    return v___x_4203_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4_spec__6_spec__7___boxed(
    mut v_sz_4204_: *mut leanh::LeanObject,
    mut v_i_4205_: *mut leanh::LeanObject,
    mut v_bs_4206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4207_: usize = 0;
    let mut v_i_boxed_4208_: usize = 0;
    let mut v_res_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4207_ = leanh::lean_unbox_usize(v_sz_4204_);
    leanh::lean_dec(v_sz_4204_);
    v_i_boxed_4208_ = leanh::lean_unbox_usize(v_i_4205_);
    leanh::lean_dec(v_i_4205_);
    v_res_4209_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4_spec__6_spec__7(v_sz_boxed_4207_, v_i_boxed_4208_, v_bs_4206_);
    return v_res_4209_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___redArg(
    mut v_f_4210_: *mut leanh::LeanObject,
    mut v_x_4211_: *mut leanh::LeanObject,
    mut v___y_4212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4216_: u8 = 0;
    let mut v___x_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4221_: u8 = 0;
    let mut v_a_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4225_: u8 = 0;
    let mut v_sz_4226_: usize = 0;
    let mut v___x_4227_: usize = 0;
    let mut v___x_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4233_: u8 = 0;
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4240_: u8 = 0;
    let mut v_isSharedCheck_4241_: u8 = 0;
    let mut v_a_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4246_: u8 = 0;
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4255_: u8 = 0;
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4262_: u8 = 0;
    let mut v_isSharedCheck_4263_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_4211_) {
                0 => {
                    leanh::lean_dec_ref(v_f_4210_);
                    v_a_4213_ = leanh::lean_ctor_get(v_x_4211_, 0);
                    v_isSharedCheck_4221_ = (!leanh::lean_is_exclusive(v_x_4211_)) as u8;
                    if v_isSharedCheck_4221_ == 0 {
                        v___x_4215_ = v_x_4211_;
                        v_isShared_4216_ = v_isSharedCheck_4221_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4213_);
                        leanh::lean_dec(v_x_4211_);
                        v___x_4215_ = leanh::lean_box(0);
                        v_isShared_4216_ = v_isSharedCheck_4221_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_4222_ = leanh::lean_ctor_get(v_x_4211_, 0);
                    v_isSharedCheck_4241_ = (!leanh::lean_is_exclusive(v_x_4211_)) as u8;
                    if v_isSharedCheck_4241_ == 0 {
                        v___x_4224_ = v_x_4211_;
                        v_isShared_4225_ = v_isSharedCheck_4241_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4222_);
                        leanh::lean_dec(v_x_4211_);
                        v___x_4224_ = leanh::lean_box(0);
                        v_isShared_4225_ = v_isSharedCheck_4241_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v_a_4242_ = leanh::lean_ctor_get(v_x_4211_, 0);
                    v_a_4243_ = leanh::lean_ctor_get(v_x_4211_, 1);
                    v_isSharedCheck_4263_ = (!leanh::lean_is_exclusive(v_x_4211_)) as u8;
                    if v_isSharedCheck_4263_ == 0 {
                        v___x_4245_ = v_x_4211_;
                        v_isShared_4246_ = v_isSharedCheck_4263_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4243_);
                        leanh::lean_inc(v_a_4242_);
                        leanh::lean_dec(v_x_4211_);
                        v___x_4245_ = leanh::lean_box(0);
                        v_isShared_4246_ = v_isSharedCheck_4263_;
                        state = 7;
                        continue;
                    }
                }
            },
            1 => {
                if v_isShared_4216_ == 0 {
                    v___x_4218_ = v___x_4215_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4220_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_a_4213_);
                    v___x_4218_ = v_reuseFailAlloc_4220_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4219_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4219_, 0, v___x_4218_);
                leanh::lean_ctor_set(v___x_4219_, 1, v___y_4212_);
                return v___x_4219_;
            }
            3 => {
                v_sz_4226_ = lean_array_size(v_a_4222_);
                v___x_4227_ = 0usize;
                v___x_4228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2_spec__2___redArg(v_f_4210_, v_sz_4226_, v___x_4227_, v_a_4222_, v___y_4212_);
                v_fst_4229_ = leanh::lean_ctor_get(v___x_4228_, 0);
                v_snd_4230_ = leanh::lean_ctor_get(v___x_4228_, 1);
                v_isSharedCheck_4240_ = (!leanh::lean_is_exclusive(v___x_4228_)) as u8;
                if v_isSharedCheck_4240_ == 0 {
                    v___x_4232_ = v___x_4228_;
                    v_isShared_4233_ = v_isSharedCheck_4240_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4230_);
                    leanh::lean_inc(v_fst_4229_);
                    leanh::lean_dec(v___x_4228_);
                    v___x_4232_ = leanh::lean_box(0);
                    v_isShared_4233_ = v_isSharedCheck_4240_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4225_ == 0 {
                    leanh::lean_ctor_set(v___x_4224_, 0, v_fst_4229_);
                    v___x_4235_ = v___x_4224_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4239_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_fst_4229_);
                    v___x_4235_ = v_reuseFailAlloc_4239_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4233_ == 0 {
                    leanh::lean_ctor_set(v___x_4232_, 0, v___x_4235_);
                    v___x_4237_ = v___x_4232_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4238_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4238_, 0, v___x_4235_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4238_, 1, v_snd_4230_);
                    v___x_4237_ = v_reuseFailAlloc_4238_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4237_;
            }
            7 => {
                leanh::lean_inc_ref(v_f_4210_);
                v___x_4247_ = leanh::lean_apply_2(v_f_4210_, v_a_4242_, v___y_4212_);
                v_fst_4248_ = leanh::lean_ctor_get(v___x_4247_, 0);
                leanh::lean_inc(v_fst_4248_);
                v_snd_4249_ = leanh::lean_ctor_get(v___x_4247_, 1);
                leanh::lean_inc(v_snd_4249_);
                leanh::lean_dec_ref(v___x_4247_);
                v___x_4250_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___redArg(v_f_4210_, v_a_4243_, v_snd_4249_);
                v_fst_4251_ = leanh::lean_ctor_get(v___x_4250_, 0);
                v_snd_4252_ = leanh::lean_ctor_get(v___x_4250_, 1);
                v_isSharedCheck_4262_ = (!leanh::lean_is_exclusive(v___x_4250_)) as u8;
                if v_isSharedCheck_4262_ == 0 {
                    v___x_4254_ = v___x_4250_;
                    v_isShared_4255_ = v_isSharedCheck_4262_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4252_);
                    leanh::lean_inc(v_fst_4251_);
                    leanh::lean_dec(v___x_4250_);
                    v___x_4254_ = leanh::lean_box(0);
                    v_isShared_4255_ = v_isSharedCheck_4262_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_4246_ == 0 {
                    leanh::lean_ctor_set(v___x_4245_, 1, v_fst_4251_);
                    leanh::lean_ctor_set(v___x_4245_, 0, v_fst_4248_);
                    v___x_4257_ = v___x_4245_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4261_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4261_, 0, v_fst_4248_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4261_, 1, v_fst_4251_);
                    v___x_4257_ = v_reuseFailAlloc_4261_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4255_ == 0 {
                    leanh::lean_ctor_set(v___x_4254_, 0, v___x_4257_);
                    v___x_4259_ = v___x_4254_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4260_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4260_, 0, v___x_4257_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4260_, 1, v_snd_4252_);
                    v___x_4259_ = v_reuseFailAlloc_4260_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4259_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2_spec__2___redArg(
    mut v_f_4264_: *mut leanh::LeanObject,
    mut v_sz_4265_: usize,
    mut v_i_4266_: usize,
    mut v_bs_4267_: *mut leanh::LeanObject,
    mut v___y_4268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4269_: u8 = 0;
    let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: usize = 0;
    let mut v___x_4278_: usize = 0;
    let mut v___x_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4269_ = lean_usize_dec_lt(v_i_4266_, v_sz_4265_);
                if v___x_4269_ == 0 {
                    leanh::lean_dec_ref(v_f_4264_);
                    v___x_4270_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4270_, 0, v_bs_4267_);
                    leanh::lean_ctor_set(v___x_4270_, 1, v___y_4268_);
                    return v___x_4270_;
                } else {
                    v_v_4271_ = lean_array_uget_borrowed(v_bs_4267_, v_i_4266_);
                    leanh::lean_inc(v_v_4271_);
                    leanh::lean_inc_ref(v_f_4264_);
                    v___x_4272_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___redArg(v_f_4264_, v_v_4271_, v___y_4268_);
                    v_fst_4273_ = leanh::lean_ctor_get(v___x_4272_, 0);
                    leanh::lean_inc(v_fst_4273_);
                    v_snd_4274_ = leanh::lean_ctor_get(v___x_4272_, 1);
                    leanh::lean_inc(v_snd_4274_);
                    leanh::lean_dec_ref(v___x_4272_);
                    v___x_4275_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4276_ = lean_array_uset(v_bs_4267_, v_i_4266_, v___x_4275_);
                    v___x_4277_ = 1usize;
                    v___x_4278_ = lean_usize_add(v_i_4266_, v___x_4277_);
                    v___x_4279_ = lean_array_uset(v_bs_x27_4276_, v_i_4266_, v_fst_4273_);
                    v_i_4266_ = v___x_4278_;
                    v_bs_4267_ = v___x_4279_;
                    v___y_4268_ = v_snd_4274_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2_spec__2___redArg___boxed(
    mut v_f_4281_: *mut leanh::LeanObject,
    mut v_sz_4282_: *mut leanh::LeanObject,
    mut v_i_4283_: *mut leanh::LeanObject,
    mut v_bs_4284_: *mut leanh::LeanObject,
    mut v___y_4285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4286_: usize = 0;
    let mut v_i_boxed_4287_: usize = 0;
    let mut v_res_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4286_ = leanh::lean_unbox_usize(v_sz_4282_);
    leanh::lean_dec(v_sz_4282_);
    v_i_boxed_4287_ = leanh::lean_unbox_usize(v_i_4283_);
    leanh::lean_dec(v_i_4283_);
    v_res_4288_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2_spec__2___redArg(v_f_4281_, v_sz_boxed_4286_, v_i_boxed_4287_, v_bs_4284_, v___y_4285_);
    return v_res_4288_;
}
pub unsafe fn l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_(
    mut v_a_4290_: *mut leanh::LeanObject,
    mut v_a_4291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_names_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarIds_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_x3f_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInstance_x3f_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isType_x3f_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInserted_x3f_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRemoved_x3f_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4302_: u8 = 0;
    let mut v_sz_4303_: usize = 0;
    let mut v___x_4304_: usize = 0;
    let mut v___x_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4308_: usize = 0;
    let mut v___x_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4318_: u8 = 0;
    let mut v___x_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4346_: u8 = 0;
    let mut v___x_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: u8 = 0;
    let mut v___x_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4352_: u8 = 0;
    let mut v___y_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4362_: u8 = 0;
    let mut v___x_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: u8 = 0;
    let mut v___x_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4368_: u8 = 0;
    let mut v___y_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4377_: u8 = 0;
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: u8 = 0;
    let mut v___x_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4383_: u8 = 0;
    let mut v_fst_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4391_: u8 = 0;
    let mut v___x_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: u8 = 0;
    let mut v___x_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4397_: u8 = 0;
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4402_: u8 = 0;
    let mut v___x_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4410_: u8 = 0;
    let mut v_isSharedCheck_4411_: u8 = 0;
    let mut v_isSharedCheck_4412_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_names_4292_ = leanh::lean_ctor_get(v_a_4290_, 0);
                v_fvarIds_4293_ = leanh::lean_ctor_get(v_a_4290_, 1);
                v_type_4294_ = leanh::lean_ctor_get(v_a_4290_, 2);
                v_val_x3f_4295_ = leanh::lean_ctor_get(v_a_4290_, 3);
                v_isInstance_x3f_4296_ = leanh::lean_ctor_get(v_a_4290_, 4);
                v_isType_x3f_4297_ = leanh::lean_ctor_get(v_a_4290_, 5);
                v_isInserted_x3f_4298_ = leanh::lean_ctor_get(v_a_4290_, 6);
                v_isRemoved_x3f_4299_ = leanh::lean_ctor_get(v_a_4290_, 7);
                v_isSharedCheck_4412_ = (!leanh::lean_is_exclusive(v_a_4290_)) as u8;
                if v_isSharedCheck_4412_ == 0 {
                    v___x_4301_ = v_a_4290_;
                    v_isShared_4302_ = v_isSharedCheck_4412_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_isRemoved_x3f_4299_);
                    leanh::lean_inc(v_isInserted_x3f_4298_);
                    leanh::lean_inc(v_isType_x3f_4297_);
                    leanh::lean_inc(v_isInstance_x3f_4296_);
                    leanh::lean_inc(v_val_x3f_4295_);
                    leanh::lean_inc(v_type_4294_);
                    leanh::lean_inc(v_fvarIds_4293_);
                    leanh::lean_inc(v_names_4292_);
                    leanh::lean_dec(v_a_4290_);
                    v___x_4301_ = leanh::lean_box(0);
                    v_isShared_4302_ = v_isSharedCheck_4412_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_sz_4303_ = lean_array_size(v_names_4292_);
                v___x_4304_ = 0usize;
                v___x_4305_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0(v_sz_4303_, v___x_4304_, v_names_4292_, v_a_4291_);
                v_fst_4306_ = leanh::lean_ctor_get(v___x_4305_, 0);
                leanh::lean_inc(v_fst_4306_);
                v_snd_4307_ = leanh::lean_ctor_get(v___x_4305_, 1);
                leanh::lean_inc(v_snd_4307_);
                leanh::lean_dec_ref(v___x_4305_);
                v_sz_4308_ = lean_array_size(v_fvarIds_4293_);
                v___x_4309_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__1(v_sz_4308_, v___x_4304_, v_fvarIds_4293_, v_snd_4307_);
                v_fst_4310_ = leanh::lean_ctor_get(v___x_4309_, 0);
                leanh::lean_inc(v_fst_4310_);
                v_snd_4311_ = leanh::lean_ctor_get(v___x_4309_, 1);
                leanh::lean_inc(v_snd_4311_);
                leanh::lean_dec_ref(v___x_4309_);
                v___x_4312_ = l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc___closed__0_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_;
                v___x_4313_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___redArg(v___x_4312_, v_type_4294_, v_snd_4311_);
                v_fst_4314_ = leanh::lean_ctor_get(v___x_4313_, 0);
                v_snd_4315_ = leanh::lean_ctor_get(v___x_4313_, 1);
                v_isSharedCheck_4411_ = (!leanh::lean_is_exclusive(v___x_4313_)) as u8;
                if v_isSharedCheck_4411_ == 0 {
                    v___x_4317_ = v___x_4313_;
                    v_isShared_4318_ = v_isSharedCheck_4411_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4315_);
                    leanh::lean_inc(v_fst_4314_);
                    leanh::lean_dec(v___x_4313_);
                    v___x_4317_ = leanh::lean_box(0);
                    v_isShared_4318_ = v_isSharedCheck_4411_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4319_ = l_Array_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3(v_fst_4306_);
                v___x_4320_ = l_Array_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3(v_fst_4310_);
                v___x_4321_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(v_fst_4314_);
                if leanh::lean_obj_tag(v_val_x3f_4295_) == 0 {
                    v___x_4398_ = leanh::lean_box(0);
                    v_fst_4385_ = v___x_4398_;
                    v_snd_4386_ = v_snd_4315_;
                    state = 15;
                    continue;
                } else {
                    v_val_4399_ = leanh::lean_ctor_get(v_val_x3f_4295_, 0);
                    v_isSharedCheck_4410_ =
                        (!leanh::lean_is_exclusive(v_val_x3f_4295_)) as u8;
                    if v_isSharedCheck_4410_ == 0 {
                        v___x_4401_ = v_val_x3f_4295_;
                        v_isShared_4402_ = v_isSharedCheck_4410_;
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4399_);
                        leanh::lean_dec(v_val_x3f_4295_);
                        v___x_4401_ = leanh::lean_box(0);
                        v_isShared_4402_ = v_isSharedCheck_4410_;
                        state = 18;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4302_ == 0 {
                    leanh::lean_ctor_set(v___x_4301_, 7, v_fst_4327_);
                    leanh::lean_ctor_set(v___x_4301_, 6, v___y_4326_);
                    leanh::lean_ctor_set(v___x_4301_, 5, v___y_4325_);
                    leanh::lean_ctor_set(v___x_4301_, 4, v___y_4324_);
                    leanh::lean_ctor_set(v___x_4301_, 3, v___y_4323_);
                    leanh::lean_ctor_set(v___x_4301_, 2, v___x_4321_);
                    leanh::lean_ctor_set(v___x_4301_, 1, v___x_4320_);
                    leanh::lean_ctor_set(v___x_4301_, 0, v___x_4319_);
                    v___x_4330_ = v___x_4301_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4335_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 0, v___x_4319_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 1, v___x_4320_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 2, v___x_4321_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 3, v___y_4323_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 4, v___y_4324_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 5, v___y_4325_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 6, v___y_4326_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 7, v_fst_4327_);
                    v___x_4330_ = v_reuseFailAlloc_4335_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4331_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47_(v___x_4330_);
                leanh::lean_dec_ref(v___x_4330_);
                if v_isShared_4318_ == 0 {
                    leanh::lean_ctor_set(v___x_4317_, 1, v_snd_4328_);
                    leanh::lean_ctor_set(v___x_4317_, 0, v___x_4331_);
                    v___x_4333_ = v___x_4317_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4334_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4334_, 0, v___x_4331_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4334_, 1, v_snd_4328_);
                    v___x_4333_ = v_reuseFailAlloc_4334_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4333_;
            }
            6 => {
                if leanh::lean_obj_tag(v_isRemoved_x3f_4299_) == 0 {
                    v___x_4342_ = leanh::lean_box(0);
                    v___y_4323_ = v___y_4337_;
                    v___y_4324_ = v___y_4338_;
                    v___y_4325_ = v___y_4339_;
                    v___y_4326_ = v_fst_4340_;
                    v_fst_4327_ = v___x_4342_;
                    v_snd_4328_ = v_snd_4341_;
                    state = 3;
                    continue;
                } else {
                    v_val_4343_ = leanh::lean_ctor_get(v_isRemoved_x3f_4299_, 0);
                    v_isSharedCheck_4352_ =
                        (!leanh::lean_is_exclusive(v_isRemoved_x3f_4299_)) as u8;
                    if v_isSharedCheck_4352_ == 0 {
                        v___x_4345_ = v_isRemoved_x3f_4299_;
                        v_isShared_4346_ = v_isSharedCheck_4352_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4343_);
                        leanh::lean_dec(v_isRemoved_x3f_4299_);
                        v___x_4345_ = leanh::lean_box(0);
                        v_isShared_4346_ = v_isSharedCheck_4352_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                v___x_4347_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_4348_ = (leanh::lean_unbox(v_val_4343_) as u8);
                leanh::lean_dec(v_val_4343_);
                leanh::lean_ctor_set_uint8(v___x_4347_, 0 as u32, v___x_4348_);
                if v_isShared_4346_ == 0 {
                    leanh::lean_ctor_set(v___x_4345_, 0, v___x_4347_);
                    v___x_4350_ = v___x_4345_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4351_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4351_, 0, v___x_4347_);
                    v___x_4350_ = v_reuseFailAlloc_4351_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___y_4323_ = v___y_4337_;
                v___y_4324_ = v___y_4338_;
                v___y_4325_ = v___y_4339_;
                v___y_4326_ = v_fst_4340_;
                v_fst_4327_ = v___x_4350_;
                v_snd_4328_ = v_snd_4341_;
                state = 3;
                continue;
            }
            9 => {
                if leanh::lean_obj_tag(v_isInserted_x3f_4298_) == 0 {
                    v___x_4358_ = leanh::lean_box(0);
                    v___y_4337_ = v___y_4354_;
                    v___y_4338_ = v___y_4355_;
                    v___y_4339_ = v_fst_4356_;
                    v_fst_4340_ = v___x_4358_;
                    v_snd_4341_ = v_snd_4357_;
                    state = 6;
                    continue;
                } else {
                    v_val_4359_ = leanh::lean_ctor_get(v_isInserted_x3f_4298_, 0);
                    v_isSharedCheck_4368_ =
                        (!leanh::lean_is_exclusive(v_isInserted_x3f_4298_)) as u8;
                    if v_isSharedCheck_4368_ == 0 {
                        v___x_4361_ = v_isInserted_x3f_4298_;
                        v_isShared_4362_ = v_isSharedCheck_4368_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4359_);
                        leanh::lean_dec(v_isInserted_x3f_4298_);
                        v___x_4361_ = leanh::lean_box(0);
                        v_isShared_4362_ = v_isSharedCheck_4368_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                v___x_4363_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_4364_ = (leanh::lean_unbox(v_val_4359_) as u8);
                leanh::lean_dec(v_val_4359_);
                leanh::lean_ctor_set_uint8(v___x_4363_, 0 as u32, v___x_4364_);
                if v_isShared_4362_ == 0 {
                    leanh::lean_ctor_set(v___x_4361_, 0, v___x_4363_);
                    v___x_4366_ = v___x_4361_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4367_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4367_, 0, v___x_4363_);
                    v___x_4366_ = v_reuseFailAlloc_4367_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___y_4337_ = v___y_4354_;
                v___y_4338_ = v___y_4355_;
                v___y_4339_ = v_fst_4356_;
                v_fst_4340_ = v___x_4366_;
                v_snd_4341_ = v_snd_4357_;
                state = 6;
                continue;
            }
            12 => {
                if leanh::lean_obj_tag(v_isType_x3f_4297_) == 0 {
                    v___x_4373_ = leanh::lean_box(0);
                    v___y_4354_ = v___y_4370_;
                    v___y_4355_ = v_fst_4371_;
                    v_fst_4356_ = v___x_4373_;
                    v_snd_4357_ = v_snd_4372_;
                    state = 9;
                    continue;
                } else {
                    v_val_4374_ = leanh::lean_ctor_get(v_isType_x3f_4297_, 0);
                    v_isSharedCheck_4383_ =
                        (!leanh::lean_is_exclusive(v_isType_x3f_4297_)) as u8;
                    if v_isSharedCheck_4383_ == 0 {
                        v___x_4376_ = v_isType_x3f_4297_;
                        v_isShared_4377_ = v_isSharedCheck_4383_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4374_);
                        leanh::lean_dec(v_isType_x3f_4297_);
                        v___x_4376_ = leanh::lean_box(0);
                        v_isShared_4377_ = v_isSharedCheck_4383_;
                        state = 13;
                        continue;
                    }
                }
            }
            13 => {
                v___x_4378_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_4379_ = (leanh::lean_unbox(v_val_4374_) as u8);
                leanh::lean_dec(v_val_4374_);
                leanh::lean_ctor_set_uint8(v___x_4378_, 0 as u32, v___x_4379_);
                if v_isShared_4377_ == 0 {
                    leanh::lean_ctor_set(v___x_4376_, 0, v___x_4378_);
                    v___x_4381_ = v___x_4376_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4382_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 0, v___x_4378_);
                    v___x_4381_ = v_reuseFailAlloc_4382_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___y_4354_ = v___y_4370_;
                v___y_4355_ = v_fst_4371_;
                v_fst_4356_ = v___x_4381_;
                v_snd_4357_ = v_snd_4372_;
                state = 9;
                continue;
            }
            15 => {
                if leanh::lean_obj_tag(v_isInstance_x3f_4296_) == 0 {
                    v___x_4387_ = leanh::lean_box(0);
                    v___y_4370_ = v_fst_4385_;
                    v_fst_4371_ = v___x_4387_;
                    v_snd_4372_ = v_snd_4386_;
                    state = 12;
                    continue;
                } else {
                    v_val_4388_ = leanh::lean_ctor_get(v_isInstance_x3f_4296_, 0);
                    v_isSharedCheck_4397_ =
                        (!leanh::lean_is_exclusive(v_isInstance_x3f_4296_)) as u8;
                    if v_isSharedCheck_4397_ == 0 {
                        v___x_4390_ = v_isInstance_x3f_4296_;
                        v_isShared_4391_ = v_isSharedCheck_4397_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4388_);
                        leanh::lean_dec(v_isInstance_x3f_4296_);
                        v___x_4390_ = leanh::lean_box(0);
                        v_isShared_4391_ = v_isSharedCheck_4397_;
                        state = 16;
                        continue;
                    }
                }
            }
            16 => {
                v___x_4392_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_4393_ = (leanh::lean_unbox(v_val_4388_) as u8);
                leanh::lean_dec(v_val_4388_);
                leanh::lean_ctor_set_uint8(v___x_4392_, 0 as u32, v___x_4393_);
                if v_isShared_4391_ == 0 {
                    leanh::lean_ctor_set(v___x_4390_, 0, v___x_4392_);
                    v___x_4395_ = v___x_4390_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4396_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___x_4392_);
                    v___x_4395_ = v_reuseFailAlloc_4396_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___y_4370_ = v_fst_4385_;
                v_fst_4371_ = v___x_4395_;
                v_snd_4372_ = v_snd_4386_;
                state = 12;
                continue;
            }
            18 => {
                v___x_4403_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___redArg(v___x_4312_, v_val_4399_, v_snd_4315_);
                v_fst_4404_ = leanh::lean_ctor_get(v___x_4403_, 0);
                leanh::lean_inc(v_fst_4404_);
                v_snd_4405_ = leanh::lean_ctor_get(v___x_4403_, 1);
                leanh::lean_inc(v_snd_4405_);
                leanh::lean_dec_ref(v___x_4403_);
                v___x_4406_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(v_fst_4404_);
                if v_isShared_4402_ == 0 {
                    leanh::lean_ctor_set(v___x_4401_, 0, v___x_4406_);
                    v___x_4408_ = v___x_4401_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4409_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4409_, 0, v___x_4406_);
                    v___x_4408_ = v_reuseFailAlloc_4409_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v_fst_4385_ = v___x_4408_;
                v_snd_4386_ = v_snd_4405_;
                state = 15;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2(
    mut v_00_u03b1_4413_: *mut leanh::LeanObject,
    mut v_00_u03b2_4414_: *mut leanh::LeanObject,
    mut v_f_4415_: *mut leanh::LeanObject,
    mut v_x_4416_: *mut leanh::LeanObject,
    mut v___y_4417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4418_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___redArg(v_f_4415_, v_x_4416_, v___y_4417_);
    return v___x_4418_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2_spec__2(
    mut v_00_u03b1_4419_: *mut leanh::LeanObject,
    mut v_00_u03b2_4420_: *mut leanh::LeanObject,
    mut v_f_4421_: *mut leanh::LeanObject,
    mut v_sz_4422_: usize,
    mut v_i_4423_: usize,
    mut v_bs_4424_: *mut leanh::LeanObject,
    mut v___y_4425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4426_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2_spec__2___redArg(v_f_4421_, v_sz_4422_, v_i_4423_, v_bs_4424_, v___y_4425_);
    return v___x_4426_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2_spec__2___boxed(
    mut v_00_u03b1_4427_: *mut leanh::LeanObject,
    mut v_00_u03b2_4428_: *mut leanh::LeanObject,
    mut v_f_4429_: *mut leanh::LeanObject,
    mut v_sz_4430_: *mut leanh::LeanObject,
    mut v_i_4431_: *mut leanh::LeanObject,
    mut v_bs_4432_: *mut leanh::LeanObject,
    mut v___y_4433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4434_: usize = 0;
    let mut v_i_boxed_4435_: usize = 0;
    let mut v_res_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4434_ = leanh::lean_unbox_usize(v_sz_4430_);
    leanh::lean_dec(v_sz_4430_);
    v_i_boxed_4435_ = leanh::lean_unbox_usize(v_i_4431_);
    leanh::lean_dec(v_i_4431_);
    v_res_4436_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2_spec__2(v_00_u03b1_4427_, v_00_u03b2_4428_, v_f_4429_, v_sz_boxed_4434_, v_i_boxed_4435_, v_bs_4432_, v___y_4433_);
    return v_res_4436_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__1___redArg(
    mut v_x_4437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_x_4437_);
    return v_x_4437_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__1___redArg___boxed(
    mut v_x_4438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4439_ = l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__1___redArg(v_x_4438_);
    leanh::lean_dec_ref(v_x_4438_);
    return v_res_4439_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__1(
    mut v_00_u03b1_4440_: *mut leanh::LeanObject,
    mut v_x_4441_: *mut leanh::LeanObject,
    mut v___y_4442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_x_4441_);
    return v_x_4441_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__1___boxed(
    mut v_00_u03b1_4443_: *mut leanh::LeanObject,
    mut v_x_4444_: *mut leanh::LeanObject,
    mut v___y_4445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4446_ = l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__1(v_00_u03b1_4443_, v_x_4444_, v___y_4445_);
    leanh::lean_dec_ref(v___y_4445_);
    leanh::lean_dec_ref(v_x_4444_);
    return v_res_4446_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5___redArg(
    mut v_f_4447_: *mut leanh::LeanObject,
    mut v_x_4448_: *mut leanh::LeanObject,
    mut v___y_4449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4453_: u8 = 0;
    let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4458_: u8 = 0;
    let mut v_a_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4462_: u8 = 0;
    let mut v_sz_4463_: usize = 0;
    let mut v___x_4464_: usize = 0;
    let mut v___x_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4469_: u8 = 0;
    let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4473_: u8 = 0;
    let mut v_a_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4477_: u8 = 0;
    let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4484_: u8 = 0;
    let mut v_isSharedCheck_4485_: u8 = 0;
    let mut v_a_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4490_: u8 = 0;
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4495_: u8 = 0;
    let mut v___x_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4499_: u8 = 0;
    let mut v_a_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4505_: u8 = 0;
    let mut v___x_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4512_: u8 = 0;
    let mut v_isSharedCheck_4513_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_4448_) {
                0 => {
                    leanh::lean_dec_ref(v_f_4447_);
                    v_a_4450_ = leanh::lean_ctor_get(v_x_4448_, 0);
                    v_isSharedCheck_4458_ = (!leanh::lean_is_exclusive(v_x_4448_)) as u8;
                    if v_isSharedCheck_4458_ == 0 {
                        v___x_4452_ = v_x_4448_;
                        v_isShared_4453_ = v_isSharedCheck_4458_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4450_);
                        leanh::lean_dec(v_x_4448_);
                        v___x_4452_ = leanh::lean_box(0);
                        v_isShared_4453_ = v_isSharedCheck_4458_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_4459_ = leanh::lean_ctor_get(v_x_4448_, 0);
                    v_isSharedCheck_4485_ = (!leanh::lean_is_exclusive(v_x_4448_)) as u8;
                    if v_isSharedCheck_4485_ == 0 {
                        v___x_4461_ = v_x_4448_;
                        v_isShared_4462_ = v_isSharedCheck_4485_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4459_);
                        leanh::lean_dec(v_x_4448_);
                        v___x_4461_ = leanh::lean_box(0);
                        v_isShared_4462_ = v_isSharedCheck_4485_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v_a_4486_ = leanh::lean_ctor_get(v_x_4448_, 0);
                    v_a_4487_ = leanh::lean_ctor_get(v_x_4448_, 1);
                    v_isSharedCheck_4513_ = (!leanh::lean_is_exclusive(v_x_4448_)) as u8;
                    if v_isSharedCheck_4513_ == 0 {
                        v___x_4489_ = v_x_4448_;
                        v_isShared_4490_ = v_isSharedCheck_4513_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4487_);
                        leanh::lean_inc(v_a_4486_);
                        leanh::lean_dec(v_x_4448_);
                        v___x_4489_ = leanh::lean_box(0);
                        v_isShared_4490_ = v_isSharedCheck_4513_;
                        state = 9;
                        continue;
                    }
                }
            },
            1 => {
                if v_isShared_4453_ == 0 {
                    v___x_4455_ = v___x_4452_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4457_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4450_);
                    v___x_4455_ = v_reuseFailAlloc_4457_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4456_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4456_, 0, v___x_4455_);
                return v___x_4456_;
            }
            3 => {
                v_sz_4463_ = lean_array_size(v_a_4459_);
                v___x_4464_ = 0usize;
                v___x_4465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5_spec__7___redArg(v_f_4447_, v_sz_4463_, v___x_4464_, v_a_4459_, v___y_4449_);
                if leanh::lean_obj_tag(v___x_4465_) == 0 {
                    leanh::lean_del_object(v___x_4461_);
                    v_a_4466_ = leanh::lean_ctor_get(v___x_4465_, 0);
                    v_isSharedCheck_4473_ = (!leanh::lean_is_exclusive(v___x_4465_)) as u8;
                    if v_isSharedCheck_4473_ == 0 {
                        v___x_4468_ = v___x_4465_;
                        v_isShared_4469_ = v_isSharedCheck_4473_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4466_);
                        leanh::lean_dec(v___x_4465_);
                        v___x_4468_ = leanh::lean_box(0);
                        v_isShared_4469_ = v_isSharedCheck_4473_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_4474_ = leanh::lean_ctor_get(v___x_4465_, 0);
                    v_isSharedCheck_4484_ = (!leanh::lean_is_exclusive(v___x_4465_)) as u8;
                    if v_isSharedCheck_4484_ == 0 {
                        v___x_4476_ = v___x_4465_;
                        v_isShared_4477_ = v_isSharedCheck_4484_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4474_);
                        leanh::lean_dec(v___x_4465_);
                        v___x_4476_ = leanh::lean_box(0);
                        v_isShared_4477_ = v_isSharedCheck_4484_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4469_ == 0 {
                    v___x_4471_ = v___x_4468_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4472_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_a_4466_);
                    v___x_4471_ = v_reuseFailAlloc_4472_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4471_;
            }
            6 => {
                if v_isShared_4462_ == 0 {
                    leanh::lean_ctor_set(v___x_4461_, 0, v_a_4474_);
                    v___x_4479_ = v___x_4461_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4483_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_a_4474_);
                    v___x_4479_ = v_reuseFailAlloc_4483_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4477_ == 0 {
                    leanh::lean_ctor_set(v___x_4476_, 0, v___x_4479_);
                    v___x_4481_ = v___x_4476_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4482_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4482_, 0, v___x_4479_);
                    v___x_4481_ = v_reuseFailAlloc_4482_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4481_;
            }
            9 => {
                leanh::lean_inc_ref(v_f_4447_);
                leanh::lean_inc_ref(v___y_4449_);
                v___x_4491_ = leanh::lean_apply_2(v_f_4447_, v_a_4486_, v___y_4449_);
                if leanh::lean_obj_tag(v___x_4491_) == 0 {
                    leanh::lean_del_object(v___x_4489_);
                    leanh::lean_dec_ref(v_a_4487_);
                    leanh::lean_dec_ref(v_f_4447_);
                    v_a_4492_ = leanh::lean_ctor_get(v___x_4491_, 0);
                    v_isSharedCheck_4499_ = (!leanh::lean_is_exclusive(v___x_4491_)) as u8;
                    if v_isSharedCheck_4499_ == 0 {
                        v___x_4494_ = v___x_4491_;
                        v_isShared_4495_ = v_isSharedCheck_4499_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4492_);
                        leanh::lean_dec(v___x_4491_);
                        v___x_4494_ = leanh::lean_box(0);
                        v_isShared_4495_ = v_isSharedCheck_4499_;
                        state = 10;
                        continue;
                    }
                } else {
                    v_a_4500_ = leanh::lean_ctor_get(v___x_4491_, 0);
                    leanh::lean_inc(v_a_4500_);
                    leanh::lean_dec_ref_known(v___x_4491_, 1);
                    v___x_4501_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5___redArg(v_f_4447_, v_a_4487_, v___y_4449_);
                    if leanh::lean_obj_tag(v___x_4501_) == 0 {
                        leanh::lean_dec(v_a_4500_);
                        leanh::lean_del_object(v___x_4489_);
                        return v___x_4501_;
                    } else {
                        v_a_4502_ = leanh::lean_ctor_get(v___x_4501_, 0);
                        v_isSharedCheck_4512_ =
                            (!leanh::lean_is_exclusive(v___x_4501_)) as u8;
                        if v_isSharedCheck_4512_ == 0 {
                            v___x_4504_ = v___x_4501_;
                            v_isShared_4505_ = v_isSharedCheck_4512_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4502_);
                            leanh::lean_dec(v___x_4501_);
                            v___x_4504_ = leanh::lean_box(0);
                            v_isShared_4505_ = v_isSharedCheck_4512_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            10 => {
                if v_isShared_4495_ == 0 {
                    v___x_4497_ = v___x_4494_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4498_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_a_4492_);
                    v___x_4497_ = v_reuseFailAlloc_4498_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4497_;
            }
            12 => {
                if v_isShared_4490_ == 0 {
                    leanh::lean_ctor_set(v___x_4489_, 1, v_a_4502_);
                    leanh::lean_ctor_set(v___x_4489_, 0, v_a_4500_);
                    v___x_4507_ = v___x_4489_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4511_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_a_4500_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4511_, 1, v_a_4502_);
                    v___x_4507_ = v_reuseFailAlloc_4511_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_4505_ == 0 {
                    leanh::lean_ctor_set(v___x_4504_, 0, v___x_4507_);
                    v___x_4509_ = v___x_4504_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4510_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4510_, 0, v___x_4507_);
                    v___x_4509_ = v_reuseFailAlloc_4510_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4509_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5_spec__7___redArg(
    mut v_f_4514_: *mut leanh::LeanObject,
    mut v_sz_4515_: usize,
    mut v_i_4516_: usize,
    mut v_bs_4517_: *mut leanh::LeanObject,
    mut v___y_4518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4519_: u8 = 0;
    let mut v___x_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4526_: u8 = 0;
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4530_: u8 = 0;
    let mut v_a_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: usize = 0;
    let mut v___x_4535_: usize = 0;
    let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4519_ = lean_usize_dec_lt(v_i_4516_, v_sz_4515_);
                if v___x_4519_ == 0 {
                    leanh::lean_dec_ref(v_f_4514_);
                    v___x_4520_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4520_, 0, v_bs_4517_);
                    return v___x_4520_;
                } else {
                    v_v_4521_ = lean_array_uget_borrowed(v_bs_4517_, v_i_4516_);
                    leanh::lean_inc(v_v_4521_);
                    leanh::lean_inc_ref(v_f_4514_);
                    v___x_4522_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5___redArg(v_f_4514_, v_v_4521_, v___y_4518_);
                    if leanh::lean_obj_tag(v___x_4522_) == 0 {
                        leanh::lean_dec_ref(v_bs_4517_);
                        leanh::lean_dec_ref(v_f_4514_);
                        v_a_4523_ = leanh::lean_ctor_get(v___x_4522_, 0);
                        v_isSharedCheck_4530_ =
                            (!leanh::lean_is_exclusive(v___x_4522_)) as u8;
                        if v_isSharedCheck_4530_ == 0 {
                            v___x_4525_ = v___x_4522_;
                            v_isShared_4526_ = v_isSharedCheck_4530_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4523_);
                            leanh::lean_dec(v___x_4522_);
                            v___x_4525_ = leanh::lean_box(0);
                            v_isShared_4526_ = v_isSharedCheck_4530_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4531_ = leanh::lean_ctor_get(v___x_4522_, 0);
                        leanh::lean_inc(v_a_4531_);
                        leanh::lean_dec_ref_known(v___x_4522_, 1);
                        v___x_4532_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_4533_ = lean_array_uset(v_bs_4517_, v_i_4516_, v___x_4532_);
                        v___x_4534_ = 1usize;
                        v___x_4535_ = lean_usize_add(v_i_4516_, v___x_4534_);
                        v___x_4536_ = lean_array_uset(v_bs_x27_4533_, v_i_4516_, v_a_4531_);
                        v_i_4516_ = v___x_4535_;
                        v_bs_4517_ = v___x_4536_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4526_ == 0 {
                    v___x_4528_ = v___x_4525_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4529_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_a_4523_);
                    v___x_4528_ = v_reuseFailAlloc_4529_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4528_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5_spec__7___redArg___boxed(
    mut v_f_4538_: *mut leanh::LeanObject,
    mut v_sz_4539_: *mut leanh::LeanObject,
    mut v_i_4540_: *mut leanh::LeanObject,
    mut v_bs_4541_: *mut leanh::LeanObject,
    mut v___y_4542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4543_: usize = 0;
    let mut v_i_boxed_4544_: usize = 0;
    let mut v_res_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4543_ = leanh::lean_unbox_usize(v_sz_4539_);
    leanh::lean_dec(v_sz_4539_);
    v_i_boxed_4544_ = leanh::lean_unbox_usize(v_i_4540_);
    leanh::lean_dec(v_i_4540_);
    v_res_4545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5_spec__7___redArg(v_f_4538_, v_sz_boxed_4543_, v_i_boxed_4544_, v_bs_4541_, v___y_4542_);
    leanh::lean_dec_ref(v___y_4542_);
    return v_res_4545_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5___redArg___boxed(
    mut v_f_4546_: *mut leanh::LeanObject,
    mut v_x_4547_: *mut leanh::LeanObject,
    mut v___y_4548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4549_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5___redArg(v_f_4546_, v_x_4547_, v___y_4548_);
    leanh::lean_dec_ref(v___y_4548_);
    return v_res_4549_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3___redArg(
    mut v_sz_4550_: usize,
    mut v_i_4551_: usize,
    mut v_bs_4552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4553_: u8 = 0;
    let mut v___x_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4560_: u8 = 0;
    let mut v___x_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4564_: u8 = 0;
    let mut v_a_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: usize = 0;
    let mut v___x_4569_: usize = 0;
    let mut v___x_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4553_ = lean_usize_dec_lt(v_i_4551_, v_sz_4550_);
                if v___x_4553_ == 0 {
                    v___x_4554_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4554_, 0, v_bs_4552_);
                    return v___x_4554_;
                } else {
                    v_v_4555_ = lean_array_uget_borrowed(v_bs_4552_, v_i_4551_);
                    leanh::lean_inc(v_v_4555_);
                    v___x_4556_ = l_Lean_Name_fromJson_x3f(v_v_4555_);
                    if leanh::lean_obj_tag(v___x_4556_) == 0 {
                        leanh::lean_dec_ref(v_bs_4552_);
                        v_a_4557_ = leanh::lean_ctor_get(v___x_4556_, 0);
                        v_isSharedCheck_4564_ =
                            (!leanh::lean_is_exclusive(v___x_4556_)) as u8;
                        if v_isSharedCheck_4564_ == 0 {
                            v___x_4559_ = v___x_4556_;
                            v_isShared_4560_ = v_isSharedCheck_4564_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4557_);
                            leanh::lean_dec(v___x_4556_);
                            v___x_4559_ = leanh::lean_box(0);
                            v_isShared_4560_ = v_isSharedCheck_4564_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4565_ = leanh::lean_ctor_get(v___x_4556_, 0);
                        leanh::lean_inc(v_a_4565_);
                        leanh::lean_dec_ref_known(v___x_4556_, 1);
                        v___x_4566_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_4567_ = lean_array_uset(v_bs_4552_, v_i_4551_, v___x_4566_);
                        v___x_4568_ = 1usize;
                        v___x_4569_ = lean_usize_add(v_i_4551_, v___x_4568_);
                        v___x_4570_ = lean_array_uset(v_bs_x27_4567_, v_i_4551_, v_a_4565_);
                        v_i_4551_ = v___x_4569_;
                        v_bs_4552_ = v___x_4570_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4560_ == 0 {
                    v___x_4562_ = v___x_4559_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4563_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4563_, 0, v_a_4557_);
                    v___x_4562_ = v_reuseFailAlloc_4563_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4562_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3___redArg___boxed(
    mut v_sz_4572_: *mut leanh::LeanObject,
    mut v_i_4573_: *mut leanh::LeanObject,
    mut v_bs_4574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4575_: usize = 0;
    let mut v_i_boxed_4576_: usize = 0;
    let mut v_res_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4575_ = leanh::lean_unbox_usize(v_sz_4572_);
    leanh::lean_dec(v_sz_4572_);
    v_i_boxed_4576_ = leanh::lean_unbox_usize(v_i_4573_);
    leanh::lean_dec(v_i_4573_);
    v_res_4577_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3___redArg(v_sz_boxed_4575_, v_i_boxed_4576_, v_bs_4574_);
    return v_res_4577_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0_spec__0(
    mut v_sz_4578_: usize,
    mut v_i_4579_: usize,
    mut v_bs_4580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4581_: u8 = 0;
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: usize = 0;
    let mut v___x_4587_: usize = 0;
    let mut v___x_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4581_ = lean_usize_dec_lt(v_i_4579_, v_sz_4578_);
                if v___x_4581_ == 0 {
                    v___x_4582_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4582_, 0, v_bs_4580_);
                    return v___x_4582_;
                } else {
                    v_v_4583_ = lean_array_uget(v_bs_4580_, v_i_4579_);
                    v___x_4584_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4585_ = lean_array_uset(v_bs_4580_, v_i_4579_, v___x_4584_);
                    v___x_4586_ = 1usize;
                    v___x_4587_ = lean_usize_add(v_i_4579_, v___x_4586_);
                    v___x_4588_ = lean_array_uset(v_bs_x27_4585_, v_i_4579_, v_v_4583_);
                    v_i_4579_ = v___x_4587_;
                    v_bs_4580_ = v___x_4588_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0_spec__0___boxed(
    mut v_sz_4590_: *mut leanh::LeanObject,
    mut v_i_4591_: *mut leanh::LeanObject,
    mut v_bs_4592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4593_: usize = 0;
    let mut v_i_boxed_4594_: usize = 0;
    let mut v_res_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4593_ = leanh::lean_unbox_usize(v_sz_4590_);
    leanh::lean_dec(v_sz_4590_);
    v_i_boxed_4594_ = leanh::lean_unbox_usize(v_i_4591_);
    leanh::lean_dec(v_i_4591_);
    v_res_4595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0_spec__0(v_sz_boxed_4593_, v_i_boxed_4594_, v_bs_4592_);
    return v_res_4595_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0(
    mut v_x_4598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4598_) == 4 {
        let mut v_elems_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4600_: usize = 0;
        let mut v___x_4601_: usize = 0;
        let mut v___x_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_elems_4599_ = leanh::lean_ctor_get(v_x_4598_, 0);
        leanh::lean_inc_ref(v_elems_4599_);
        leanh::lean_dec_ref_known(v_x_4598_, 1);
        v_sz_4600_ = lean_array_size(v_elems_4599_);
        v___x_4601_ = 0usize;
        v___x_4602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0_spec__0(v_sz_4600_, v___x_4601_, v_elems_4599_);
        return v___x_4602_;
    } else {
        let mut v___x_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4603_ = l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0___closed__0;
        v___x_4604_ = leanh::lean_unsigned_to_nat(80);
        v___x_4605_ = l_Lean_Json_pretty(v_x_4598_, v___x_4604_);
        v___x_4606_ = lean_string_append(v___x_4603_, v___x_4605_);
        leanh::lean_dec_ref(v___x_4605_);
        v___x_4607_ = l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0___closed__1;
        v___x_4608_ = lean_string_append(v___x_4606_, v___x_4607_);
        v___x_4609_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4609_, 0, v___x_4608_);
        return v___x_4609_;
    }
}
pub unsafe fn l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(
    mut v_json_4616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4622_: u8 = 0;
    let mut v___x_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: u8 = 0;
    let mut v___x_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: u8 = 0;
    let mut v___x_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: u8 = 0;
    let mut v___x_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4637_: u8 = 0;
    let mut v___x_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4641_: u8 = 0;
    let mut v_a_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4649_: u8 = 0;
    let mut v___x_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4656_: u8 = 0;
    let mut v___x_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4663_: u8 = 0;
    let mut v___x_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4667_: u8 = 0;
    let mut v_a_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4675_: u8 = 0;
    let mut v___x_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4679_: u8 = 0;
    let mut v_a_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4683_: u8 = 0;
    let mut v___x_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4690_: u8 = 0;
    let mut v___x_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4697_: u8 = 0;
    let mut v___x_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4701_: u8 = 0;
    let mut v_a_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4709_: u8 = 0;
    let mut v___x_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4713_: u8 = 0;
    let mut v_a_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4717_: u8 = 0;
    let mut v___x_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4724_: u8 = 0;
    let mut v_isSharedCheck_4725_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_json_4616_);
                v___x_4617_ = l_Lean_Json_getTag_x3f(v_json_4616_);
                if leanh::lean_obj_tag(v___x_4617_) == 0 {
                    leanh::lean_dec(v_json_4616_);
                    v___x_4618_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__1;
                    return v___x_4618_;
                } else {
                    v_val_4619_ = leanh::lean_ctor_get(v___x_4617_, 0);
                    v_isSharedCheck_4725_ = (!leanh::lean_is_exclusive(v___x_4617_)) as u8;
                    if v_isSharedCheck_4725_ == 0 {
                        v___x_4621_ = v___x_4617_;
                        v_isShared_4622_ = v_isSharedCheck_4725_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4619_);
                        leanh::lean_dec(v___x_4617_);
                        v___x_4621_ = leanh::lean_box(0);
                        v_isShared_4622_ = v_isSharedCheck_4725_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4623_ = leanh::lean_box(0);
                v___x_4624_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__1;
                v___x_4625_ = lean_string_dec_eq(v_val_4619_, v___x_4624_);
                if v___x_4625_ == 0 {
                    v___x_4626_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__0;
                    v___x_4627_ = lean_string_dec_eq(v_val_4619_, v___x_4626_);
                    if v___x_4627_ == 0 {
                        leanh::lean_del_object(v___x_4621_);
                        v___x_4628_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__2;
                        v___x_4629_ = lean_string_dec_eq(v_val_4619_, v___x_4628_);
                        leanh::lean_dec(v_val_4619_);
                        if v___x_4629_ == 0 {
                            leanh::lean_dec(v_json_4616_);
                            v___x_4630_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__3;
                            return v___x_4630_;
                        } else {
                            v___x_4631_ = leanh::lean_unsigned_to_nat(2);
                            v___x_4632_ = leanh::lean_box(0);
                            v___x_4633_ = l_Lean_Json_parseCtorFields(
                                v_json_4616_,
                                v___x_4628_,
                                v___x_4631_,
                                v___x_4632_,
                            );
                            if leanh::lean_obj_tag(v___x_4633_) == 0 {
                                v_a_4634_ = leanh::lean_ctor_get(v___x_4633_, 0);
                                v_isSharedCheck_4641_ =
                                    (!leanh::lean_is_exclusive(v___x_4633_)) as u8;
                                if v_isSharedCheck_4641_ == 0 {
                                    v___x_4636_ = v___x_4633_;
                                    v_isShared_4637_ = v_isSharedCheck_4641_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4634_);
                                    leanh::lean_dec(v___x_4633_);
                                    v___x_4636_ = leanh::lean_box(0);
                                    v_isShared_4637_ = v_isSharedCheck_4641_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_a_4642_ = leanh::lean_ctor_get(v___x_4633_, 0);
                                leanh::lean_inc(v_a_4642_);
                                leanh::lean_dec_ref_known(v___x_4633_, 1);
                                v___x_4643_ = leanh::lean_unsigned_to_nat(1);
                                v___x_4644_ =
                                    lean_array_get_borrowed(v___x_4623_, v_a_4642_, v___x_4643_);
                                leanh::lean_inc(v___x_4644_);
                                v___x_4645_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(v___x_4644_);
                                if leanh::lean_obj_tag(v___x_4645_) == 0 {
                                    leanh::lean_dec(v_a_4642_);
                                    return v___x_4645_;
                                } else {
                                    v_a_4646_ = leanh::lean_ctor_get(v___x_4645_, 0);
                                    v_isSharedCheck_4656_ =
                                        (!leanh::lean_is_exclusive(v___x_4645_)) as u8;
                                    if v_isSharedCheck_4656_ == 0 {
                                        v___x_4648_ = v___x_4645_;
                                        v_isShared_4649_ = v_isSharedCheck_4656_;
                                        state = 4;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4646_);
                                        leanh::lean_dec(v___x_4645_);
                                        v___x_4648_ = leanh::lean_box(0);
                                        v_isShared_4649_ = v_isSharedCheck_4656_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_val_4619_);
                        v___x_4657_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4658_ = leanh::lean_box(0);
                        v___x_4659_ = l_Lean_Json_parseCtorFields(
                            v_json_4616_,
                            v___x_4626_,
                            v___x_4657_,
                            v___x_4658_,
                        );
                        if leanh::lean_obj_tag(v___x_4659_) == 0 {
                            leanh::lean_del_object(v___x_4621_);
                            v_a_4660_ = leanh::lean_ctor_get(v___x_4659_, 0);
                            v_isSharedCheck_4667_ =
                                (!leanh::lean_is_exclusive(v___x_4659_)) as u8;
                            if v_isSharedCheck_4667_ == 0 {
                                v___x_4662_ = v___x_4659_;
                                v_isShared_4663_ = v_isSharedCheck_4667_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4660_);
                                leanh::lean_dec(v___x_4659_);
                                v___x_4662_ = leanh::lean_box(0);
                                v_isShared_4663_ = v_isSharedCheck_4667_;
                                state = 6;
                                continue;
                            }
                        } else {
                            v_a_4668_ = leanh::lean_ctor_get(v___x_4659_, 0);
                            leanh::lean_inc(v_a_4668_);
                            leanh::lean_dec_ref_known(v___x_4659_, 1);
                            v___x_4669_ = leanh::lean_unsigned_to_nat(0);
                            v___x_4670_ = lean_array_get(v___x_4623_, v_a_4668_, v___x_4669_);
                            leanh::lean_dec(v_a_4668_);
                            v___x_4671_ = l_Lean_Json_getStr_x3f(v___x_4670_);
                            if leanh::lean_obj_tag(v___x_4671_) == 0 {
                                leanh::lean_del_object(v___x_4621_);
                                v_a_4672_ = leanh::lean_ctor_get(v___x_4671_, 0);
                                v_isSharedCheck_4679_ =
                                    (!leanh::lean_is_exclusive(v___x_4671_)) as u8;
                                if v_isSharedCheck_4679_ == 0 {
                                    v___x_4674_ = v___x_4671_;
                                    v_isShared_4675_ = v_isSharedCheck_4679_;
                                    state = 8;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4672_);
                                    leanh::lean_dec(v___x_4671_);
                                    v___x_4674_ = leanh::lean_box(0);
                                    v_isShared_4675_ = v_isSharedCheck_4679_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                v_a_4680_ = leanh::lean_ctor_get(v___x_4671_, 0);
                                v_isSharedCheck_4690_ =
                                    (!leanh::lean_is_exclusive(v___x_4671_)) as u8;
                                if v_isSharedCheck_4690_ == 0 {
                                    v___x_4682_ = v___x_4671_;
                                    v_isShared_4683_ = v_isSharedCheck_4690_;
                                    state = 10;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4680_);
                                    leanh::lean_dec(v___x_4671_);
                                    v___x_4682_ = leanh::lean_box(0);
                                    v_isShared_4683_ = v_isSharedCheck_4690_;
                                    state = 10;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_val_4619_);
                    v___x_4691_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4692_ = leanh::lean_box(0);
                    v___x_4693_ = l_Lean_Json_parseCtorFields(
                        v_json_4616_,
                        v___x_4624_,
                        v___x_4691_,
                        v___x_4692_,
                    );
                    if leanh::lean_obj_tag(v___x_4693_) == 0 {
                        leanh::lean_del_object(v___x_4621_);
                        v_a_4694_ = leanh::lean_ctor_get(v___x_4693_, 0);
                        v_isSharedCheck_4701_ =
                            (!leanh::lean_is_exclusive(v___x_4693_)) as u8;
                        if v_isSharedCheck_4701_ == 0 {
                            v___x_4696_ = v___x_4693_;
                            v_isShared_4697_ = v_isSharedCheck_4701_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4694_);
                            leanh::lean_dec(v___x_4693_);
                            v___x_4696_ = leanh::lean_box(0);
                            v_isShared_4697_ = v_isSharedCheck_4701_;
                            state = 13;
                            continue;
                        }
                    } else {
                        v_a_4702_ = leanh::lean_ctor_get(v___x_4693_, 0);
                        leanh::lean_inc(v_a_4702_);
                        leanh::lean_dec_ref_known(v___x_4693_, 1);
                        v___x_4703_ = leanh::lean_unsigned_to_nat(0);
                        v___x_4704_ = lean_array_get(v___x_4623_, v_a_4702_, v___x_4703_);
                        leanh::lean_dec(v_a_4702_);
                        v___x_4705_ = l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4_spec__5(v___x_4704_);
                        if leanh::lean_obj_tag(v___x_4705_) == 0 {
                            leanh::lean_del_object(v___x_4621_);
                            v_a_4706_ = leanh::lean_ctor_get(v___x_4705_, 0);
                            v_isSharedCheck_4713_ =
                                (!leanh::lean_is_exclusive(v___x_4705_)) as u8;
                            if v_isSharedCheck_4713_ == 0 {
                                v___x_4708_ = v___x_4705_;
                                v_isShared_4709_ = v_isSharedCheck_4713_;
                                state = 15;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4706_);
                                leanh::lean_dec(v___x_4705_);
                                v___x_4708_ = leanh::lean_box(0);
                                v_isShared_4709_ = v_isSharedCheck_4713_;
                                state = 15;
                                continue;
                            }
                        } else {
                            v_a_4714_ = leanh::lean_ctor_get(v___x_4705_, 0);
                            v_isSharedCheck_4724_ =
                                (!leanh::lean_is_exclusive(v___x_4705_)) as u8;
                            if v_isSharedCheck_4724_ == 0 {
                                v___x_4716_ = v___x_4705_;
                                v_isShared_4717_ = v_isSharedCheck_4724_;
                                state = 17;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4714_);
                                leanh::lean_dec(v___x_4705_);
                                v___x_4716_ = leanh::lean_box(0);
                                v_isShared_4717_ = v_isSharedCheck_4724_;
                                state = 17;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                if v_isShared_4637_ == 0 {
                    v___x_4639_ = v___x_4636_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4640_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4640_, 0, v_a_4634_);
                    v___x_4639_ = v_reuseFailAlloc_4640_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4639_;
            }
            4 => {
                v___x_4650_ = leanh::lean_unsigned_to_nat(0);
                v___x_4651_ = lean_array_get(v___x_4623_, v_a_4642_, v___x_4650_);
                leanh::lean_dec(v_a_4642_);
                v___x_4652_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4652_, 0, v___x_4651_);
                leanh::lean_ctor_set(v___x_4652_, 1, v_a_4646_);
                if v_isShared_4649_ == 0 {
                    leanh::lean_ctor_set(v___x_4648_, 0, v___x_4652_);
                    v___x_4654_ = v___x_4648_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4655_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4655_, 0, v___x_4652_);
                    v___x_4654_ = v_reuseFailAlloc_4655_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4654_;
            }
            6 => {
                if v_isShared_4663_ == 0 {
                    v___x_4665_ = v___x_4662_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4666_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4666_, 0, v_a_4660_);
                    v___x_4665_ = v_reuseFailAlloc_4666_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4665_;
            }
            8 => {
                if v_isShared_4675_ == 0 {
                    v___x_4677_ = v___x_4674_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4678_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_a_4672_);
                    v___x_4677_ = v_reuseFailAlloc_4678_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4677_;
            }
            10 => {
                if v_isShared_4622_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4621_, 0);
                    leanh::lean_ctor_set(v___x_4621_, 0, v_a_4680_);
                    v___x_4685_ = v___x_4621_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4689_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4689_, 0, v_a_4680_);
                    v___x_4685_ = v_reuseFailAlloc_4689_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4683_ == 0 {
                    leanh::lean_ctor_set(v___x_4682_, 0, v___x_4685_);
                    v___x_4687_ = v___x_4682_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4688_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4688_, 0, v___x_4685_);
                    v___x_4687_ = v_reuseFailAlloc_4688_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4687_;
            }
            13 => {
                if v_isShared_4697_ == 0 {
                    v___x_4699_ = v___x_4696_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4700_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4700_, 0, v_a_4694_);
                    v___x_4699_ = v_reuseFailAlloc_4700_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4699_;
            }
            15 => {
                if v_isShared_4709_ == 0 {
                    v___x_4711_ = v___x_4708_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4712_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4712_, 0, v_a_4706_);
                    v___x_4711_ = v_reuseFailAlloc_4712_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4711_;
            }
            17 => {
                if v_isShared_4622_ == 0 {
                    leanh::lean_ctor_set(v___x_4621_, 0, v_a_4714_);
                    v___x_4719_ = v___x_4621_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4723_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4723_, 0, v_a_4714_);
                    v___x_4719_ = v_reuseFailAlloc_4723_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_4717_ == 0 {
                    leanh::lean_ctor_set(v___x_4716_, 0, v___x_4719_);
                    v___x_4721_ = v___x_4716_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4722_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4722_, 0, v___x_4719_);
                    v___x_4721_ = v_reuseFailAlloc_4722_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4721_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4_spec__5_spec__6(
    mut v_sz_4726_: usize,
    mut v_i_4727_: usize,
    mut v_bs_4728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4729_: u8 = 0;
    let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4736_: u8 = 0;
    let mut v___x_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4740_: u8 = 0;
    let mut v_a_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: usize = 0;
    let mut v___x_4745_: usize = 0;
    let mut v___x_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4729_ = lean_usize_dec_lt(v_i_4727_, v_sz_4726_);
                if v___x_4729_ == 0 {
                    v___x_4730_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4730_, 0, v_bs_4728_);
                    return v___x_4730_;
                } else {
                    v_v_4731_ = lean_array_uget_borrowed(v_bs_4728_, v_i_4727_);
                    leanh::lean_inc(v_v_4731_);
                    v___x_4732_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(v_v_4731_);
                    if leanh::lean_obj_tag(v___x_4732_) == 0 {
                        leanh::lean_dec_ref(v_bs_4728_);
                        v_a_4733_ = leanh::lean_ctor_get(v___x_4732_, 0);
                        v_isSharedCheck_4740_ =
                            (!leanh::lean_is_exclusive(v___x_4732_)) as u8;
                        if v_isSharedCheck_4740_ == 0 {
                            v___x_4735_ = v___x_4732_;
                            v_isShared_4736_ = v_isSharedCheck_4740_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4733_);
                            leanh::lean_dec(v___x_4732_);
                            v___x_4735_ = leanh::lean_box(0);
                            v_isShared_4736_ = v_isSharedCheck_4740_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4741_ = leanh::lean_ctor_get(v___x_4732_, 0);
                        leanh::lean_inc(v_a_4741_);
                        leanh::lean_dec_ref_known(v___x_4732_, 1);
                        v___x_4742_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_4743_ = lean_array_uset(v_bs_4728_, v_i_4727_, v___x_4742_);
                        v___x_4744_ = 1usize;
                        v___x_4745_ = lean_usize_add(v_i_4727_, v___x_4744_);
                        v___x_4746_ = lean_array_uset(v_bs_x27_4743_, v_i_4727_, v_a_4741_);
                        v_i_4727_ = v___x_4745_;
                        v_bs_4728_ = v___x_4746_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4736_ == 0 {
                    v___x_4738_ = v___x_4735_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4739_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4739_, 0, v_a_4733_);
                    v___x_4738_ = v_reuseFailAlloc_4739_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4738_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4_spec__5(
    mut v_x_4748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4748_) == 4 {
        let mut v_elems_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4750_: usize = 0;
        let mut v___x_4751_: usize = 0;
        let mut v___x_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_elems_4749_ = leanh::lean_ctor_get(v_x_4748_, 0);
        leanh::lean_inc_ref(v_elems_4749_);
        leanh::lean_dec_ref_known(v_x_4748_, 1);
        v_sz_4750_ = lean_array_size(v_elems_4749_);
        v___x_4751_ = 0usize;
        v___x_4752_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4_spec__5_spec__6(v_sz_4750_, v___x_4751_, v_elems_4749_);
        return v___x_4752_;
    } else {
        let mut v___x_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4753_ = l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0___closed__0;
        v___x_4754_ = leanh::lean_unsigned_to_nat(80);
        v___x_4755_ = l_Lean_Json_pretty(v_x_4748_, v___x_4754_);
        v___x_4756_ = lean_string_append(v___x_4753_, v___x_4755_);
        leanh::lean_dec_ref(v___x_4755_);
        v___x_4757_ = l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0___closed__1;
        v___x_4758_ = lean_string_append(v___x_4756_, v___x_4757_);
        v___x_4759_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4759_, 0, v___x_4758_);
        return v___x_4759_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4_spec__5_spec__6___boxed(
    mut v_sz_4760_: *mut leanh::LeanObject,
    mut v_i_4761_: *mut leanh::LeanObject,
    mut v_bs_4762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4763_: usize = 0;
    let mut v_i_boxed_4764_: usize = 0;
    let mut v_res_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4763_ = leanh::lean_unbox_usize(v_sz_4760_);
    leanh::lean_dec(v_sz_4760_);
    v_i_boxed_4764_ = leanh::lean_unbox_usize(v_i_4761_);
    leanh::lean_dec(v_i_4761_);
    v_res_4765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4_spec__5_spec__6(v_sz_boxed_4763_, v_i_boxed_4764_, v_bs_4762_);
    return v_res_4765_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___redArg(
    mut v_sz_4766_: usize,
    mut v_i_4767_: usize,
    mut v_bs_4768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4769_: u8 = 0;
    let mut v___x_4770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4776_: u8 = 0;
    let mut v___x_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4780_: u8 = 0;
    let mut v_a_4781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: usize = 0;
    let mut v___x_4785_: usize = 0;
    let mut v___x_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4769_ = lean_usize_dec_lt(v_i_4767_, v_sz_4766_);
                if v___x_4769_ == 0 {
                    v___x_4770_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4770_, 0, v_bs_4768_);
                    return v___x_4770_;
                } else {
                    v_v_4771_ = lean_array_uget_borrowed(v_bs_4768_, v_i_4767_);
                    leanh::lean_inc(v_v_4771_);
                    v___x_4772_ = l_Lean_Json_getStr_x3f(v_v_4771_);
                    if leanh::lean_obj_tag(v___x_4772_) == 0 {
                        leanh::lean_dec_ref(v_bs_4768_);
                        v_a_4773_ = leanh::lean_ctor_get(v___x_4772_, 0);
                        v_isSharedCheck_4780_ =
                            (!leanh::lean_is_exclusive(v___x_4772_)) as u8;
                        if v_isSharedCheck_4780_ == 0 {
                            v___x_4775_ = v___x_4772_;
                            v_isShared_4776_ = v_isSharedCheck_4780_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4773_);
                            leanh::lean_dec(v___x_4772_);
                            v___x_4775_ = leanh::lean_box(0);
                            v_isShared_4776_ = v_isSharedCheck_4780_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4781_ = leanh::lean_ctor_get(v___x_4772_, 0);
                        leanh::lean_inc(v_a_4781_);
                        leanh::lean_dec_ref_known(v___x_4772_, 1);
                        v___x_4782_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_4783_ = lean_array_uset(v_bs_4768_, v_i_4767_, v___x_4782_);
                        v___x_4784_ = 1usize;
                        v___x_4785_ = lean_usize_add(v_i_4767_, v___x_4784_);
                        v___x_4786_ = lean_array_uset(v_bs_x27_4783_, v_i_4767_, v_a_4781_);
                        v_i_4767_ = v___x_4785_;
                        v_bs_4768_ = v___x_4786_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4776_ == 0 {
                    v___x_4778_ = v___x_4775_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4779_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4779_, 0, v_a_4773_);
                    v___x_4778_ = v_reuseFailAlloc_4779_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4778_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___redArg___boxed(
    mut v_sz_4788_: *mut leanh::LeanObject,
    mut v_i_4789_: *mut leanh::LeanObject,
    mut v_bs_4790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4791_: usize = 0;
    let mut v_i_boxed_4792_: usize = 0;
    let mut v_res_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4791_ = leanh::lean_unbox_usize(v_sz_4788_);
    leanh::lean_dec(v_sz_4788_);
    v_i_boxed_4792_ = leanh::lean_unbox_usize(v_i_4789_);
    leanh::lean_dec(v_i_4789_);
    v_res_4793_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___redArg(v_sz_boxed_4791_, v_i_boxed_4792_, v_bs_4790_);
    return v_res_4793_;
}
pub unsafe fn l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_(
    mut v_j_4795_: *mut leanh::LeanObject,
    mut v_a_4796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4801_: u8 = 0;
    let mut v___x_4803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4805_: u8 = 0;
    let mut v_a_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_names_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarIds_4808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_x3f_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInstance_x3f_4811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isType_x3f_4812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInserted_x3f_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRemoved_x3f_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4817_: u8 = 0;
    let mut v___x_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4822_: u8 = 0;
    let mut v___x_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4826_: u8 = 0;
    let mut v_a_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4828_: usize = 0;
    let mut v___x_4829_: usize = 0;
    let mut v___x_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4834_: u8 = 0;
    let mut v___x_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4838_: u8 = 0;
    let mut v_a_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4844_: u8 = 0;
    let mut v___x_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4848_: u8 = 0;
    let mut v_a_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4850_: usize = 0;
    let mut v___x_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4855_: u8 = 0;
    let mut v___x_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4859_: u8 = 0;
    let mut v_a_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4865_: u8 = 0;
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4869_: u8 = 0;
    let mut v_a_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4876_: u8 = 0;
    let mut v___x_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4880_: u8 = 0;
    let mut v_a_4881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4884_: u8 = 0;
    let mut v___y_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_____do__lift_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_____do__lift_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4906_: u8 = 0;
    let mut v___x_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4911_: u8 = 0;
    let mut v___x_4913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4915_: u8 = 0;
    let mut v_a_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4920_: u8 = 0;
    let mut v___y_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_____do__lift_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4929_: u8 = 0;
    let mut v___x_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4934_: u8 = 0;
    let mut v___x_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4938_: u8 = 0;
    let mut v_a_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4943_: u8 = 0;
    let mut v___y_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_____do__lift_4946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4951_: u8 = 0;
    let mut v___x_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4956_: u8 = 0;
    let mut v___x_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4960_: u8 = 0;
    let mut v_a_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4965_: u8 = 0;
    let mut v_____do__lift_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4972_: u8 = 0;
    let mut v___x_4973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4977_: u8 = 0;
    let mut v___x_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4981_: u8 = 0;
    let mut v_a_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4986_: u8 = 0;
    let mut v___x_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4991_: u8 = 0;
    let mut v___x_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4996_: u8 = 0;
    let mut v___x_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5000_: u8 = 0;
    let mut v_a_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5006_: u8 = 0;
    let mut v___x_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5010_: u8 = 0;
    let mut v_a_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5015_: u8 = 0;
    let mut v_isSharedCheck_5016_: u8 = 0;
    let mut v_isSharedCheck_5017_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4797_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_(v_j_4795_);
                if leanh::lean_obj_tag(v___x_4797_) == 0 {
                    v_a_4798_ = leanh::lean_ctor_get(v___x_4797_, 0);
                    v_isSharedCheck_4805_ = (!leanh::lean_is_exclusive(v___x_4797_)) as u8;
                    if v_isSharedCheck_4805_ == 0 {
                        v___x_4800_ = v___x_4797_;
                        v_isShared_4801_ = v_isSharedCheck_4805_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4798_);
                        leanh::lean_dec(v___x_4797_);
                        v___x_4800_ = leanh::lean_box(0);
                        v_isShared_4801_ = v_isSharedCheck_4805_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4806_ = leanh::lean_ctor_get(v___x_4797_, 0);
                    leanh::lean_inc(v_a_4806_);
                    leanh::lean_dec_ref_known(v___x_4797_, 1);
                    v_names_4807_ = leanh::lean_ctor_get(v_a_4806_, 0);
                    v_fvarIds_4808_ = leanh::lean_ctor_get(v_a_4806_, 1);
                    v_type_4809_ = leanh::lean_ctor_get(v_a_4806_, 2);
                    v_val_x3f_4810_ = leanh::lean_ctor_get(v_a_4806_, 3);
                    v_isInstance_x3f_4811_ = leanh::lean_ctor_get(v_a_4806_, 4);
                    v_isType_x3f_4812_ = leanh::lean_ctor_get(v_a_4806_, 5);
                    v_isInserted_x3f_4813_ = leanh::lean_ctor_get(v_a_4806_, 6);
                    v_isRemoved_x3f_4814_ = leanh::lean_ctor_get(v_a_4806_, 7);
                    v_isSharedCheck_5017_ = (!leanh::lean_is_exclusive(v_a_4806_)) as u8;
                    if v_isSharedCheck_5017_ == 0 {
                        v___x_4816_ = v_a_4806_;
                        v_isShared_4817_ = v_isSharedCheck_5017_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_isRemoved_x3f_4814_);
                        leanh::lean_inc(v_isInserted_x3f_4813_);
                        leanh::lean_inc(v_isType_x3f_4812_);
                        leanh::lean_inc(v_isInstance_x3f_4811_);
                        leanh::lean_inc(v_val_x3f_4810_);
                        leanh::lean_inc(v_type_4809_);
                        leanh::lean_inc(v_fvarIds_4808_);
                        leanh::lean_inc(v_names_4807_);
                        leanh::lean_dec(v_a_4806_);
                        v___x_4816_ = leanh::lean_box(0);
                        v_isShared_4817_ = v_isSharedCheck_5017_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4801_ == 0 {
                    v___x_4803_ = v___x_4800_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4804_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_a_4798_);
                    v___x_4803_ = v_reuseFailAlloc_4804_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4803_;
            }
            3 => {
                v___x_4818_ = l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0(v_names_4807_);
                if leanh::lean_obj_tag(v___x_4818_) == 0 {
                    leanh::lean_del_object(v___x_4816_);
                    leanh::lean_dec(v_isRemoved_x3f_4814_);
                    leanh::lean_dec(v_isInserted_x3f_4813_);
                    leanh::lean_dec(v_isType_x3f_4812_);
                    leanh::lean_dec(v_isInstance_x3f_4811_);
                    leanh::lean_dec(v_val_x3f_4810_);
                    leanh::lean_dec(v_type_4809_);
                    leanh::lean_dec(v_fvarIds_4808_);
                    v_a_4819_ = leanh::lean_ctor_get(v___x_4818_, 0);
                    v_isSharedCheck_4826_ = (!leanh::lean_is_exclusive(v___x_4818_)) as u8;
                    if v_isSharedCheck_4826_ == 0 {
                        v___x_4821_ = v___x_4818_;
                        v_isShared_4822_ = v_isSharedCheck_4826_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4819_);
                        leanh::lean_dec(v___x_4818_);
                        v___x_4821_ = leanh::lean_box(0);
                        v_isShared_4822_ = v_isSharedCheck_4826_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_4827_ = leanh::lean_ctor_get(v___x_4818_, 0);
                    leanh::lean_inc(v_a_4827_);
                    leanh::lean_dec_ref_known(v___x_4818_, 1);
                    v_sz_4828_ = lean_array_size(v_a_4827_);
                    v___x_4829_ = 0usize;
                    v___x_4830_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___redArg(v_sz_4828_, v___x_4829_, v_a_4827_);
                    if leanh::lean_obj_tag(v___x_4830_) == 0 {
                        leanh::lean_del_object(v___x_4816_);
                        leanh::lean_dec(v_isRemoved_x3f_4814_);
                        leanh::lean_dec(v_isInserted_x3f_4813_);
                        leanh::lean_dec(v_isType_x3f_4812_);
                        leanh::lean_dec(v_isInstance_x3f_4811_);
                        leanh::lean_dec(v_val_x3f_4810_);
                        leanh::lean_dec(v_type_4809_);
                        leanh::lean_dec(v_fvarIds_4808_);
                        v_a_4831_ = leanh::lean_ctor_get(v___x_4830_, 0);
                        v_isSharedCheck_4838_ =
                            (!leanh::lean_is_exclusive(v___x_4830_)) as u8;
                        if v_isSharedCheck_4838_ == 0 {
                            v___x_4833_ = v___x_4830_;
                            v_isShared_4834_ = v_isSharedCheck_4838_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4831_);
                            leanh::lean_dec(v___x_4830_);
                            v___x_4833_ = leanh::lean_box(0);
                            v_isShared_4834_ = v_isSharedCheck_4838_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_4839_ = leanh::lean_ctor_get(v___x_4830_, 0);
                        leanh::lean_inc(v_a_4839_);
                        leanh::lean_dec_ref_known(v___x_4830_, 1);
                        v___x_4840_ = l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0(v_fvarIds_4808_);
                        if leanh::lean_obj_tag(v___x_4840_) == 0 {
                            leanh::lean_dec(v_a_4839_);
                            leanh::lean_del_object(v___x_4816_);
                            leanh::lean_dec(v_isRemoved_x3f_4814_);
                            leanh::lean_dec(v_isInserted_x3f_4813_);
                            leanh::lean_dec(v_isType_x3f_4812_);
                            leanh::lean_dec(v_isInstance_x3f_4811_);
                            leanh::lean_dec(v_val_x3f_4810_);
                            leanh::lean_dec(v_type_4809_);
                            v_a_4841_ = leanh::lean_ctor_get(v___x_4840_, 0);
                            v_isSharedCheck_4848_ =
                                (!leanh::lean_is_exclusive(v___x_4840_)) as u8;
                            if v_isSharedCheck_4848_ == 0 {
                                v___x_4843_ = v___x_4840_;
                                v_isShared_4844_ = v_isSharedCheck_4848_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4841_);
                                leanh::lean_dec(v___x_4840_);
                                v___x_4843_ = leanh::lean_box(0);
                                v_isShared_4844_ = v_isSharedCheck_4848_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v_a_4849_ = leanh::lean_ctor_get(v___x_4840_, 0);
                            leanh::lean_inc(v_a_4849_);
                            leanh::lean_dec_ref_known(v___x_4840_, 1);
                            v_sz_4850_ = lean_array_size(v_a_4849_);
                            v___x_4851_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3___redArg(v_sz_4850_, v___x_4829_, v_a_4849_);
                            if leanh::lean_obj_tag(v___x_4851_) == 0 {
                                leanh::lean_dec(v_a_4839_);
                                leanh::lean_del_object(v___x_4816_);
                                leanh::lean_dec(v_isRemoved_x3f_4814_);
                                leanh::lean_dec(v_isInserted_x3f_4813_);
                                leanh::lean_dec(v_isType_x3f_4812_);
                                leanh::lean_dec(v_isInstance_x3f_4811_);
                                leanh::lean_dec(v_val_x3f_4810_);
                                leanh::lean_dec(v_type_4809_);
                                v_a_4852_ = leanh::lean_ctor_get(v___x_4851_, 0);
                                v_isSharedCheck_4859_ =
                                    (!leanh::lean_is_exclusive(v___x_4851_)) as u8;
                                if v_isSharedCheck_4859_ == 0 {
                                    v___x_4854_ = v___x_4851_;
                                    v_isShared_4855_ = v_isSharedCheck_4859_;
                                    state = 10;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4852_);
                                    leanh::lean_dec(v___x_4851_);
                                    v___x_4854_ = leanh::lean_box(0);
                                    v_isShared_4855_ = v_isSharedCheck_4859_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                v_a_4860_ = leanh::lean_ctor_get(v___x_4851_, 0);
                                leanh::lean_inc(v_a_4860_);
                                leanh::lean_dec_ref_known(v___x_4851_, 1);
                                v___x_4861_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(v_type_4809_);
                                if leanh::lean_obj_tag(v___x_4861_) == 0 {
                                    leanh::lean_dec(v_a_4860_);
                                    leanh::lean_dec(v_a_4839_);
                                    leanh::lean_del_object(v___x_4816_);
                                    leanh::lean_dec(v_isRemoved_x3f_4814_);
                                    leanh::lean_dec(v_isInserted_x3f_4813_);
                                    leanh::lean_dec(v_isType_x3f_4812_);
                                    leanh::lean_dec(v_isInstance_x3f_4811_);
                                    leanh::lean_dec(v_val_x3f_4810_);
                                    v_a_4862_ = leanh::lean_ctor_get(v___x_4861_, 0);
                                    v_isSharedCheck_4869_ =
                                        (!leanh::lean_is_exclusive(v___x_4861_)) as u8;
                                    if v_isSharedCheck_4869_ == 0 {
                                        v___x_4864_ = v___x_4861_;
                                        v_isShared_4865_ = v_isSharedCheck_4869_;
                                        state = 12;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4862_);
                                        leanh::lean_dec(v___x_4861_);
                                        v___x_4864_ = leanh::lean_box(0);
                                        v_isShared_4865_ = v_isSharedCheck_4869_;
                                        state = 12;
                                        continue;
                                    }
                                } else {
                                    v_a_4870_ = leanh::lean_ctor_get(v___x_4861_, 0);
                                    leanh::lean_inc(v_a_4870_);
                                    leanh::lean_dec_ref_known(v___x_4861_, 1);
                                    v___x_4871_ = l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec___closed__0_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_;
                                    v___x_4872_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5___redArg(v___x_4871_, v_a_4870_, v_a_4796_);
                                    if leanh::lean_obj_tag(v___x_4872_) == 0 {
                                        leanh::lean_dec(v_a_4860_);
                                        leanh::lean_dec(v_a_4839_);
                                        leanh::lean_del_object(v___x_4816_);
                                        leanh::lean_dec(v_isRemoved_x3f_4814_);
                                        leanh::lean_dec(v_isInserted_x3f_4813_);
                                        leanh::lean_dec(v_isType_x3f_4812_);
                                        leanh::lean_dec(v_isInstance_x3f_4811_);
                                        leanh::lean_dec(v_val_x3f_4810_);
                                        v_a_4873_ = leanh::lean_ctor_get(v___x_4872_, 0);
                                        v_isSharedCheck_4880_ =
                                            (!leanh::lean_is_exclusive(v___x_4872_)) as u8;
                                        if v_isSharedCheck_4880_ == 0 {
                                            v___x_4875_ = v___x_4872_;
                                            v_isShared_4876_ = v_isSharedCheck_4880_;
                                            state = 14;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_4873_);
                                            leanh::lean_dec(v___x_4872_);
                                            v___x_4875_ = leanh::lean_box(0);
                                            v_isShared_4876_ = v_isSharedCheck_4880_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_a_4881_ = leanh::lean_ctor_get(v___x_4872_, 0);
                                        v_isSharedCheck_5016_ =
                                            (!leanh::lean_is_exclusive(v___x_4872_)) as u8;
                                        if v_isSharedCheck_5016_ == 0 {
                                            v___x_4883_ = v___x_4872_;
                                            v_isShared_4884_ = v_isSharedCheck_5016_;
                                            state = 16;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_4881_);
                                            leanh::lean_dec(v___x_4872_);
                                            v___x_4883_ = leanh::lean_box(0);
                                            v_isShared_4884_ = v_isSharedCheck_5016_;
                                            state = 16;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            4 => {
                if v_isShared_4822_ == 0 {
                    v___x_4824_ = v___x_4821_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4825_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4825_, 0, v_a_4819_);
                    v___x_4824_ = v_reuseFailAlloc_4825_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4824_;
            }
            6 => {
                if v_isShared_4834_ == 0 {
                    v___x_4836_ = v___x_4833_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4837_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4837_, 0, v_a_4831_);
                    v___x_4836_ = v_reuseFailAlloc_4837_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4836_;
            }
            8 => {
                if v_isShared_4844_ == 0 {
                    v___x_4846_ = v___x_4843_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4847_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4847_, 0, v_a_4841_);
                    v___x_4846_ = v_reuseFailAlloc_4847_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4846_;
            }
            10 => {
                if v_isShared_4855_ == 0 {
                    v___x_4857_ = v___x_4854_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4858_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_a_4852_);
                    v___x_4857_ = v_reuseFailAlloc_4858_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4857_;
            }
            12 => {
                if v_isShared_4865_ == 0 {
                    v___x_4867_ = v___x_4864_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4868_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4868_, 0, v_a_4862_);
                    v___x_4867_ = v_reuseFailAlloc_4868_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4867_;
            }
            14 => {
                if v_isShared_4876_ == 0 {
                    v___x_4878_ = v___x_4875_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4879_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4879_, 0, v_a_4873_);
                    v___x_4878_ = v_reuseFailAlloc_4879_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4878_;
            }
            16 => {
                if leanh::lean_obj_tag(v_val_x3f_4810_) == 0 {
                    v___x_4987_ = leanh::lean_box(0);
                    v_____do__lift_4967_ = v___x_4987_;
                    state = 35;
                    continue;
                } else {
                    v_val_4988_ = leanh::lean_ctor_get(v_val_x3f_4810_, 0);
                    v_isSharedCheck_5015_ =
                        (!leanh::lean_is_exclusive(v_val_x3f_4810_)) as u8;
                    if v_isSharedCheck_5015_ == 0 {
                        v___x_4990_ = v_val_x3f_4810_;
                        v_isShared_4991_ = v_isSharedCheck_5015_;
                        state = 40;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4988_);
                        leanh::lean_dec(v_val_x3f_4810_);
                        v___x_4990_ = leanh::lean_box(0);
                        v_isShared_4991_ = v_isSharedCheck_5015_;
                        state = 40;
                        continue;
                    }
                }
            }
            17 => {
                if v_isShared_4817_ == 0 {
                    leanh::lean_ctor_set(v___x_4816_, 7, v_____do__lift_4890_);
                    leanh::lean_ctor_set(v___x_4816_, 6, v___y_4887_);
                    leanh::lean_ctor_set(v___x_4816_, 5, v___y_4889_);
                    leanh::lean_ctor_set(v___x_4816_, 4, v___y_4886_);
                    leanh::lean_ctor_set(v___x_4816_, 3, v___y_4888_);
                    leanh::lean_ctor_set(v___x_4816_, 2, v_a_4881_);
                    leanh::lean_ctor_set(v___x_4816_, 1, v_a_4860_);
                    leanh::lean_ctor_set(v___x_4816_, 0, v_a_4839_);
                    v___x_4892_ = v___x_4816_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4896_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4896_, 0, v_a_4839_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4896_, 1, v_a_4860_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4896_, 2, v_a_4881_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4896_, 3, v___y_4888_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4896_, 4, v___y_4886_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4896_, 5, v___y_4889_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4896_, 6, v___y_4887_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4896_, 7, v_____do__lift_4890_);
                    v___x_4892_ = v_reuseFailAlloc_4896_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_4884_ == 0 {
                    leanh::lean_ctor_set(v___x_4883_, 0, v___x_4892_);
                    v___x_4894_ = v___x_4883_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4895_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4895_, 0, v___x_4892_);
                    v___x_4894_ = v_reuseFailAlloc_4895_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4894_;
            }
            20 => {
                if leanh::lean_obj_tag(v_isRemoved_x3f_4814_) == 0 {
                    v___x_4902_ = leanh::lean_box(0);
                    v___y_4886_ = v___y_4898_;
                    v___y_4887_ = v_____do__lift_4901_;
                    v___y_4888_ = v___y_4899_;
                    v___y_4889_ = v___y_4900_;
                    v_____do__lift_4890_ = v___x_4902_;
                    state = 17;
                    continue;
                } else {
                    v_val_4903_ = leanh::lean_ctor_get(v_isRemoved_x3f_4814_, 0);
                    v_isSharedCheck_4920_ =
                        (!leanh::lean_is_exclusive(v_isRemoved_x3f_4814_)) as u8;
                    if v_isSharedCheck_4920_ == 0 {
                        v___x_4905_ = v_isRemoved_x3f_4814_;
                        v_isShared_4906_ = v_isSharedCheck_4920_;
                        state = 21;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4903_);
                        leanh::lean_dec(v_isRemoved_x3f_4814_);
                        v___x_4905_ = leanh::lean_box(0);
                        v_isShared_4906_ = v_isSharedCheck_4920_;
                        state = 21;
                        continue;
                    }
                }
            }
            21 => {
                v___x_4907_ = l_Lean_Json_getBool_x3f(v_val_4903_);
                leanh::lean_dec(v_val_4903_);
                if leanh::lean_obj_tag(v___x_4907_) == 0 {
                    leanh::lean_del_object(v___x_4905_);
                    leanh::lean_dec(v_____do__lift_4901_);
                    leanh::lean_dec(v___y_4900_);
                    leanh::lean_dec(v___y_4899_);
                    leanh::lean_dec(v___y_4898_);
                    leanh::lean_del_object(v___x_4883_);
                    leanh::lean_dec(v_a_4881_);
                    leanh::lean_dec(v_a_4860_);
                    leanh::lean_dec(v_a_4839_);
                    leanh::lean_del_object(v___x_4816_);
                    v_a_4908_ = leanh::lean_ctor_get(v___x_4907_, 0);
                    v_isSharedCheck_4915_ = (!leanh::lean_is_exclusive(v___x_4907_)) as u8;
                    if v_isSharedCheck_4915_ == 0 {
                        v___x_4910_ = v___x_4907_;
                        v_isShared_4911_ = v_isSharedCheck_4915_;
                        state = 22;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4908_);
                        leanh::lean_dec(v___x_4907_);
                        v___x_4910_ = leanh::lean_box(0);
                        v_isShared_4911_ = v_isSharedCheck_4915_;
                        state = 22;
                        continue;
                    }
                } else {
                    v_a_4916_ = leanh::lean_ctor_get(v___x_4907_, 0);
                    leanh::lean_inc(v_a_4916_);
                    leanh::lean_dec_ref_known(v___x_4907_, 1);
                    if v_isShared_4906_ == 0 {
                        leanh::lean_ctor_set(v___x_4905_, 0, v_a_4916_);
                        v___x_4918_ = v___x_4905_;
                        state = 24;
                        continue;
                    } else {
                        v_reuseFailAlloc_4919_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4919_, 0, v_a_4916_);
                        v___x_4918_ = v_reuseFailAlloc_4919_;
                        state = 24;
                        continue;
                    }
                }
            }
            22 => {
                if v_isShared_4911_ == 0 {
                    v___x_4913_ = v___x_4910_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4914_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4914_, 0, v_a_4908_);
                    v___x_4913_ = v_reuseFailAlloc_4914_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_4913_;
            }
            24 => {
                v___y_4886_ = v___y_4898_;
                v___y_4887_ = v_____do__lift_4901_;
                v___y_4888_ = v___y_4899_;
                v___y_4889_ = v___y_4900_;
                v_____do__lift_4890_ = v___x_4918_;
                state = 17;
                continue;
            }
            25 => {
                if leanh::lean_obj_tag(v_isInserted_x3f_4813_) == 0 {
                    v___x_4925_ = leanh::lean_box(0);
                    v___y_4898_ = v___y_4922_;
                    v___y_4899_ = v___y_4923_;
                    v___y_4900_ = v_____do__lift_4924_;
                    v_____do__lift_4901_ = v___x_4925_;
                    state = 20;
                    continue;
                } else {
                    v_val_4926_ = leanh::lean_ctor_get(v_isInserted_x3f_4813_, 0);
                    v_isSharedCheck_4943_ =
                        (!leanh::lean_is_exclusive(v_isInserted_x3f_4813_)) as u8;
                    if v_isSharedCheck_4943_ == 0 {
                        v___x_4928_ = v_isInserted_x3f_4813_;
                        v_isShared_4929_ = v_isSharedCheck_4943_;
                        state = 26;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4926_);
                        leanh::lean_dec(v_isInserted_x3f_4813_);
                        v___x_4928_ = leanh::lean_box(0);
                        v_isShared_4929_ = v_isSharedCheck_4943_;
                        state = 26;
                        continue;
                    }
                }
            }
            26 => {
                v___x_4930_ = l_Lean_Json_getBool_x3f(v_val_4926_);
                leanh::lean_dec(v_val_4926_);
                if leanh::lean_obj_tag(v___x_4930_) == 0 {
                    leanh::lean_del_object(v___x_4928_);
                    leanh::lean_dec(v_____do__lift_4924_);
                    leanh::lean_dec(v___y_4923_);
                    leanh::lean_dec(v___y_4922_);
                    leanh::lean_del_object(v___x_4883_);
                    leanh::lean_dec(v_a_4881_);
                    leanh::lean_dec(v_a_4860_);
                    leanh::lean_dec(v_a_4839_);
                    leanh::lean_del_object(v___x_4816_);
                    leanh::lean_dec(v_isRemoved_x3f_4814_);
                    v_a_4931_ = leanh::lean_ctor_get(v___x_4930_, 0);
                    v_isSharedCheck_4938_ = (!leanh::lean_is_exclusive(v___x_4930_)) as u8;
                    if v_isSharedCheck_4938_ == 0 {
                        v___x_4933_ = v___x_4930_;
                        v_isShared_4934_ = v_isSharedCheck_4938_;
                        state = 27;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4931_);
                        leanh::lean_dec(v___x_4930_);
                        v___x_4933_ = leanh::lean_box(0);
                        v_isShared_4934_ = v_isSharedCheck_4938_;
                        state = 27;
                        continue;
                    }
                } else {
                    v_a_4939_ = leanh::lean_ctor_get(v___x_4930_, 0);
                    leanh::lean_inc(v_a_4939_);
                    leanh::lean_dec_ref_known(v___x_4930_, 1);
                    if v_isShared_4929_ == 0 {
                        leanh::lean_ctor_set(v___x_4928_, 0, v_a_4939_);
                        v___x_4941_ = v___x_4928_;
                        state = 29;
                        continue;
                    } else {
                        v_reuseFailAlloc_4942_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4942_, 0, v_a_4939_);
                        v___x_4941_ = v_reuseFailAlloc_4942_;
                        state = 29;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_4934_ == 0 {
                    v___x_4936_ = v___x_4933_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4937_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4937_, 0, v_a_4931_);
                    v___x_4936_ = v_reuseFailAlloc_4937_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_4936_;
            }
            29 => {
                v___y_4898_ = v___y_4922_;
                v___y_4899_ = v___y_4923_;
                v___y_4900_ = v_____do__lift_4924_;
                v_____do__lift_4901_ = v___x_4941_;
                state = 20;
                continue;
            }
            30 => {
                if leanh::lean_obj_tag(v_isType_x3f_4812_) == 0 {
                    v___x_4947_ = leanh::lean_box(0);
                    v___y_4922_ = v_____do__lift_4946_;
                    v___y_4923_ = v___y_4945_;
                    v_____do__lift_4924_ = v___x_4947_;
                    state = 25;
                    continue;
                } else {
                    v_val_4948_ = leanh::lean_ctor_get(v_isType_x3f_4812_, 0);
                    v_isSharedCheck_4965_ =
                        (!leanh::lean_is_exclusive(v_isType_x3f_4812_)) as u8;
                    if v_isSharedCheck_4965_ == 0 {
                        v___x_4950_ = v_isType_x3f_4812_;
                        v_isShared_4951_ = v_isSharedCheck_4965_;
                        state = 31;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4948_);
                        leanh::lean_dec(v_isType_x3f_4812_);
                        v___x_4950_ = leanh::lean_box(0);
                        v_isShared_4951_ = v_isSharedCheck_4965_;
                        state = 31;
                        continue;
                    }
                }
            }
            31 => {
                v___x_4952_ = l_Lean_Json_getBool_x3f(v_val_4948_);
                leanh::lean_dec(v_val_4948_);
                if leanh::lean_obj_tag(v___x_4952_) == 0 {
                    leanh::lean_del_object(v___x_4950_);
                    leanh::lean_dec(v_____do__lift_4946_);
                    leanh::lean_dec(v___y_4945_);
                    leanh::lean_del_object(v___x_4883_);
                    leanh::lean_dec(v_a_4881_);
                    leanh::lean_dec(v_a_4860_);
                    leanh::lean_dec(v_a_4839_);
                    leanh::lean_del_object(v___x_4816_);
                    leanh::lean_dec(v_isRemoved_x3f_4814_);
                    leanh::lean_dec(v_isInserted_x3f_4813_);
                    v_a_4953_ = leanh::lean_ctor_get(v___x_4952_, 0);
                    v_isSharedCheck_4960_ = (!leanh::lean_is_exclusive(v___x_4952_)) as u8;
                    if v_isSharedCheck_4960_ == 0 {
                        v___x_4955_ = v___x_4952_;
                        v_isShared_4956_ = v_isSharedCheck_4960_;
                        state = 32;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4953_);
                        leanh::lean_dec(v___x_4952_);
                        v___x_4955_ = leanh::lean_box(0);
                        v_isShared_4956_ = v_isSharedCheck_4960_;
                        state = 32;
                        continue;
                    }
                } else {
                    v_a_4961_ = leanh::lean_ctor_get(v___x_4952_, 0);
                    leanh::lean_inc(v_a_4961_);
                    leanh::lean_dec_ref_known(v___x_4952_, 1);
                    if v_isShared_4951_ == 0 {
                        leanh::lean_ctor_set(v___x_4950_, 0, v_a_4961_);
                        v___x_4963_ = v___x_4950_;
                        state = 34;
                        continue;
                    } else {
                        v_reuseFailAlloc_4964_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4964_, 0, v_a_4961_);
                        v___x_4963_ = v_reuseFailAlloc_4964_;
                        state = 34;
                        continue;
                    }
                }
            }
            32 => {
                if v_isShared_4956_ == 0 {
                    v___x_4958_ = v___x_4955_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_4959_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4959_, 0, v_a_4953_);
                    v___x_4958_ = v_reuseFailAlloc_4959_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_4958_;
            }
            34 => {
                v___y_4922_ = v_____do__lift_4946_;
                v___y_4923_ = v___y_4945_;
                v_____do__lift_4924_ = v___x_4963_;
                state = 25;
                continue;
            }
            35 => {
                if leanh::lean_obj_tag(v_isInstance_x3f_4811_) == 0 {
                    v___x_4968_ = leanh::lean_box(0);
                    v___y_4945_ = v_____do__lift_4967_;
                    v_____do__lift_4946_ = v___x_4968_;
                    state = 30;
                    continue;
                } else {
                    v_val_4969_ = leanh::lean_ctor_get(v_isInstance_x3f_4811_, 0);
                    v_isSharedCheck_4986_ =
                        (!leanh::lean_is_exclusive(v_isInstance_x3f_4811_)) as u8;
                    if v_isSharedCheck_4986_ == 0 {
                        v___x_4971_ = v_isInstance_x3f_4811_;
                        v_isShared_4972_ = v_isSharedCheck_4986_;
                        state = 36;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4969_);
                        leanh::lean_dec(v_isInstance_x3f_4811_);
                        v___x_4971_ = leanh::lean_box(0);
                        v_isShared_4972_ = v_isSharedCheck_4986_;
                        state = 36;
                        continue;
                    }
                }
            }
            36 => {
                v___x_4973_ = l_Lean_Json_getBool_x3f(v_val_4969_);
                leanh::lean_dec(v_val_4969_);
                if leanh::lean_obj_tag(v___x_4973_) == 0 {
                    leanh::lean_del_object(v___x_4971_);
                    leanh::lean_dec(v_____do__lift_4967_);
                    leanh::lean_del_object(v___x_4883_);
                    leanh::lean_dec(v_a_4881_);
                    leanh::lean_dec(v_a_4860_);
                    leanh::lean_dec(v_a_4839_);
                    leanh::lean_del_object(v___x_4816_);
                    leanh::lean_dec(v_isRemoved_x3f_4814_);
                    leanh::lean_dec(v_isInserted_x3f_4813_);
                    leanh::lean_dec(v_isType_x3f_4812_);
                    v_a_4974_ = leanh::lean_ctor_get(v___x_4973_, 0);
                    v_isSharedCheck_4981_ = (!leanh::lean_is_exclusive(v___x_4973_)) as u8;
                    if v_isSharedCheck_4981_ == 0 {
                        v___x_4976_ = v___x_4973_;
                        v_isShared_4977_ = v_isSharedCheck_4981_;
                        state = 37;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4974_);
                        leanh::lean_dec(v___x_4973_);
                        v___x_4976_ = leanh::lean_box(0);
                        v_isShared_4977_ = v_isSharedCheck_4981_;
                        state = 37;
                        continue;
                    }
                } else {
                    v_a_4982_ = leanh::lean_ctor_get(v___x_4973_, 0);
                    leanh::lean_inc(v_a_4982_);
                    leanh::lean_dec_ref_known(v___x_4973_, 1);
                    if v_isShared_4972_ == 0 {
                        leanh::lean_ctor_set(v___x_4971_, 0, v_a_4982_);
                        v___x_4984_ = v___x_4971_;
                        state = 39;
                        continue;
                    } else {
                        v_reuseFailAlloc_4985_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4985_, 0, v_a_4982_);
                        v___x_4984_ = v_reuseFailAlloc_4985_;
                        state = 39;
                        continue;
                    }
                }
            }
            37 => {
                if v_isShared_4977_ == 0 {
                    v___x_4979_ = v___x_4976_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_4980_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4980_, 0, v_a_4974_);
                    v___x_4979_ = v_reuseFailAlloc_4980_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_4979_;
            }
            39 => {
                v___y_4945_ = v_____do__lift_4967_;
                v_____do__lift_4946_ = v___x_4984_;
                state = 30;
                continue;
            }
            40 => {
                v___x_4992_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(v_val_4988_);
                if leanh::lean_obj_tag(v___x_4992_) == 0 {
                    leanh::lean_del_object(v___x_4990_);
                    leanh::lean_del_object(v___x_4883_);
                    leanh::lean_dec(v_a_4881_);
                    leanh::lean_dec(v_a_4860_);
                    leanh::lean_dec(v_a_4839_);
                    leanh::lean_del_object(v___x_4816_);
                    leanh::lean_dec(v_isRemoved_x3f_4814_);
                    leanh::lean_dec(v_isInserted_x3f_4813_);
                    leanh::lean_dec(v_isType_x3f_4812_);
                    leanh::lean_dec(v_isInstance_x3f_4811_);
                    v_a_4993_ = leanh::lean_ctor_get(v___x_4992_, 0);
                    v_isSharedCheck_5000_ = (!leanh::lean_is_exclusive(v___x_4992_)) as u8;
                    if v_isSharedCheck_5000_ == 0 {
                        v___x_4995_ = v___x_4992_;
                        v_isShared_4996_ = v_isSharedCheck_5000_;
                        state = 41;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4993_);
                        leanh::lean_dec(v___x_4992_);
                        v___x_4995_ = leanh::lean_box(0);
                        v_isShared_4996_ = v_isSharedCheck_5000_;
                        state = 41;
                        continue;
                    }
                } else {
                    v_a_5001_ = leanh::lean_ctor_get(v___x_4992_, 0);
                    leanh::lean_inc(v_a_5001_);
                    leanh::lean_dec_ref_known(v___x_4992_, 1);
                    v___x_5002_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5___redArg(v___x_4871_, v_a_5001_, v_a_4796_);
                    if leanh::lean_obj_tag(v___x_5002_) == 0 {
                        leanh::lean_del_object(v___x_4990_);
                        leanh::lean_del_object(v___x_4883_);
                        leanh::lean_dec(v_a_4881_);
                        leanh::lean_dec(v_a_4860_);
                        leanh::lean_dec(v_a_4839_);
                        leanh::lean_del_object(v___x_4816_);
                        leanh::lean_dec(v_isRemoved_x3f_4814_);
                        leanh::lean_dec(v_isInserted_x3f_4813_);
                        leanh::lean_dec(v_isType_x3f_4812_);
                        leanh::lean_dec(v_isInstance_x3f_4811_);
                        v_a_5003_ = leanh::lean_ctor_get(v___x_5002_, 0);
                        v_isSharedCheck_5010_ =
                            (!leanh::lean_is_exclusive(v___x_5002_)) as u8;
                        if v_isSharedCheck_5010_ == 0 {
                            v___x_5005_ = v___x_5002_;
                            v_isShared_5006_ = v_isSharedCheck_5010_;
                            state = 43;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5003_);
                            leanh::lean_dec(v___x_5002_);
                            v___x_5005_ = leanh::lean_box(0);
                            v_isShared_5006_ = v_isSharedCheck_5010_;
                            state = 43;
                            continue;
                        }
                    } else {
                        v_a_5011_ = leanh::lean_ctor_get(v___x_5002_, 0);
                        leanh::lean_inc(v_a_5011_);
                        leanh::lean_dec_ref_known(v___x_5002_, 1);
                        if v_isShared_4991_ == 0 {
                            leanh::lean_ctor_set(v___x_4990_, 0, v_a_5011_);
                            v___x_5013_ = v___x_4990_;
                            state = 45;
                            continue;
                        } else {
                            v_reuseFailAlloc_5014_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5014_, 0, v_a_5011_);
                            v___x_5013_ = v_reuseFailAlloc_5014_;
                            state = 45;
                            continue;
                        }
                    }
                }
            }
            41 => {
                if v_isShared_4996_ == 0 {
                    v___x_4998_ = v___x_4995_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_4999_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_a_4993_);
                    v___x_4998_ = v_reuseFailAlloc_4999_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_4998_;
            }
            43 => {
                if v_isShared_5006_ == 0 {
                    v___x_5008_ = v___x_5005_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_5009_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5009_, 0, v_a_5003_);
                    v___x_5008_ = v_reuseFailAlloc_5009_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_5008_;
            }
            45 => {
                v_____do__lift_4967_ = v___x_5013_;
                state = 35;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1____boxed(
    mut v_j_5018_: *mut leanh::LeanObject,
    mut v_a_5019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5020_ = l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_(v_j_5018_, v_a_5019_);
    leanh::lean_dec_ref(v_a_5019_);
    return v_res_5020_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2(
    mut v_sz_5021_: usize,
    mut v_i_5022_: usize,
    mut v_bs_5023_: *mut leanh::LeanObject,
    mut v___y_5024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5025_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___redArg(v_sz_5021_, v_i_5022_, v_bs_5023_);
    return v___x_5025_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___boxed(
    mut v_sz_5026_: *mut leanh::LeanObject,
    mut v_i_5027_: *mut leanh::LeanObject,
    mut v_bs_5028_: *mut leanh::LeanObject,
    mut v___y_5029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5030_: usize = 0;
    let mut v_i_boxed_5031_: usize = 0;
    let mut v_res_5032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5030_ = leanh::lean_unbox_usize(v_sz_5026_);
    leanh::lean_dec(v_sz_5026_);
    v_i_boxed_5031_ = leanh::lean_unbox_usize(v_i_5027_);
    leanh::lean_dec(v_i_5027_);
    v_res_5032_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2(v_sz_boxed_5030_, v_i_boxed_5031_, v_bs_5028_, v___y_5029_);
    leanh::lean_dec_ref(v___y_5029_);
    return v_res_5032_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3(
    mut v_sz_5033_: usize,
    mut v_i_5034_: usize,
    mut v_bs_5035_: *mut leanh::LeanObject,
    mut v___y_5036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3___redArg(v_sz_5033_, v_i_5034_, v_bs_5035_);
    return v___x_5037_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3___boxed(
    mut v_sz_5038_: *mut leanh::LeanObject,
    mut v_i_5039_: *mut leanh::LeanObject,
    mut v_bs_5040_: *mut leanh::LeanObject,
    mut v___y_5041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5042_: usize = 0;
    let mut v_i_boxed_5043_: usize = 0;
    let mut v_res_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5042_ = leanh::lean_unbox_usize(v_sz_5038_);
    leanh::lean_dec(v_sz_5038_);
    v_i_boxed_5043_ = leanh::lean_unbox_usize(v_i_5039_);
    leanh::lean_dec(v_i_5039_);
    v_res_5044_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3(v_sz_boxed_5042_, v_i_boxed_5043_, v_bs_5040_, v___y_5041_);
    leanh::lean_dec_ref(v___y_5041_);
    return v_res_5044_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5(
    mut v_00_u03b1_5045_: *mut leanh::LeanObject,
    mut v_00_u03b2_5046_: *mut leanh::LeanObject,
    mut v_f_5047_: *mut leanh::LeanObject,
    mut v_x_5048_: *mut leanh::LeanObject,
    mut v___y_5049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5050_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5___redArg(v_f_5047_, v_x_5048_, v___y_5049_);
    return v___x_5050_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5___boxed(
    mut v_00_u03b1_5051_: *mut leanh::LeanObject,
    mut v_00_u03b2_5052_: *mut leanh::LeanObject,
    mut v_f_5053_: *mut leanh::LeanObject,
    mut v_x_5054_: *mut leanh::LeanObject,
    mut v___y_5055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5056_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5(v_00_u03b1_5051_, v_00_u03b2_5052_, v_f_5053_, v_x_5054_, v___y_5055_);
    leanh::lean_dec_ref(v___y_5055_);
    return v_res_5056_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5_spec__7(
    mut v_00_u03b1_5057_: *mut leanh::LeanObject,
    mut v_00_u03b2_5058_: *mut leanh::LeanObject,
    mut v_f_5059_: *mut leanh::LeanObject,
    mut v_sz_5060_: usize,
    mut v_i_5061_: usize,
    mut v_bs_5062_: *mut leanh::LeanObject,
    mut v___y_5063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5064_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5_spec__7___redArg(v_f_5059_, v_sz_5060_, v_i_5061_, v_bs_5062_, v___y_5063_);
    return v___x_5064_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5_spec__7___boxed(
    mut v_00_u03b1_5065_: *mut leanh::LeanObject,
    mut v_00_u03b2_5066_: *mut leanh::LeanObject,
    mut v_f_5067_: *mut leanh::LeanObject,
    mut v_sz_5068_: *mut leanh::LeanObject,
    mut v_i_5069_: *mut leanh::LeanObject,
    mut v_bs_5070_: *mut leanh::LeanObject,
    mut v___y_5071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5072_: usize = 0;
    let mut v_i_boxed_5073_: usize = 0;
    let mut v_res_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5072_ = leanh::lean_unbox_usize(v_sz_5068_);
    leanh::lean_dec(v_sz_5068_);
    v_i_boxed_5073_ = leanh::lean_unbox_usize(v_i_5069_);
    leanh::lean_dec(v_i_5069_);
    v_res_5074_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5_spec__7(v_00_u03b1_5065_, v_00_u03b2_5066_, v_f_5067_, v_sz_boxed_5072_, v_i_boxed_5073_, v_bs_5070_, v___y_5071_);
    leanh::lean_dec_ref(v___y_5071_);
    return v_res_5074_;
}
pub unsafe fn l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_(
    mut v_json_5086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5113_: u8 = 0;
    let mut v___x_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5118_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5087_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
                leanh::lean_inc_n(v_json_5086_, 7);
                v___x_5088_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_5086_, v___x_5087_);
                v_a_5089_ = leanh::lean_ctor_get(v___x_5088_, 0);
                leanh::lean_inc(v_a_5089_);
                leanh::lean_dec_ref(v___x_5088_);
                v___x_5090_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
                v___x_5091_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_5086_, v___x_5090_);
                v_a_5092_ = leanh::lean_ctor_get(v___x_5091_, 0);
                leanh::lean_inc(v_a_5092_);
                leanh::lean_dec_ref(v___x_5091_);
                v___x_5093_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
                v___x_5094_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_5086_, v___x_5093_);
                v_a_5095_ = leanh::lean_ctor_get(v___x_5094_, 0);
                leanh::lean_inc(v_a_5095_);
                leanh::lean_dec_ref(v___x_5094_);
                v___x_5096_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
                v___x_5097_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1(v_json_5086_, v___x_5096_);
                v_a_5098_ = leanh::lean_ctor_get(v___x_5097_, 0);
                leanh::lean_inc(v_a_5098_);
                leanh::lean_dec_ref(v___x_5097_);
                v___x_5099_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
                v___x_5100_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_5086_, v___x_5099_);
                v_a_5101_ = leanh::lean_ctor_get(v___x_5100_, 0);
                leanh::lean_inc(v_a_5101_);
                leanh::lean_dec_ref(v___x_5100_);
                v___x_5102_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
                v___x_5103_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_5086_, v___x_5102_);
                v_a_5104_ = leanh::lean_ctor_get(v___x_5103_, 0);
                leanh::lean_inc(v_a_5104_);
                leanh::lean_dec_ref(v___x_5103_);
                v___x_5105_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
                v___x_5106_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1(v_json_5086_, v___x_5105_);
                v_a_5107_ = leanh::lean_ctor_get(v___x_5106_, 0);
                leanh::lean_inc(v_a_5107_);
                leanh::lean_dec_ref(v___x_5106_);
                v___x_5108_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
                v___x_5109_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1(v_json_5086_, v___x_5108_);
                v_a_5110_ = leanh::lean_ctor_get(v___x_5109_, 0);
                v_isSharedCheck_5118_ = (!leanh::lean_is_exclusive(v___x_5109_)) as u8;
                if v_isSharedCheck_5118_ == 0 {
                    v___x_5112_ = v___x_5109_;
                    v_isShared_5113_ = v_isSharedCheck_5118_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5110_);
                    leanh::lean_dec(v___x_5109_);
                    v___x_5112_ = leanh::lean_box(0);
                    v_isShared_5113_ = v_isSharedCheck_5118_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5114_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                leanh::lean_ctor_set(v___x_5114_, 0, v_a_5089_);
                leanh::lean_ctor_set(v___x_5114_, 1, v_a_5092_);
                leanh::lean_ctor_set(v___x_5114_, 2, v_a_5095_);
                leanh::lean_ctor_set(v___x_5114_, 3, v_a_5098_);
                leanh::lean_ctor_set(v___x_5114_, 4, v_a_5101_);
                leanh::lean_ctor_set(v___x_5114_, 5, v_a_5104_);
                leanh::lean_ctor_set(v___x_5114_, 6, v_a_5107_);
                leanh::lean_ctor_set(v___x_5114_, 7, v_a_5110_);
                if v_isShared_5113_ == 0 {
                    leanh::lean_ctor_set(v___x_5112_, 0, v___x_5114_);
                    v___x_5116_ = v___x_5112_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5117_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5117_, 0, v___x_5114_);
                    v___x_5116_ = v_reuseFailAlloc_5117_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5116_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_45_(
    mut v_x_5121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hyps_5122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_5124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_x3f_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_goalPrefix_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInserted_x3f_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRemoved_x3f_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_hyps_5122_ = leanh::lean_ctor_get(v_x_5121_, 0);
    v_type_5123_ = leanh::lean_ctor_get(v_x_5121_, 1);
    v_ctx_5124_ = leanh::lean_ctor_get(v_x_5121_, 2);
    v_userName_x3f_5125_ = leanh::lean_ctor_get(v_x_5121_, 3);
    v_goalPrefix_5126_ = leanh::lean_ctor_get(v_x_5121_, 4);
    v_mvarId_5127_ = leanh::lean_ctor_get(v_x_5121_, 5);
    v_isInserted_x3f_5128_ = leanh::lean_ctor_get(v_x_5121_, 6);
    v_isRemoved_x3f_5129_ = leanh::lean_ctor_get(v_x_5121_, 7);
    v___x_5130_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
    leanh::lean_inc(v_hyps_5122_);
    v___x_5131_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5131_, 0, v___x_5130_);
    leanh::lean_ctor_set(v___x_5131_, 1, v_hyps_5122_);
    v___x_5132_ = leanh::lean_box(0);
    v___x_5133_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5133_, 0, v___x_5131_);
    leanh::lean_ctor_set(v___x_5133_, 1, v___x_5132_);
    v___x_5134_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
    leanh::lean_inc(v_type_5123_);
    v___x_5135_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5135_, 0, v___x_5134_);
    leanh::lean_ctor_set(v___x_5135_, 1, v_type_5123_);
    v___x_5136_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5136_, 0, v___x_5135_);
    leanh::lean_ctor_set(v___x_5136_, 1, v___x_5132_);
    v___x_5137_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
    leanh::lean_inc(v_ctx_5124_);
    v___x_5138_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5138_, 0, v___x_5137_);
    leanh::lean_ctor_set(v___x_5138_, 1, v_ctx_5124_);
    v___x_5139_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5139_, 0, v___x_5138_);
    leanh::lean_ctor_set(v___x_5139_, 1, v___x_5132_);
    v___x_5140_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
    v___x_5141_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__0(v___x_5140_, v_userName_x3f_5125_);
    v___x_5142_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
    leanh::lean_inc(v_goalPrefix_5126_);
    v___x_5143_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5143_, 0, v___x_5142_);
    leanh::lean_ctor_set(v___x_5143_, 1, v_goalPrefix_5126_);
    v___x_5144_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5144_, 0, v___x_5143_);
    leanh::lean_ctor_set(v___x_5144_, 1, v___x_5132_);
    v___x_5145_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
    leanh::lean_inc(v_mvarId_5127_);
    v___x_5146_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5146_, 0, v___x_5145_);
    leanh::lean_ctor_set(v___x_5146_, 1, v_mvarId_5127_);
    v___x_5147_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5147_, 0, v___x_5146_);
    leanh::lean_ctor_set(v___x_5147_, 1, v___x_5132_);
    v___x_5148_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
    v___x_5149_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__0(v___x_5148_, v_isInserted_x3f_5128_);
    v___x_5150_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
    v___x_5151_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__0(v___x_5150_, v_isRemoved_x3f_5129_);
    v___x_5152_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5152_, 0, v___x_5151_);
    leanh::lean_ctor_set(v___x_5152_, 1, v___x_5132_);
    v___x_5153_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5153_, 0, v___x_5149_);
    leanh::lean_ctor_set(v___x_5153_, 1, v___x_5152_);
    v___x_5154_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5154_, 0, v___x_5147_);
    leanh::lean_ctor_set(v___x_5154_, 1, v___x_5153_);
    v___x_5155_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5155_, 0, v___x_5144_);
    leanh::lean_ctor_set(v___x_5155_, 1, v___x_5154_);
    v___x_5156_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5156_, 0, v___x_5141_);
    leanh::lean_ctor_set(v___x_5156_, 1, v___x_5155_);
    v___x_5157_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5157_, 0, v___x_5139_);
    leanh::lean_ctor_set(v___x_5157_, 1, v___x_5156_);
    v___x_5158_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5158_, 0, v___x_5136_);
    leanh::lean_ctor_set(v___x_5158_, 1, v___x_5157_);
    v___x_5159_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5159_, 0, v___x_5133_);
    leanh::lean_ctor_set(v___x_5159_, 1, v___x_5158_);
    v___x_5160_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47_;
    v___x_5161_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__1(v___x_5159_, v___x_5160_);
    v___x_5162_ = l_Lean_Json_mkObj(v___x_5161_);
    leanh::lean_dec(v___x_5161_);
    return v___x_5162_;
}
pub unsafe fn l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_45____boxed(
    mut v_x_5163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5164_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_45_(v_x_5163_);
    leanh::lean_dec_ref(v_x_5163_);
    return v_res_5164_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoal_enc_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1__spec__0(
    mut v_sz_5167_: usize,
    mut v_i_5168_: usize,
    mut v_bs_5169_: *mut leanh::LeanObject,
    mut v___y_5170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5171_: u8 = 0;
    let mut v___x_5172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: usize = 0;
    let mut v___x_5180_: usize = 0;
    let mut v___x_5181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5171_ = lean_usize_dec_lt(v_i_5168_, v_sz_5167_);
                if v___x_5171_ == 0 {
                    v___x_5172_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5172_, 0, v_bs_5169_);
                    leanh::lean_ctor_set(v___x_5172_, 1, v___y_5170_);
                    return v___x_5172_;
                } else {
                    v_v_5173_ = lean_array_uget_borrowed(v_bs_5169_, v_i_5168_);
                    leanh::lean_inc(v_v_5173_);
                    v___x_5174_ = l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_(v_v_5173_, v___y_5170_);
                    v_fst_5175_ = leanh::lean_ctor_get(v___x_5174_, 0);
                    leanh::lean_inc(v_fst_5175_);
                    v_snd_5176_ = leanh::lean_ctor_get(v___x_5174_, 1);
                    leanh::lean_inc(v_snd_5176_);
                    leanh::lean_dec_ref(v___x_5174_);
                    v___x_5177_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5178_ = lean_array_uset(v_bs_5169_, v_i_5168_, v___x_5177_);
                    v___x_5179_ = 1usize;
                    v___x_5180_ = lean_usize_add(v_i_5168_, v___x_5179_);
                    v___x_5181_ = lean_array_uset(v_bs_x27_5178_, v_i_5168_, v_fst_5175_);
                    v_i_5168_ = v___x_5180_;
                    v_bs_5169_ = v___x_5181_;
                    v___y_5170_ = v_snd_5176_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoal_enc_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1__spec__0___boxed(
    mut v_sz_5183_: *mut leanh::LeanObject,
    mut v_i_5184_: *mut leanh::LeanObject,
    mut v_bs_5185_: *mut leanh::LeanObject,
    mut v___y_5186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5187_: usize = 0;
    let mut v_i_boxed_5188_: usize = 0;
    let mut v_res_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5187_ = leanh::lean_unbox_usize(v_sz_5183_);
    leanh::lean_dec(v_sz_5183_);
    v_i_boxed_5188_ = leanh::lean_unbox_usize(v_i_5184_);
    leanh::lean_dec(v_i_5184_);
    v_res_5189_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoal_enc_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1__spec__0(v_sz_boxed_5187_, v_i_boxed_5188_, v_bs_5185_, v___y_5186_);
    return v_res_5189_;
}
pub unsafe fn l_Lean_Widget_instRpcEncodableInteractiveGoal_enc_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1_(
    mut v_a_5190_: *mut leanh::LeanObject,
    mut v_a_5191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toInteractiveGoalCore_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_x3f_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_goalPrefix_5194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInserted_x3f_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRemoved_x3f_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5201_: usize = 0;
    let mut v___x_5202_: usize = 0;
    let mut v___x_5203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5216_: u8 = 0;
    let mut v___x_5217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5241_: u8 = 0;
    let mut v___x_5242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: u8 = 0;
    let mut v___x_5245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5247_: u8 = 0;
    let mut v_fst_5249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: u8 = 0;
    let mut v___x_5252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5258_: u8 = 0;
    let mut v___x_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: u8 = 0;
    let mut v___x_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5264_: u8 = 0;
    let mut v___x_5265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5269_: u8 = 0;
    let mut v___x_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5274_: u8 = 0;
    let mut v_isSharedCheck_5275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInteractiveGoalCore_5192_ = leanh::lean_ctor_get(v_a_5190_, 0);
                leanh::lean_inc_ref(v_toInteractiveGoalCore_5192_);
                v_userName_x3f_5193_ = leanh::lean_ctor_get(v_a_5190_, 1);
                leanh::lean_inc(v_userName_x3f_5193_);
                v_goalPrefix_5194_ = leanh::lean_ctor_get(v_a_5190_, 2);
                leanh::lean_inc_ref(v_goalPrefix_5194_);
                v_mvarId_5195_ = leanh::lean_ctor_get(v_a_5190_, 3);
                leanh::lean_inc(v_mvarId_5195_);
                v_isInserted_x3f_5196_ = leanh::lean_ctor_get(v_a_5190_, 4);
                leanh::lean_inc(v_isInserted_x3f_5196_);
                v_isRemoved_x3f_5197_ = leanh::lean_ctor_get(v_a_5190_, 5);
                leanh::lean_inc(v_isRemoved_x3f_5197_);
                leanh::lean_dec_ref(v_a_5190_);
                v_hyps_5198_ = leanh::lean_ctor_get(v_toInteractiveGoalCore_5192_, 0);
                leanh::lean_inc_ref(v_hyps_5198_);
                v_type_5199_ = leanh::lean_ctor_get(v_toInteractiveGoalCore_5192_, 1);
                leanh::lean_inc_ref(v_type_5199_);
                v_ctx_5200_ = leanh::lean_ctor_get(v_toInteractiveGoalCore_5192_, 2);
                leanh::lean_inc_ref(v_ctx_5200_);
                leanh::lean_dec_ref(v_toInteractiveGoalCore_5192_);
                v_sz_5201_ = lean_array_size(v_hyps_5198_);
                v___x_5202_ = 0usize;
                v___x_5203_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoal_enc_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1__spec__0(v_sz_5201_, v___x_5202_, v_hyps_5198_, v_a_5191_);
                v_fst_5204_ = leanh::lean_ctor_get(v___x_5203_, 0);
                leanh::lean_inc(v_fst_5204_);
                v_snd_5205_ = leanh::lean_ctor_get(v___x_5203_, 1);
                leanh::lean_inc(v_snd_5205_);
                leanh::lean_dec_ref(v___x_5203_);
                v___x_5206_ = l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc___closed__0_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_;
                v___x_5207_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___redArg(v___x_5206_, v_type_5199_, v_snd_5205_);
                v_fst_5208_ = leanh::lean_ctor_get(v___x_5207_, 0);
                leanh::lean_inc(v_fst_5208_);
                v_snd_5209_ = leanh::lean_ctor_get(v___x_5207_, 1);
                leanh::lean_inc(v_snd_5209_);
                leanh::lean_dec_ref(v___x_5207_);
                v___x_5210_ =
                    l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_2318528980____hygCtx___hyg_3_;
                v___x_5211_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(
                    v___x_5210_,
                    v_ctx_5200_,
                    v_snd_5209_,
                );
                leanh::lean_dec_ref(v_ctx_5200_);
                v_fst_5212_ = leanh::lean_ctor_get(v___x_5211_, 0);
                v_snd_5213_ = leanh::lean_ctor_get(v___x_5211_, 1);
                v_isSharedCheck_5275_ = (!leanh::lean_is_exclusive(v___x_5211_)) as u8;
                if v_isSharedCheck_5275_ == 0 {
                    v___x_5215_ = v___x_5211_;
                    v_isShared_5216_ = v_isSharedCheck_5275_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_5213_);
                    leanh::lean_inc(v_fst_5212_);
                    leanh::lean_dec(v___x_5211_);
                    v___x_5215_ = leanh::lean_box(0);
                    v_isShared_5216_ = v_isSharedCheck_5275_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5217_ = l_Array_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3(v_fst_5204_);
                v___x_5218_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(v_fst_5208_);
                if leanh::lean_obj_tag(v_userName_x3f_5193_) == 0 {
                    v___x_5265_ = leanh::lean_box(0);
                    v_fst_5249_ = v___x_5265_;
                    state = 7;
                    continue;
                } else {
                    v_val_5266_ = leanh::lean_ctor_get(v_userName_x3f_5193_, 0);
                    v_isSharedCheck_5274_ =
                        (!leanh::lean_is_exclusive(v_userName_x3f_5193_)) as u8;
                    if v_isSharedCheck_5274_ == 0 {
                        v___x_5268_ = v_userName_x3f_5193_;
                        v_isShared_5269_ = v_isSharedCheck_5274_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5266_);
                        leanh::lean_dec(v_userName_x3f_5193_);
                        v___x_5268_ = leanh::lean_box(0);
                        v_isShared_5269_ = v_isSharedCheck_5274_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5226_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                leanh::lean_ctor_set(v___x_5226_, 0, v___x_5217_);
                leanh::lean_ctor_set(v___x_5226_, 1, v___x_5218_);
                leanh::lean_ctor_set(v___x_5226_, 2, v_fst_5212_);
                leanh::lean_ctor_set(v___x_5226_, 3, v___y_5223_);
                leanh::lean_ctor_set(v___x_5226_, 4, v___y_5220_);
                leanh::lean_ctor_set(v___x_5226_, 5, v___y_5222_);
                leanh::lean_ctor_set(v___x_5226_, 6, v___y_5221_);
                leanh::lean_ctor_set(v___x_5226_, 7, v_fst_5224_);
                v___x_5227_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_45_(v___x_5226_);
                leanh::lean_dec_ref_known(v___x_5226_, 8);
                if v_isShared_5216_ == 0 {
                    leanh::lean_ctor_set(v___x_5215_, 1, v_snd_5225_);
                    leanh::lean_ctor_set(v___x_5215_, 0, v___x_5227_);
                    v___x_5229_ = v___x_5215_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5230_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5230_, 0, v___x_5227_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5230_, 1, v_snd_5225_);
                    v___x_5229_ = v_reuseFailAlloc_5230_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5229_;
            }
            4 => {
                if leanh::lean_obj_tag(v_isRemoved_x3f_5197_) == 0 {
                    v___x_5237_ = leanh::lean_box(0);
                    v___y_5220_ = v___y_5232_;
                    v___y_5221_ = v_fst_5235_;
                    v___y_5222_ = v___y_5233_;
                    v___y_5223_ = v___y_5234_;
                    v_fst_5224_ = v___x_5237_;
                    v_snd_5225_ = v_snd_5236_;
                    state = 2;
                    continue;
                } else {
                    v_val_5238_ = leanh::lean_ctor_get(v_isRemoved_x3f_5197_, 0);
                    v_isSharedCheck_5247_ =
                        (!leanh::lean_is_exclusive(v_isRemoved_x3f_5197_)) as u8;
                    if v_isSharedCheck_5247_ == 0 {
                        v___x_5240_ = v_isRemoved_x3f_5197_;
                        v_isShared_5241_ = v_isSharedCheck_5247_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5238_);
                        leanh::lean_dec(v_isRemoved_x3f_5197_);
                        v___x_5240_ = leanh::lean_box(0);
                        v_isShared_5241_ = v_isSharedCheck_5247_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___x_5242_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_5243_ = (leanh::lean_unbox(v_val_5238_) as u8);
                leanh::lean_dec(v_val_5238_);
                leanh::lean_ctor_set_uint8(v___x_5242_, 0 as u32, v___x_5243_);
                if v_isShared_5241_ == 0 {
                    leanh::lean_ctor_set(v___x_5240_, 0, v___x_5242_);
                    v___x_5245_ = v___x_5240_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5246_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 0, v___x_5242_);
                    v___x_5245_ = v_reuseFailAlloc_5246_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___y_5220_ = v___y_5232_;
                v___y_5221_ = v_fst_5235_;
                v___y_5222_ = v___y_5233_;
                v___y_5223_ = v___y_5234_;
                v_fst_5224_ = v___x_5245_;
                v_snd_5225_ = v_snd_5236_;
                state = 2;
                continue;
            }
            7 => {
                v___x_5250_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5250_, 0, v_goalPrefix_5194_);
                v___x_5251_ = 1;
                v___x_5252_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_mvarId_5195_,
                    v___x_5251_,
                );
                v___x_5253_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5253_, 0, v___x_5252_);
                if leanh::lean_obj_tag(v_isInserted_x3f_5196_) == 0 {
                    v___x_5254_ = leanh::lean_box(0);
                    v___y_5232_ = v___x_5250_;
                    v___y_5233_ = v___x_5253_;
                    v___y_5234_ = v_fst_5249_;
                    v_fst_5235_ = v___x_5254_;
                    v_snd_5236_ = v_snd_5213_;
                    state = 4;
                    continue;
                } else {
                    v_val_5255_ = leanh::lean_ctor_get(v_isInserted_x3f_5196_, 0);
                    v_isSharedCheck_5264_ =
                        (!leanh::lean_is_exclusive(v_isInserted_x3f_5196_)) as u8;
                    if v_isSharedCheck_5264_ == 0 {
                        v___x_5257_ = v_isInserted_x3f_5196_;
                        v_isShared_5258_ = v_isSharedCheck_5264_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5255_);
                        leanh::lean_dec(v_isInserted_x3f_5196_);
                        v___x_5257_ = leanh::lean_box(0);
                        v_isShared_5258_ = v_isSharedCheck_5264_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                v___x_5259_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_5260_ = (leanh::lean_unbox(v_val_5255_) as u8);
                leanh::lean_dec(v_val_5255_);
                leanh::lean_ctor_set_uint8(v___x_5259_, 0 as u32, v___x_5260_);
                if v_isShared_5258_ == 0 {
                    leanh::lean_ctor_set(v___x_5257_, 0, v___x_5259_);
                    v___x_5262_ = v___x_5257_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5263_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5263_, 0, v___x_5259_);
                    v___x_5262_ = v_reuseFailAlloc_5263_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___y_5232_ = v___x_5250_;
                v___y_5233_ = v___x_5253_;
                v___y_5234_ = v_fst_5249_;
                v_fst_5235_ = v___x_5262_;
                v_snd_5236_ = v_snd_5213_;
                state = 4;
                continue;
            }
            10 => {
                v___x_5270_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5270_, 0, v_val_5266_);
                if v_isShared_5269_ == 0 {
                    leanh::lean_ctor_set(v___x_5268_, 0, v___x_5270_);
                    v___x_5272_ = v___x_5268_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5273_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5273_, 0, v___x_5270_);
                    v___x_5272_ = v_reuseFailAlloc_5273_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_fst_5249_ = v___x_5272_;
                state = 7;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoal_dec_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1__spec__0(
    mut v_sz_5276_: usize,
    mut v_i_5277_: usize,
    mut v_bs_5278_: *mut leanh::LeanObject,
    mut v___y_5279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5280_: u8 = 0;
    let mut v___x_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5287_: u8 = 0;
    let mut v___x_5289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5291_: u8 = 0;
    let mut v_a_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: usize = 0;
    let mut v___x_5296_: usize = 0;
    let mut v___x_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5280_ = lean_usize_dec_lt(v_i_5277_, v_sz_5276_);
                if v___x_5280_ == 0 {
                    v___x_5281_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5281_, 0, v_bs_5278_);
                    return v___x_5281_;
                } else {
                    v_v_5282_ = lean_array_uget_borrowed(v_bs_5278_, v_i_5277_);
                    leanh::lean_inc(v_v_5282_);
                    v___x_5283_ = l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_(v_v_5282_, v___y_5279_);
                    if leanh::lean_obj_tag(v___x_5283_) == 0 {
                        leanh::lean_dec_ref(v_bs_5278_);
                        v_a_5284_ = leanh::lean_ctor_get(v___x_5283_, 0);
                        v_isSharedCheck_5291_ =
                            (!leanh::lean_is_exclusive(v___x_5283_)) as u8;
                        if v_isSharedCheck_5291_ == 0 {
                            v___x_5286_ = v___x_5283_;
                            v_isShared_5287_ = v_isSharedCheck_5291_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5284_);
                            leanh::lean_dec(v___x_5283_);
                            v___x_5286_ = leanh::lean_box(0);
                            v_isShared_5287_ = v_isSharedCheck_5291_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5292_ = leanh::lean_ctor_get(v___x_5283_, 0);
                        leanh::lean_inc(v_a_5292_);
                        leanh::lean_dec_ref_known(v___x_5283_, 1);
                        v___x_5293_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_5294_ = lean_array_uset(v_bs_5278_, v_i_5277_, v___x_5293_);
                        v___x_5295_ = 1usize;
                        v___x_5296_ = lean_usize_add(v_i_5277_, v___x_5295_);
                        v___x_5297_ = lean_array_uset(v_bs_x27_5294_, v_i_5277_, v_a_5292_);
                        v_i_5277_ = v___x_5296_;
                        v_bs_5278_ = v___x_5297_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5287_ == 0 {
                    v___x_5289_ = v___x_5286_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5290_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5290_, 0, v_a_5284_);
                    v___x_5289_ = v_reuseFailAlloc_5290_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5289_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoal_dec_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1__spec__0___boxed(
    mut v_sz_5299_: *mut leanh::LeanObject,
    mut v_i_5300_: *mut leanh::LeanObject,
    mut v_bs_5301_: *mut leanh::LeanObject,
    mut v___y_5302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5303_: usize = 0;
    let mut v_i_boxed_5304_: usize = 0;
    let mut v_res_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5303_ = leanh::lean_unbox_usize(v_sz_5299_);
    leanh::lean_dec(v_sz_5299_);
    v_i_boxed_5304_ = leanh::lean_unbox_usize(v_i_5300_);
    leanh::lean_dec(v_i_5300_);
    v_res_5305_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoal_dec_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1__spec__0(v_sz_boxed_5303_, v_i_boxed_5304_, v_bs_5301_, v___y_5302_);
    leanh::lean_dec_ref(v___y_5302_);
    return v_res_5305_;
}
pub unsafe fn l_Lean_Widget_instRpcEncodableInteractiveGoal_dec_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1_(
    mut v_j_5306_: *mut leanh::LeanObject,
    mut v_a_5307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5312_: u8 = 0;
    let mut v___x_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5316_: u8 = 0;
    let mut v_a_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_5320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_x3f_5321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_goalPrefix_5322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInserted_x3f_5324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRemoved_x3f_5325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5330_: u8 = 0;
    let mut v___x_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5334_: u8 = 0;
    let mut v_a_5335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5336_: usize = 0;
    let mut v___x_5337_: usize = 0;
    let mut v___x_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5342_: u8 = 0;
    let mut v___x_5344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5346_: u8 = 0;
    let mut v_a_5347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5352_: u8 = 0;
    let mut v___x_5354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5356_: u8 = 0;
    let mut v_a_5357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5363_: u8 = 0;
    let mut v___x_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5367_: u8 = 0;
    let mut v_a_5368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5374_: u8 = 0;
    let mut v___x_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5378_: u8 = 0;
    let mut v_a_5379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5382_: u8 = 0;
    let mut v___y_5384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_____do__lift_5388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_____do__lift_5398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5403_: u8 = 0;
    let mut v___x_5404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5408_: u8 = 0;
    let mut v___x_5410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5412_: u8 = 0;
    let mut v_a_5413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5417_: u8 = 0;
    let mut v_____do__lift_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5424_: u8 = 0;
    let mut v___x_5426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5428_: u8 = 0;
    let mut v_a_5429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5434_: u8 = 0;
    let mut v___x_5436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5438_: u8 = 0;
    let mut v_a_5439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5445_: u8 = 0;
    let mut v___x_5446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5450_: u8 = 0;
    let mut v___x_5452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5454_: u8 = 0;
    let mut v_a_5455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5459_: u8 = 0;
    let mut v___x_5460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5464_: u8 = 0;
    let mut v___x_5465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5469_: u8 = 0;
    let mut v___x_5471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5473_: u8 = 0;
    let mut v_a_5474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5478_: u8 = 0;
    let mut v_isSharedCheck_5479_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5308_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_(v_j_5306_);
                if leanh::lean_obj_tag(v___x_5308_) == 0 {
                    v_a_5309_ = leanh::lean_ctor_get(v___x_5308_, 0);
                    v_isSharedCheck_5316_ = (!leanh::lean_is_exclusive(v___x_5308_)) as u8;
                    if v_isSharedCheck_5316_ == 0 {
                        v___x_5311_ = v___x_5308_;
                        v_isShared_5312_ = v_isSharedCheck_5316_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5309_);
                        leanh::lean_dec(v___x_5308_);
                        v___x_5311_ = leanh::lean_box(0);
                        v_isShared_5312_ = v_isSharedCheck_5316_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5317_ = leanh::lean_ctor_get(v___x_5308_, 0);
                    leanh::lean_inc(v_a_5317_);
                    leanh::lean_dec_ref_known(v___x_5308_, 1);
                    v_hyps_5318_ = leanh::lean_ctor_get(v_a_5317_, 0);
                    leanh::lean_inc(v_hyps_5318_);
                    v_type_5319_ = leanh::lean_ctor_get(v_a_5317_, 1);
                    leanh::lean_inc(v_type_5319_);
                    v_ctx_5320_ = leanh::lean_ctor_get(v_a_5317_, 2);
                    leanh::lean_inc(v_ctx_5320_);
                    v_userName_x3f_5321_ = leanh::lean_ctor_get(v_a_5317_, 3);
                    leanh::lean_inc(v_userName_x3f_5321_);
                    v_goalPrefix_5322_ = leanh::lean_ctor_get(v_a_5317_, 4);
                    leanh::lean_inc(v_goalPrefix_5322_);
                    v_mvarId_5323_ = leanh::lean_ctor_get(v_a_5317_, 5);
                    leanh::lean_inc(v_mvarId_5323_);
                    v_isInserted_x3f_5324_ = leanh::lean_ctor_get(v_a_5317_, 6);
                    leanh::lean_inc(v_isInserted_x3f_5324_);
                    v_isRemoved_x3f_5325_ = leanh::lean_ctor_get(v_a_5317_, 7);
                    leanh::lean_inc(v_isRemoved_x3f_5325_);
                    leanh::lean_dec(v_a_5317_);
                    v___x_5326_ = l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0(v_hyps_5318_);
                    if leanh::lean_obj_tag(v___x_5326_) == 0 {
                        leanh::lean_dec(v_isRemoved_x3f_5325_);
                        leanh::lean_dec(v_isInserted_x3f_5324_);
                        leanh::lean_dec(v_mvarId_5323_);
                        leanh::lean_dec(v_goalPrefix_5322_);
                        leanh::lean_dec(v_userName_x3f_5321_);
                        leanh::lean_dec(v_ctx_5320_);
                        leanh::lean_dec(v_type_5319_);
                        v_a_5327_ = leanh::lean_ctor_get(v___x_5326_, 0);
                        v_isSharedCheck_5334_ =
                            (!leanh::lean_is_exclusive(v___x_5326_)) as u8;
                        if v_isSharedCheck_5334_ == 0 {
                            v___x_5329_ = v___x_5326_;
                            v_isShared_5330_ = v_isSharedCheck_5334_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5327_);
                            leanh::lean_dec(v___x_5326_);
                            v___x_5329_ = leanh::lean_box(0);
                            v_isShared_5330_ = v_isSharedCheck_5334_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5335_ = leanh::lean_ctor_get(v___x_5326_, 0);
                        leanh::lean_inc(v_a_5335_);
                        leanh::lean_dec_ref_known(v___x_5326_, 1);
                        v_sz_5336_ = lean_array_size(v_a_5335_);
                        v___x_5337_ = 0usize;
                        v___x_5338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoal_dec_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1__spec__0(v_sz_5336_, v___x_5337_, v_a_5335_, v_a_5307_);
                        if leanh::lean_obj_tag(v___x_5338_) == 0 {
                            leanh::lean_dec(v_isRemoved_x3f_5325_);
                            leanh::lean_dec(v_isInserted_x3f_5324_);
                            leanh::lean_dec(v_mvarId_5323_);
                            leanh::lean_dec(v_goalPrefix_5322_);
                            leanh::lean_dec(v_userName_x3f_5321_);
                            leanh::lean_dec(v_ctx_5320_);
                            leanh::lean_dec(v_type_5319_);
                            v_a_5339_ = leanh::lean_ctor_get(v___x_5338_, 0);
                            v_isSharedCheck_5346_ =
                                (!leanh::lean_is_exclusive(v___x_5338_)) as u8;
                            if v_isSharedCheck_5346_ == 0 {
                                v___x_5341_ = v___x_5338_;
                                v_isShared_5342_ = v_isSharedCheck_5346_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5339_);
                                leanh::lean_dec(v___x_5338_);
                                v___x_5341_ = leanh::lean_box(0);
                                v_isShared_5342_ = v_isSharedCheck_5346_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v_a_5347_ = leanh::lean_ctor_get(v___x_5338_, 0);
                            leanh::lean_inc(v_a_5347_);
                            leanh::lean_dec_ref_known(v___x_5338_, 1);
                            v___x_5348_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(v_type_5319_);
                            if leanh::lean_obj_tag(v___x_5348_) == 0 {
                                leanh::lean_dec(v_a_5347_);
                                leanh::lean_dec(v_isRemoved_x3f_5325_);
                                leanh::lean_dec(v_isInserted_x3f_5324_);
                                leanh::lean_dec(v_mvarId_5323_);
                                leanh::lean_dec(v_goalPrefix_5322_);
                                leanh::lean_dec(v_userName_x3f_5321_);
                                leanh::lean_dec(v_ctx_5320_);
                                v_a_5349_ = leanh::lean_ctor_get(v___x_5348_, 0);
                                v_isSharedCheck_5356_ =
                                    (!leanh::lean_is_exclusive(v___x_5348_)) as u8;
                                if v_isSharedCheck_5356_ == 0 {
                                    v___x_5351_ = v___x_5348_;
                                    v_isShared_5352_ = v_isSharedCheck_5356_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5349_);
                                    leanh::lean_dec(v___x_5348_);
                                    v___x_5351_ = leanh::lean_box(0);
                                    v_isShared_5352_ = v_isSharedCheck_5356_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_5357_ = leanh::lean_ctor_get(v___x_5348_, 0);
                                leanh::lean_inc(v_a_5357_);
                                leanh::lean_dec_ref_known(v___x_5348_, 1);
                                v___x_5358_ = l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec___closed__0_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_;
                                v___x_5359_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5___redArg(v___x_5358_, v_a_5357_, v_a_5307_);
                                if leanh::lean_obj_tag(v___x_5359_) == 0 {
                                    leanh::lean_dec(v_a_5347_);
                                    leanh::lean_dec(v_isRemoved_x3f_5325_);
                                    leanh::lean_dec(v_isInserted_x3f_5324_);
                                    leanh::lean_dec(v_mvarId_5323_);
                                    leanh::lean_dec(v_goalPrefix_5322_);
                                    leanh::lean_dec(v_userName_x3f_5321_);
                                    leanh::lean_dec(v_ctx_5320_);
                                    v_a_5360_ = leanh::lean_ctor_get(v___x_5359_, 0);
                                    v_isSharedCheck_5367_ =
                                        (!leanh::lean_is_exclusive(v___x_5359_)) as u8;
                                    if v_isSharedCheck_5367_ == 0 {
                                        v___x_5362_ = v___x_5359_;
                                        v_isShared_5363_ = v_isSharedCheck_5367_;
                                        state = 9;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_5360_);
                                        leanh::lean_dec(v___x_5359_);
                                        v___x_5362_ = leanh::lean_box(0);
                                        v_isShared_5363_ = v_isSharedCheck_5367_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    v_a_5368_ = leanh::lean_ctor_get(v___x_5359_, 0);
                                    leanh::lean_inc(v_a_5368_);
                                    leanh::lean_dec_ref_known(v___x_5359_, 1);
                                    v___x_5369_ = l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_2318528980____hygCtx___hyg_3_;
                                    v___x_5370_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(v___x_5369_, v_ctx_5320_, v_a_5307_);
                                    if leanh::lean_obj_tag(v___x_5370_) == 0 {
                                        leanh::lean_dec(v_a_5368_);
                                        leanh::lean_dec(v_a_5347_);
                                        leanh::lean_dec(v_isRemoved_x3f_5325_);
                                        leanh::lean_dec(v_isInserted_x3f_5324_);
                                        leanh::lean_dec(v_mvarId_5323_);
                                        leanh::lean_dec(v_goalPrefix_5322_);
                                        leanh::lean_dec(v_userName_x3f_5321_);
                                        v_a_5371_ = leanh::lean_ctor_get(v___x_5370_, 0);
                                        v_isSharedCheck_5378_ =
                                            (!leanh::lean_is_exclusive(v___x_5370_)) as u8;
                                        if v_isSharedCheck_5378_ == 0 {
                                            v___x_5373_ = v___x_5370_;
                                            v_isShared_5374_ = v_isSharedCheck_5378_;
                                            state = 11;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_5371_);
                                            leanh::lean_dec(v___x_5370_);
                                            v___x_5373_ = leanh::lean_box(0);
                                            v_isShared_5374_ = v_isSharedCheck_5378_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_5379_ = leanh::lean_ctor_get(v___x_5370_, 0);
                                        v_isSharedCheck_5479_ =
                                            (!leanh::lean_is_exclusive(v___x_5370_)) as u8;
                                        if v_isSharedCheck_5479_ == 0 {
                                            v___x_5381_ = v___x_5370_;
                                            v_isShared_5382_ = v_isSharedCheck_5479_;
                                            state = 13;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_5379_);
                                            leanh::lean_dec(v___x_5370_);
                                            v___x_5381_ = leanh::lean_box(0);
                                            v_isShared_5382_ = v_isSharedCheck_5479_;
                                            state = 13;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5312_ == 0 {
                    v___x_5314_ = v___x_5311_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5315_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5315_, 0, v_a_5309_);
                    v___x_5314_ = v_reuseFailAlloc_5315_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5314_;
            }
            3 => {
                if v_isShared_5330_ == 0 {
                    v___x_5332_ = v___x_5329_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5333_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5333_, 0, v_a_5327_);
                    v___x_5332_ = v_reuseFailAlloc_5333_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5332_;
            }
            5 => {
                if v_isShared_5342_ == 0 {
                    v___x_5344_ = v___x_5341_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5345_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5345_, 0, v_a_5339_);
                    v___x_5344_ = v_reuseFailAlloc_5345_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5344_;
            }
            7 => {
                if v_isShared_5352_ == 0 {
                    v___x_5354_ = v___x_5351_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5355_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5355_, 0, v_a_5349_);
                    v___x_5354_ = v_reuseFailAlloc_5355_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5354_;
            }
            9 => {
                if v_isShared_5363_ == 0 {
                    v___x_5365_ = v___x_5362_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5366_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_a_5360_);
                    v___x_5365_ = v_reuseFailAlloc_5366_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5365_;
            }
            11 => {
                if v_isShared_5374_ == 0 {
                    v___x_5376_ = v___x_5373_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5377_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5377_, 0, v_a_5371_);
                    v___x_5376_ = v_reuseFailAlloc_5377_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5376_;
            }
            13 => {
                if leanh::lean_obj_tag(v_userName_x3f_5321_) == 0 {
                    v___x_5460_ = leanh::lean_box(0);
                    v_____do__lift_5419_ = v___x_5460_;
                    state = 21;
                    continue;
                } else {
                    v_val_5461_ = leanh::lean_ctor_get(v_userName_x3f_5321_, 0);
                    v_isSharedCheck_5478_ =
                        (!leanh::lean_is_exclusive(v_userName_x3f_5321_)) as u8;
                    if v_isSharedCheck_5478_ == 0 {
                        v___x_5463_ = v_userName_x3f_5321_;
                        v_isShared_5464_ = v_isSharedCheck_5478_;
                        state = 30;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5461_);
                        leanh::lean_dec(v_userName_x3f_5321_);
                        v___x_5463_ = leanh::lean_box(0);
                        v_isShared_5464_ = v_isSharedCheck_5478_;
                        state = 30;
                        continue;
                    }
                }
            }
            14 => {
                v___x_5389_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_5389_, 0, v_a_5347_);
                leanh::lean_ctor_set(v___x_5389_, 1, v_a_5368_);
                leanh::lean_ctor_set(v___x_5389_, 2, v_a_5379_);
                v___x_5390_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                leanh::lean_ctor_set(v___x_5390_, 0, v___x_5389_);
                leanh::lean_ctor_set(v___x_5390_, 1, v___y_5387_);
                leanh::lean_ctor_set(v___x_5390_, 2, v___y_5386_);
                leanh::lean_ctor_set(v___x_5390_, 3, v___y_5384_);
                leanh::lean_ctor_set(v___x_5390_, 4, v___y_5385_);
                leanh::lean_ctor_set(v___x_5390_, 5, v_____do__lift_5388_);
                if v_isShared_5382_ == 0 {
                    leanh::lean_ctor_set(v___x_5381_, 0, v___x_5390_);
                    v___x_5392_ = v___x_5381_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5393_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5393_, 0, v___x_5390_);
                    v___x_5392_ = v_reuseFailAlloc_5393_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5392_;
            }
            16 => {
                if leanh::lean_obj_tag(v_isRemoved_x3f_5325_) == 0 {
                    v___x_5399_ = leanh::lean_box(0);
                    v___y_5384_ = v___y_5395_;
                    v___y_5385_ = v_____do__lift_5398_;
                    v___y_5386_ = v___y_5396_;
                    v___y_5387_ = v___y_5397_;
                    v_____do__lift_5388_ = v___x_5399_;
                    state = 14;
                    continue;
                } else {
                    v_val_5400_ = leanh::lean_ctor_get(v_isRemoved_x3f_5325_, 0);
                    v_isSharedCheck_5417_ =
                        (!leanh::lean_is_exclusive(v_isRemoved_x3f_5325_)) as u8;
                    if v_isSharedCheck_5417_ == 0 {
                        v___x_5402_ = v_isRemoved_x3f_5325_;
                        v_isShared_5403_ = v_isSharedCheck_5417_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5400_);
                        leanh::lean_dec(v_isRemoved_x3f_5325_);
                        v___x_5402_ = leanh::lean_box(0);
                        v_isShared_5403_ = v_isSharedCheck_5417_;
                        state = 17;
                        continue;
                    }
                }
            }
            17 => {
                v___x_5404_ = l_Lean_Json_getBool_x3f(v_val_5400_);
                leanh::lean_dec(v_val_5400_);
                if leanh::lean_obj_tag(v___x_5404_) == 0 {
                    leanh::lean_del_object(v___x_5402_);
                    leanh::lean_dec(v_____do__lift_5398_);
                    leanh::lean_dec(v___y_5397_);
                    leanh::lean_dec_ref(v___y_5396_);
                    leanh::lean_dec(v___y_5395_);
                    leanh::lean_del_object(v___x_5381_);
                    leanh::lean_dec(v_a_5379_);
                    leanh::lean_dec(v_a_5368_);
                    leanh::lean_dec(v_a_5347_);
                    v_a_5405_ = leanh::lean_ctor_get(v___x_5404_, 0);
                    v_isSharedCheck_5412_ = (!leanh::lean_is_exclusive(v___x_5404_)) as u8;
                    if v_isSharedCheck_5412_ == 0 {
                        v___x_5407_ = v___x_5404_;
                        v_isShared_5408_ = v_isSharedCheck_5412_;
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5405_);
                        leanh::lean_dec(v___x_5404_);
                        v___x_5407_ = leanh::lean_box(0);
                        v_isShared_5408_ = v_isSharedCheck_5412_;
                        state = 18;
                        continue;
                    }
                } else {
                    v_a_5413_ = leanh::lean_ctor_get(v___x_5404_, 0);
                    leanh::lean_inc(v_a_5413_);
                    leanh::lean_dec_ref_known(v___x_5404_, 1);
                    if v_isShared_5403_ == 0 {
                        leanh::lean_ctor_set(v___x_5402_, 0, v_a_5413_);
                        v___x_5415_ = v___x_5402_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_5416_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5416_, 0, v_a_5413_);
                        v___x_5415_ = v_reuseFailAlloc_5416_;
                        state = 20;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_5408_ == 0 {
                    v___x_5410_ = v___x_5407_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5411_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5411_, 0, v_a_5405_);
                    v___x_5410_ = v_reuseFailAlloc_5411_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_5410_;
            }
            20 => {
                v___y_5384_ = v___y_5395_;
                v___y_5385_ = v_____do__lift_5398_;
                v___y_5386_ = v___y_5396_;
                v___y_5387_ = v___y_5397_;
                v_____do__lift_5388_ = v___x_5415_;
                state = 14;
                continue;
            }
            21 => {
                v___x_5420_ = l_Lean_Json_getStr_x3f(v_goalPrefix_5322_);
                if leanh::lean_obj_tag(v___x_5420_) == 0 {
                    leanh::lean_dec(v_____do__lift_5419_);
                    leanh::lean_del_object(v___x_5381_);
                    leanh::lean_dec(v_a_5379_);
                    leanh::lean_dec(v_a_5368_);
                    leanh::lean_dec(v_a_5347_);
                    leanh::lean_dec(v_isRemoved_x3f_5325_);
                    leanh::lean_dec(v_isInserted_x3f_5324_);
                    leanh::lean_dec(v_mvarId_5323_);
                    v_a_5421_ = leanh::lean_ctor_get(v___x_5420_, 0);
                    v_isSharedCheck_5428_ = (!leanh::lean_is_exclusive(v___x_5420_)) as u8;
                    if v_isSharedCheck_5428_ == 0 {
                        v___x_5423_ = v___x_5420_;
                        v_isShared_5424_ = v_isSharedCheck_5428_;
                        state = 22;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5421_);
                        leanh::lean_dec(v___x_5420_);
                        v___x_5423_ = leanh::lean_box(0);
                        v_isShared_5424_ = v_isSharedCheck_5428_;
                        state = 22;
                        continue;
                    }
                } else {
                    v_a_5429_ = leanh::lean_ctor_get(v___x_5420_, 0);
                    leanh::lean_inc(v_a_5429_);
                    leanh::lean_dec_ref_known(v___x_5420_, 1);
                    v___x_5430_ = l_Lean_Name_fromJson_x3f(v_mvarId_5323_);
                    if leanh::lean_obj_tag(v___x_5430_) == 0 {
                        leanh::lean_dec(v_a_5429_);
                        leanh::lean_dec(v_____do__lift_5419_);
                        leanh::lean_del_object(v___x_5381_);
                        leanh::lean_dec(v_a_5379_);
                        leanh::lean_dec(v_a_5368_);
                        leanh::lean_dec(v_a_5347_);
                        leanh::lean_dec(v_isRemoved_x3f_5325_);
                        leanh::lean_dec(v_isInserted_x3f_5324_);
                        v_a_5431_ = leanh::lean_ctor_get(v___x_5430_, 0);
                        v_isSharedCheck_5438_ =
                            (!leanh::lean_is_exclusive(v___x_5430_)) as u8;
                        if v_isSharedCheck_5438_ == 0 {
                            v___x_5433_ = v___x_5430_;
                            v_isShared_5434_ = v_isSharedCheck_5438_;
                            state = 24;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5431_);
                            leanh::lean_dec(v___x_5430_);
                            v___x_5433_ = leanh::lean_box(0);
                            v_isShared_5434_ = v_isSharedCheck_5438_;
                            state = 24;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v_isInserted_x3f_5324_) == 0 {
                            v_a_5439_ = leanh::lean_ctor_get(v___x_5430_, 0);
                            leanh::lean_inc(v_a_5439_);
                            leanh::lean_dec_ref_known(v___x_5430_, 1);
                            v___x_5440_ = leanh::lean_box(0);
                            v___y_5395_ = v_a_5439_;
                            v___y_5396_ = v_a_5429_;
                            v___y_5397_ = v_____do__lift_5419_;
                            v_____do__lift_5398_ = v___x_5440_;
                            state = 16;
                            continue;
                        } else {
                            v_a_5441_ = leanh::lean_ctor_get(v___x_5430_, 0);
                            leanh::lean_inc(v_a_5441_);
                            leanh::lean_dec_ref_known(v___x_5430_, 1);
                            v_val_5442_ = leanh::lean_ctor_get(v_isInserted_x3f_5324_, 0);
                            v_isSharedCheck_5459_ =
                                (!leanh::lean_is_exclusive(v_isInserted_x3f_5324_)) as u8;
                            if v_isSharedCheck_5459_ == 0 {
                                v___x_5444_ = v_isInserted_x3f_5324_;
                                v_isShared_5445_ = v_isSharedCheck_5459_;
                                state = 26;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_5442_);
                                leanh::lean_dec(v_isInserted_x3f_5324_);
                                v___x_5444_ = leanh::lean_box(0);
                                v_isShared_5445_ = v_isSharedCheck_5459_;
                                state = 26;
                                continue;
                            }
                        }
                    }
                }
            }
            22 => {
                if v_isShared_5424_ == 0 {
                    v___x_5426_ = v___x_5423_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_5427_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5427_, 0, v_a_5421_);
                    v___x_5426_ = v_reuseFailAlloc_5427_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_5426_;
            }
            24 => {
                if v_isShared_5434_ == 0 {
                    v___x_5436_ = v___x_5433_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_5437_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5437_, 0, v_a_5431_);
                    v___x_5436_ = v_reuseFailAlloc_5437_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_5436_;
            }
            26 => {
                v___x_5446_ = l_Lean_Json_getBool_x3f(v_val_5442_);
                leanh::lean_dec(v_val_5442_);
                if leanh::lean_obj_tag(v___x_5446_) == 0 {
                    leanh::lean_del_object(v___x_5444_);
                    leanh::lean_dec(v_a_5441_);
                    leanh::lean_dec(v_a_5429_);
                    leanh::lean_dec(v_____do__lift_5419_);
                    leanh::lean_del_object(v___x_5381_);
                    leanh::lean_dec(v_a_5379_);
                    leanh::lean_dec(v_a_5368_);
                    leanh::lean_dec(v_a_5347_);
                    leanh::lean_dec(v_isRemoved_x3f_5325_);
                    v_a_5447_ = leanh::lean_ctor_get(v___x_5446_, 0);
                    v_isSharedCheck_5454_ = (!leanh::lean_is_exclusive(v___x_5446_)) as u8;
                    if v_isSharedCheck_5454_ == 0 {
                        v___x_5449_ = v___x_5446_;
                        v_isShared_5450_ = v_isSharedCheck_5454_;
                        state = 27;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5447_);
                        leanh::lean_dec(v___x_5446_);
                        v___x_5449_ = leanh::lean_box(0);
                        v_isShared_5450_ = v_isSharedCheck_5454_;
                        state = 27;
                        continue;
                    }
                } else {
                    v_a_5455_ = leanh::lean_ctor_get(v___x_5446_, 0);
                    leanh::lean_inc(v_a_5455_);
                    leanh::lean_dec_ref_known(v___x_5446_, 1);
                    if v_isShared_5445_ == 0 {
                        leanh::lean_ctor_set(v___x_5444_, 0, v_a_5455_);
                        v___x_5457_ = v___x_5444_;
                        state = 29;
                        continue;
                    } else {
                        v_reuseFailAlloc_5458_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5458_, 0, v_a_5455_);
                        v___x_5457_ = v_reuseFailAlloc_5458_;
                        state = 29;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_5450_ == 0 {
                    v___x_5452_ = v___x_5449_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5453_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5453_, 0, v_a_5447_);
                    v___x_5452_ = v_reuseFailAlloc_5453_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_5452_;
            }
            29 => {
                v___y_5395_ = v_a_5441_;
                v___y_5396_ = v_a_5429_;
                v___y_5397_ = v_____do__lift_5419_;
                v_____do__lift_5398_ = v___x_5457_;
                state = 16;
                continue;
            }
            30 => {
                v___x_5465_ = l_Lean_Json_getStr_x3f(v_val_5461_);
                if leanh::lean_obj_tag(v___x_5465_) == 0 {
                    leanh::lean_del_object(v___x_5463_);
                    leanh::lean_del_object(v___x_5381_);
                    leanh::lean_dec(v_a_5379_);
                    leanh::lean_dec(v_a_5368_);
                    leanh::lean_dec(v_a_5347_);
                    leanh::lean_dec(v_isRemoved_x3f_5325_);
                    leanh::lean_dec(v_isInserted_x3f_5324_);
                    leanh::lean_dec(v_mvarId_5323_);
                    leanh::lean_dec(v_goalPrefix_5322_);
                    v_a_5466_ = leanh::lean_ctor_get(v___x_5465_, 0);
                    v_isSharedCheck_5473_ = (!leanh::lean_is_exclusive(v___x_5465_)) as u8;
                    if v_isSharedCheck_5473_ == 0 {
                        v___x_5468_ = v___x_5465_;
                        v_isShared_5469_ = v_isSharedCheck_5473_;
                        state = 31;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5466_);
                        leanh::lean_dec(v___x_5465_);
                        v___x_5468_ = leanh::lean_box(0);
                        v_isShared_5469_ = v_isSharedCheck_5473_;
                        state = 31;
                        continue;
                    }
                } else {
                    v_a_5474_ = leanh::lean_ctor_get(v___x_5465_, 0);
                    leanh::lean_inc(v_a_5474_);
                    leanh::lean_dec_ref_known(v___x_5465_, 1);
                    if v_isShared_5464_ == 0 {
                        leanh::lean_ctor_set(v___x_5463_, 0, v_a_5474_);
                        v___x_5476_ = v___x_5463_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_5477_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5477_, 0, v_a_5474_);
                        v___x_5476_ = v_reuseFailAlloc_5477_;
                        state = 33;
                        continue;
                    }
                }
            }
            31 => {
                if v_isShared_5469_ == 0 {
                    v___x_5471_ = v___x_5468_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_5472_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5472_, 0, v_a_5466_);
                    v___x_5471_ = v_reuseFailAlloc_5472_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_5471_;
            }
            33 => {
                v_____do__lift_5419_ = v___x_5476_;
                state = 21;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_instRpcEncodableInteractiveGoal_dec_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1____boxed(
    mut v_j_5480_: *mut leanh::LeanObject,
    mut v_a_5481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5482_ = l_Lean_Widget_instRpcEncodableInteractiveGoal_dec_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1_(v_j_5480_, v_a_5481_);
    leanh::lean_dec_ref(v_a_5481_);
    return v_res_5482_;
}
pub unsafe fn l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18_(
    mut v_json_5491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5509_: u8 = 0;
    let mut v___x_5510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5514_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5492_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
                leanh::lean_inc_n(v_json_5491_, 4);
                v___x_5493_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_5491_, v___x_5492_);
                v_a_5494_ = leanh::lean_ctor_get(v___x_5493_, 0);
                leanh::lean_inc(v_a_5494_);
                leanh::lean_dec_ref(v___x_5493_);
                v___x_5495_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
                v___x_5496_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_5491_, v___x_5495_);
                v_a_5497_ = leanh::lean_ctor_get(v___x_5496_, 0);
                leanh::lean_inc(v_a_5497_);
                leanh::lean_dec_ref(v___x_5496_);
                v___x_5498_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
                v___x_5499_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_5491_, v___x_5498_);
                v_a_5500_ = leanh::lean_ctor_get(v___x_5499_, 0);
                leanh::lean_inc(v_a_5500_);
                leanh::lean_dec_ref(v___x_5499_);
                v___x_5501_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18_;
                v___x_5502_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_5491_, v___x_5501_);
                v_a_5503_ = leanh::lean_ctor_get(v___x_5502_, 0);
                leanh::lean_inc(v_a_5503_);
                leanh::lean_dec_ref(v___x_5502_);
                v___x_5504_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18_;
                v___x_5505_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_5491_, v___x_5504_);
                v_a_5506_ = leanh::lean_ctor_get(v___x_5505_, 0);
                v_isSharedCheck_5514_ = (!leanh::lean_is_exclusive(v___x_5505_)) as u8;
                if v_isSharedCheck_5514_ == 0 {
                    v___x_5508_ = v___x_5505_;
                    v_isShared_5509_ = v_isSharedCheck_5514_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5506_);
                    leanh::lean_dec(v___x_5505_);
                    v___x_5508_ = leanh::lean_box(0);
                    v_isShared_5509_ = v_isSharedCheck_5514_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5510_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_5510_, 0, v_a_5494_);
                leanh::lean_ctor_set(v___x_5510_, 1, v_a_5497_);
                leanh::lean_ctor_set(v___x_5510_, 2, v_a_5500_);
                leanh::lean_ctor_set(v___x_5510_, 3, v_a_5503_);
                leanh::lean_ctor_set(v___x_5510_, 4, v_a_5506_);
                if v_isShared_5509_ == 0 {
                    leanh::lean_ctor_set(v___x_5508_, 0, v___x_5510_);
                    v___x_5512_ = v___x_5508_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5513_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5513_, 0, v___x_5510_);
                    v___x_5512_ = v_reuseFailAlloc_5513_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5512_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_36_(
    mut v_x_5517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hyps_5518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_5520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_5521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_5522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_hyps_5518_ = leanh::lean_ctor_get(v_x_5517_, 0);
    v_type_5519_ = leanh::lean_ctor_get(v_x_5517_, 1);
    v_ctx_5520_ = leanh::lean_ctor_get(v_x_5517_, 2);
    v_range_5521_ = leanh::lean_ctor_get(v_x_5517_, 3);
    v_term_5522_ = leanh::lean_ctor_get(v_x_5517_, 4);
    v___x_5523_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
    leanh::lean_inc(v_hyps_5518_);
    v___x_5524_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5524_, 0, v___x_5523_);
    leanh::lean_ctor_set(v___x_5524_, 1, v_hyps_5518_);
    v___x_5525_ = leanh::lean_box(0);
    v___x_5526_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5526_, 0, v___x_5524_);
    leanh::lean_ctor_set(v___x_5526_, 1, v___x_5525_);
    v___x_5527_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
    leanh::lean_inc(v_type_5519_);
    v___x_5528_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5528_, 0, v___x_5527_);
    leanh::lean_ctor_set(v___x_5528_, 1, v_type_5519_);
    v___x_5529_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5529_, 0, v___x_5528_);
    leanh::lean_ctor_set(v___x_5529_, 1, v___x_5525_);
    v___x_5530_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
    leanh::lean_inc(v_ctx_5520_);
    v___x_5531_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5531_, 0, v___x_5530_);
    leanh::lean_ctor_set(v___x_5531_, 1, v_ctx_5520_);
    v___x_5532_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5532_, 0, v___x_5531_);
    leanh::lean_ctor_set(v___x_5532_, 1, v___x_5525_);
    v___x_5533_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18_;
    leanh::lean_inc(v_range_5521_);
    v___x_5534_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5534_, 0, v___x_5533_);
    leanh::lean_ctor_set(v___x_5534_, 1, v_range_5521_);
    v___x_5535_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5535_, 0, v___x_5534_);
    leanh::lean_ctor_set(v___x_5535_, 1, v___x_5525_);
    v___x_5536_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18_;
    leanh::lean_inc(v_term_5522_);
    v___x_5537_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5537_, 0, v___x_5536_);
    leanh::lean_ctor_set(v___x_5537_, 1, v_term_5522_);
    v___x_5538_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5538_, 0, v___x_5537_);
    leanh::lean_ctor_set(v___x_5538_, 1, v___x_5525_);
    v___x_5539_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5539_, 0, v___x_5538_);
    leanh::lean_ctor_set(v___x_5539_, 1, v___x_5525_);
    v___x_5540_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5540_, 0, v___x_5535_);
    leanh::lean_ctor_set(v___x_5540_, 1, v___x_5539_);
    v___x_5541_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5541_, 0, v___x_5532_);
    leanh::lean_ctor_set(v___x_5541_, 1, v___x_5540_);
    v___x_5542_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5542_, 0, v___x_5529_);
    leanh::lean_ctor_set(v___x_5542_, 1, v___x_5541_);
    v___x_5543_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5543_, 0, v___x_5526_);
    leanh::lean_ctor_set(v___x_5543_, 1, v___x_5542_);
    v___x_5544_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47_;
    v___x_5545_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__1(v___x_5543_, v___x_5544_);
    v___x_5546_ = l_Lean_Json_mkObj(v___x_5545_);
    leanh::lean_dec(v___x_5545_);
    return v___x_5546_;
}
pub unsafe fn l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_36____boxed(
    mut v_x_5547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5548_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_36_(v_x_5547_);
    leanh::lean_dec_ref(v_x_5547_);
    return v_res_5548_;
}
pub unsafe fn l_Lean_Widget_instRpcEncodableInteractiveTermGoal_enc_00___x40_Lean_Widget_InteractiveGoal_2553565095____hygCtx___hyg_1_(
    mut v_a_5551_: *mut leanh::LeanObject,
    mut v_a_5552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toInteractiveGoalCore_5553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_5554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_5555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_5556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_5558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5559_: usize = 0;
    let mut v___x_5560_: usize = 0;
    let mut v___x_5561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5578_: u8 = 0;
    let mut v___x_5579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInteractiveGoalCore_5553_ = leanh::lean_ctor_get(v_a_5551_, 0);
                leanh::lean_inc_ref(v_toInteractiveGoalCore_5553_);
                v_range_5554_ = leanh::lean_ctor_get(v_a_5551_, 1);
                leanh::lean_inc_ref(v_range_5554_);
                v_term_5555_ = leanh::lean_ctor_get(v_a_5551_, 2);
                leanh::lean_inc_ref(v_term_5555_);
                leanh::lean_dec_ref(v_a_5551_);
                v_hyps_5556_ = leanh::lean_ctor_get(v_toInteractiveGoalCore_5553_, 0);
                leanh::lean_inc_ref(v_hyps_5556_);
                v_type_5557_ = leanh::lean_ctor_get(v_toInteractiveGoalCore_5553_, 1);
                leanh::lean_inc_ref(v_type_5557_);
                v_ctx_5558_ = leanh::lean_ctor_get(v_toInteractiveGoalCore_5553_, 2);
                leanh::lean_inc_ref(v_ctx_5558_);
                leanh::lean_dec_ref(v_toInteractiveGoalCore_5553_);
                v_sz_5559_ = lean_array_size(v_hyps_5556_);
                v___x_5560_ = 0usize;
                v___x_5561_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoal_enc_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1__spec__0(v_sz_5559_, v___x_5560_, v_hyps_5556_, v_a_5552_);
                v_fst_5562_ = leanh::lean_ctor_get(v___x_5561_, 0);
                leanh::lean_inc(v_fst_5562_);
                v_snd_5563_ = leanh::lean_ctor_get(v___x_5561_, 1);
                leanh::lean_inc(v_snd_5563_);
                leanh::lean_dec_ref(v___x_5561_);
                v___x_5564_ = l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc___closed__0_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_;
                v___x_5565_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___redArg(v___x_5564_, v_type_5557_, v_snd_5563_);
                v_fst_5566_ = leanh::lean_ctor_get(v___x_5565_, 0);
                leanh::lean_inc(v_fst_5566_);
                v_snd_5567_ = leanh::lean_ctor_get(v___x_5565_, 1);
                leanh::lean_inc(v_snd_5567_);
                leanh::lean_dec_ref(v___x_5565_);
                v___x_5568_ =
                    l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_2318528980____hygCtx___hyg_3_;
                v___x_5569_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(
                    v___x_5568_,
                    v_ctx_5558_,
                    v_snd_5567_,
                );
                leanh::lean_dec_ref(v_ctx_5558_);
                v_fst_5570_ = leanh::lean_ctor_get(v___x_5569_, 0);
                leanh::lean_inc(v_fst_5570_);
                v_snd_5571_ = leanh::lean_ctor_get(v___x_5569_, 1);
                leanh::lean_inc(v_snd_5571_);
                leanh::lean_dec_ref(v___x_5569_);
                v___x_5572_ =
                    l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_173954553____hygCtx___hyg_3_;
                v___x_5573_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(
                    v___x_5572_,
                    v_term_5555_,
                    v_snd_5571_,
                );
                leanh::lean_dec_ref(v_term_5555_);
                v_fst_5574_ = leanh::lean_ctor_get(v___x_5573_, 0);
                v_snd_5575_ = leanh::lean_ctor_get(v___x_5573_, 1);
                v_isSharedCheck_5587_ = (!leanh::lean_is_exclusive(v___x_5573_)) as u8;
                if v_isSharedCheck_5587_ == 0 {
                    v___x_5577_ = v___x_5573_;
                    v_isShared_5578_ = v_isSharedCheck_5587_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_5575_);
                    leanh::lean_inc(v_fst_5574_);
                    leanh::lean_dec(v___x_5573_);
                    v___x_5577_ = leanh::lean_box(0);
                    v_isShared_5578_ = v_isSharedCheck_5587_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5579_ = l_Array_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3(v_fst_5562_);
                v___x_5580_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(v_fst_5566_);
                v___x_5581_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_5554_);
                v___x_5582_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_5582_, 0, v___x_5579_);
                leanh::lean_ctor_set(v___x_5582_, 1, v___x_5580_);
                leanh::lean_ctor_set(v___x_5582_, 2, v_fst_5570_);
                leanh::lean_ctor_set(v___x_5582_, 3, v___x_5581_);
                leanh::lean_ctor_set(v___x_5582_, 4, v_fst_5574_);
                v___x_5583_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_36_(v___x_5582_);
                leanh::lean_dec_ref_known(v___x_5582_, 5);
                if v_isShared_5578_ == 0 {
                    leanh::lean_ctor_set(v___x_5577_, 0, v___x_5583_);
                    v___x_5585_ = v___x_5577_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5586_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5586_, 0, v___x_5583_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5586_, 1, v_snd_5575_);
                    v___x_5585_ = v_reuseFailAlloc_5586_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5585_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_instRpcEncodableInteractiveTermGoal_dec_00___x40_Lean_Widget_InteractiveGoal_2553565095____hygCtx___hyg_1_(
    mut v_j_5588_: *mut leanh::LeanObject,
    mut v_a_5589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5594_: u8 = 0;
    let mut v___x_5596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5598_: u8 = 0;
    let mut v_a_5599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_5600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_5602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_5603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_5604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5609_: u8 = 0;
    let mut v___x_5611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5613_: u8 = 0;
    let mut v_a_5614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5615_: usize = 0;
    let mut v___x_5616_: usize = 0;
    let mut v___x_5617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5621_: u8 = 0;
    let mut v___x_5623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5625_: u8 = 0;
    let mut v_a_5626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5631_: u8 = 0;
    let mut v___x_5633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5635_: u8 = 0;
    let mut v_a_5636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5642_: u8 = 0;
    let mut v___x_5644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5646_: u8 = 0;
    let mut v_a_5647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5653_: u8 = 0;
    let mut v___x_5655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5657_: u8 = 0;
    let mut v_a_5658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5663_: u8 = 0;
    let mut v___x_5665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5667_: u8 = 0;
    let mut v_a_5668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5674_: u8 = 0;
    let mut v___x_5676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5678_: u8 = 0;
    let mut v_a_5679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5682_: u8 = 0;
    let mut v___x_5683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5688_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5590_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18_(v_j_5588_);
                if leanh::lean_obj_tag(v___x_5590_) == 0 {
                    v_a_5591_ = leanh::lean_ctor_get(v___x_5590_, 0);
                    v_isSharedCheck_5598_ = (!leanh::lean_is_exclusive(v___x_5590_)) as u8;
                    if v_isSharedCheck_5598_ == 0 {
                        v___x_5593_ = v___x_5590_;
                        v_isShared_5594_ = v_isSharedCheck_5598_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5591_);
                        leanh::lean_dec(v___x_5590_);
                        v___x_5593_ = leanh::lean_box(0);
                        v_isShared_5594_ = v_isSharedCheck_5598_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5599_ = leanh::lean_ctor_get(v___x_5590_, 0);
                    leanh::lean_inc(v_a_5599_);
                    leanh::lean_dec_ref_known(v___x_5590_, 1);
                    v_hyps_5600_ = leanh::lean_ctor_get(v_a_5599_, 0);
                    leanh::lean_inc(v_hyps_5600_);
                    v_type_5601_ = leanh::lean_ctor_get(v_a_5599_, 1);
                    leanh::lean_inc(v_type_5601_);
                    v_ctx_5602_ = leanh::lean_ctor_get(v_a_5599_, 2);
                    leanh::lean_inc(v_ctx_5602_);
                    v_range_5603_ = leanh::lean_ctor_get(v_a_5599_, 3);
                    leanh::lean_inc(v_range_5603_);
                    v_term_5604_ = leanh::lean_ctor_get(v_a_5599_, 4);
                    leanh::lean_inc(v_term_5604_);
                    leanh::lean_dec(v_a_5599_);
                    v___x_5605_ = l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0(v_hyps_5600_);
                    if leanh::lean_obj_tag(v___x_5605_) == 0 {
                        leanh::lean_dec(v_term_5604_);
                        leanh::lean_dec(v_range_5603_);
                        leanh::lean_dec(v_ctx_5602_);
                        leanh::lean_dec(v_type_5601_);
                        v_a_5606_ = leanh::lean_ctor_get(v___x_5605_, 0);
                        v_isSharedCheck_5613_ =
                            (!leanh::lean_is_exclusive(v___x_5605_)) as u8;
                        if v_isSharedCheck_5613_ == 0 {
                            v___x_5608_ = v___x_5605_;
                            v_isShared_5609_ = v_isSharedCheck_5613_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5606_);
                            leanh::lean_dec(v___x_5605_);
                            v___x_5608_ = leanh::lean_box(0);
                            v_isShared_5609_ = v_isSharedCheck_5613_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5614_ = leanh::lean_ctor_get(v___x_5605_, 0);
                        leanh::lean_inc(v_a_5614_);
                        leanh::lean_dec_ref_known(v___x_5605_, 1);
                        v_sz_5615_ = lean_array_size(v_a_5614_);
                        v___x_5616_ = 0usize;
                        v___x_5617_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoal_dec_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1__spec__0(v_sz_5615_, v___x_5616_, v_a_5614_, v_a_5589_);
                        if leanh::lean_obj_tag(v___x_5617_) == 0 {
                            leanh::lean_dec(v_term_5604_);
                            leanh::lean_dec(v_range_5603_);
                            leanh::lean_dec(v_ctx_5602_);
                            leanh::lean_dec(v_type_5601_);
                            v_a_5618_ = leanh::lean_ctor_get(v___x_5617_, 0);
                            v_isSharedCheck_5625_ =
                                (!leanh::lean_is_exclusive(v___x_5617_)) as u8;
                            if v_isSharedCheck_5625_ == 0 {
                                v___x_5620_ = v___x_5617_;
                                v_isShared_5621_ = v_isSharedCheck_5625_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5618_);
                                leanh::lean_dec(v___x_5617_);
                                v___x_5620_ = leanh::lean_box(0);
                                v_isShared_5621_ = v_isSharedCheck_5625_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v_a_5626_ = leanh::lean_ctor_get(v___x_5617_, 0);
                            leanh::lean_inc(v_a_5626_);
                            leanh::lean_dec_ref_known(v___x_5617_, 1);
                            v___x_5627_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(v_type_5601_);
                            if leanh::lean_obj_tag(v___x_5627_) == 0 {
                                leanh::lean_dec(v_a_5626_);
                                leanh::lean_dec(v_term_5604_);
                                leanh::lean_dec(v_range_5603_);
                                leanh::lean_dec(v_ctx_5602_);
                                v_a_5628_ = leanh::lean_ctor_get(v___x_5627_, 0);
                                v_isSharedCheck_5635_ =
                                    (!leanh::lean_is_exclusive(v___x_5627_)) as u8;
                                if v_isSharedCheck_5635_ == 0 {
                                    v___x_5630_ = v___x_5627_;
                                    v_isShared_5631_ = v_isSharedCheck_5635_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5628_);
                                    leanh::lean_dec(v___x_5627_);
                                    v___x_5630_ = leanh::lean_box(0);
                                    v_isShared_5631_ = v_isSharedCheck_5635_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_5636_ = leanh::lean_ctor_get(v___x_5627_, 0);
                                leanh::lean_inc(v_a_5636_);
                                leanh::lean_dec_ref_known(v___x_5627_, 1);
                                v___x_5637_ = l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec___closed__0_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_;
                                v___x_5638_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5___redArg(v___x_5637_, v_a_5636_, v_a_5589_);
                                if leanh::lean_obj_tag(v___x_5638_) == 0 {
                                    leanh::lean_dec(v_a_5626_);
                                    leanh::lean_dec(v_term_5604_);
                                    leanh::lean_dec(v_range_5603_);
                                    leanh::lean_dec(v_ctx_5602_);
                                    v_a_5639_ = leanh::lean_ctor_get(v___x_5638_, 0);
                                    v_isSharedCheck_5646_ =
                                        (!leanh::lean_is_exclusive(v___x_5638_)) as u8;
                                    if v_isSharedCheck_5646_ == 0 {
                                        v___x_5641_ = v___x_5638_;
                                        v_isShared_5642_ = v_isSharedCheck_5646_;
                                        state = 9;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_5639_);
                                        leanh::lean_dec(v___x_5638_);
                                        v___x_5641_ = leanh::lean_box(0);
                                        v_isShared_5642_ = v_isSharedCheck_5646_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    v_a_5647_ = leanh::lean_ctor_get(v___x_5638_, 0);
                                    leanh::lean_inc(v_a_5647_);
                                    leanh::lean_dec_ref_known(v___x_5638_, 1);
                                    v___x_5648_ = l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_2318528980____hygCtx___hyg_3_;
                                    v___x_5649_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(v___x_5648_, v_ctx_5602_, v_a_5589_);
                                    if leanh::lean_obj_tag(v___x_5649_) == 0 {
                                        leanh::lean_dec(v_a_5647_);
                                        leanh::lean_dec(v_a_5626_);
                                        leanh::lean_dec(v_term_5604_);
                                        leanh::lean_dec(v_range_5603_);
                                        v_a_5650_ = leanh::lean_ctor_get(v___x_5649_, 0);
                                        v_isSharedCheck_5657_ =
                                            (!leanh::lean_is_exclusive(v___x_5649_)) as u8;
                                        if v_isSharedCheck_5657_ == 0 {
                                            v___x_5652_ = v___x_5649_;
                                            v_isShared_5653_ = v_isSharedCheck_5657_;
                                            state = 11;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_5650_);
                                            leanh::lean_dec(v___x_5649_);
                                            v___x_5652_ = leanh::lean_box(0);
                                            v_isShared_5653_ = v_isSharedCheck_5657_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_5658_ = leanh::lean_ctor_get(v___x_5649_, 0);
                                        leanh::lean_inc(v_a_5658_);
                                        leanh::lean_dec_ref_known(v___x_5649_, 1);
                                        v___x_5659_ =
                                            l_Lean_Lsp_instFromJsonRange_fromJson(v_range_5603_);
                                        if leanh::lean_obj_tag(v___x_5659_) == 0 {
                                            leanh::lean_dec(v_a_5658_);
                                            leanh::lean_dec(v_a_5647_);
                                            leanh::lean_dec(v_a_5626_);
                                            leanh::lean_dec(v_term_5604_);
                                            v_a_5660_ = leanh::lean_ctor_get(v___x_5659_, 0);
                                            v_isSharedCheck_5667_ =
                                                (!leanh::lean_is_exclusive(v___x_5659_))
                                                    as u8;
                                            if v_isSharedCheck_5667_ == 0 {
                                                v___x_5662_ = v___x_5659_;
                                                v_isShared_5663_ = v_isSharedCheck_5667_;
                                                state = 13;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_5660_);
                                                leanh::lean_dec(v___x_5659_);
                                                v___x_5662_ = leanh::lean_box(0);
                                                v_isShared_5663_ = v_isSharedCheck_5667_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            v_a_5668_ = leanh::lean_ctor_get(v___x_5659_, 0);
                                            leanh::lean_inc(v_a_5668_);
                                            leanh::lean_dec_ref_known(v___x_5659_, 1);
                                            v___x_5669_ = l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_173954553____hygCtx___hyg_3_;
                                            v___x_5670_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(v___x_5669_, v_term_5604_, v_a_5589_);
                                            if leanh::lean_obj_tag(v___x_5670_) == 0 {
                                                leanh::lean_dec(v_a_5668_);
                                                leanh::lean_dec(v_a_5658_);
                                                leanh::lean_dec(v_a_5647_);
                                                leanh::lean_dec(v_a_5626_);
                                                v_a_5671_ =
                                                    leanh::lean_ctor_get(v___x_5670_, 0);
                                                v_isSharedCheck_5678_ =
                                                    (!leanh::lean_is_exclusive(v___x_5670_))
                                                        as u8;
                                                if v_isSharedCheck_5678_ == 0 {
                                                    v___x_5673_ = v___x_5670_;
                                                    v_isShared_5674_ = v_isSharedCheck_5678_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_5671_);
                                                    leanh::lean_dec(v___x_5670_);
                                                    v___x_5673_ = leanh::lean_box(0);
                                                    v_isShared_5674_ = v_isSharedCheck_5678_;
                                                    state = 15;
                                                    continue;
                                                }
                                            } else {
                                                v_a_5679_ =
                                                    leanh::lean_ctor_get(v___x_5670_, 0);
                                                v_isSharedCheck_5688_ =
                                                    (!leanh::lean_is_exclusive(v___x_5670_))
                                                        as u8;
                                                if v_isSharedCheck_5688_ == 0 {
                                                    v___x_5681_ = v___x_5670_;
                                                    v_isShared_5682_ = v_isSharedCheck_5688_;
                                                    state = 17;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_5679_);
                                                    leanh::lean_dec(v___x_5670_);
                                                    v___x_5681_ = leanh::lean_box(0);
                                                    v_isShared_5682_ = v_isSharedCheck_5688_;
                                                    state = 17;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5594_ == 0 {
                    v___x_5596_ = v___x_5593_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5597_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5597_, 0, v_a_5591_);
                    v___x_5596_ = v_reuseFailAlloc_5597_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5596_;
            }
            3 => {
                if v_isShared_5609_ == 0 {
                    v___x_5611_ = v___x_5608_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5612_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5612_, 0, v_a_5606_);
                    v___x_5611_ = v_reuseFailAlloc_5612_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5611_;
            }
            5 => {
                if v_isShared_5621_ == 0 {
                    v___x_5623_ = v___x_5620_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5624_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5624_, 0, v_a_5618_);
                    v___x_5623_ = v_reuseFailAlloc_5624_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5623_;
            }
            7 => {
                if v_isShared_5631_ == 0 {
                    v___x_5633_ = v___x_5630_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5634_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5634_, 0, v_a_5628_);
                    v___x_5633_ = v_reuseFailAlloc_5634_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5633_;
            }
            9 => {
                if v_isShared_5642_ == 0 {
                    v___x_5644_ = v___x_5641_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5645_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5645_, 0, v_a_5639_);
                    v___x_5644_ = v_reuseFailAlloc_5645_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5644_;
            }
            11 => {
                if v_isShared_5653_ == 0 {
                    v___x_5655_ = v___x_5652_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5656_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5656_, 0, v_a_5650_);
                    v___x_5655_ = v_reuseFailAlloc_5656_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5655_;
            }
            13 => {
                if v_isShared_5663_ == 0 {
                    v___x_5665_ = v___x_5662_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5666_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5666_, 0, v_a_5660_);
                    v___x_5665_ = v_reuseFailAlloc_5666_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5665_;
            }
            15 => {
                if v_isShared_5674_ == 0 {
                    v___x_5676_ = v___x_5673_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5677_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5677_, 0, v_a_5671_);
                    v___x_5676_ = v_reuseFailAlloc_5677_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5676_;
            }
            17 => {
                v___x_5683_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_5683_, 0, v_a_5626_);
                leanh::lean_ctor_set(v___x_5683_, 1, v_a_5647_);
                leanh::lean_ctor_set(v___x_5683_, 2, v_a_5658_);
                v___x_5684_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_5684_, 0, v___x_5683_);
                leanh::lean_ctor_set(v___x_5684_, 1, v_a_5668_);
                leanh::lean_ctor_set(v___x_5684_, 2, v_a_5679_);
                if v_isShared_5682_ == 0 {
                    leanh::lean_ctor_set(v___x_5681_, 0, v___x_5684_);
                    v___x_5686_ = v___x_5681_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5687_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5687_, 0, v___x_5684_);
                    v___x_5686_ = v_reuseFailAlloc_5687_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5686_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_instRpcEncodableInteractiveTermGoal_dec_00___x40_Lean_Widget_InteractiveGoal_2553565095____hygCtx___hyg_1____boxed(
    mut v_j_5689_: *mut leanh::LeanObject,
    mut v_a_5690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5691_ = l_Lean_Widget_instRpcEncodableInteractiveTermGoal_dec_00___x40_Lean_Widget_InteractiveGoal_2553565095____hygCtx___hyg_1_(v_j_5689_, v_a_5690_);
    leanh::lean_dec_ref(v_a_5690_);
    return v_res_5691_;
}
pub unsafe fn l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_InteractiveGoalCore_pretty_addLine(
    mut v_fmt_5698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5699_: u8 = 0;
    v___x_5699_ = l_Std_Format_isNil(v_fmt_5698_);
    if v___x_5699_ == 0 {
        let mut v___x_5700_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5701_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5700_ = leanh::lean_box(1);
        v___x_5701_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_5701_, 0, v_fmt_5698_);
        leanh::lean_ctor_set(v___x_5701_, 1, v___x_5700_);
        return v___x_5701_;
    } else {
        return v_fmt_5698_;
    }
}
pub unsafe fn _init_l_List_filterTR_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5702_: u8 = 0;
    let mut v___x_5703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5702_ = 1;
    v___x_5703_ = leanh::lean_box(0);
    v___x_5704_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5703_, v___x_5702_);
    return v___x_5704_;
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__0(
    mut v_a_5705_: *mut leanh::LeanObject,
    mut v_a_5706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5712_: u8 = 0;
    let mut v___x_5713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: u8 = 0;
    let mut v___x_5716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5720_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_5705_) == 0 {
                    v___x_5707_ = l_List_reverse___redArg(v_a_5706_);
                    return v___x_5707_;
                } else {
                    v_head_5708_ = leanh::lean_ctor_get(v_a_5705_, 0);
                    v_tail_5709_ = leanh::lean_ctor_get(v_a_5705_, 1);
                    v_isSharedCheck_5720_ = (!leanh::lean_is_exclusive(v_a_5705_)) as u8;
                    if v_isSharedCheck_5720_ == 0 {
                        v___x_5711_ = v_a_5705_;
                        v_isShared_5712_ = v_isSharedCheck_5720_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5709_);
                        leanh::lean_inc(v_head_5708_);
                        leanh::lean_dec(v_a_5705_);
                        v___x_5711_ = leanh::lean_box(0);
                        v_isShared_5712_ = v_isSharedCheck_5720_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5713_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_filterTR_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__0___closed__0), core::ptr::addr_of_mut!(l_List_filterTR_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__0___closed__0_once), _init_l_List_filterTR_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__0___closed__0);
                v___x_5714_ = lean_string_dec_eq(v_head_5708_, v___x_5713_);
                if v___x_5714_ == 0 {
                    if v_isShared_5712_ == 0 {
                        leanh::lean_ctor_set(v___x_5711_, 1, v_a_5706_);
                        v___x_5716_ = v___x_5711_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5718_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5718_, 0, v_head_5708_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5718_, 1, v_a_5706_);
                        v___x_5716_ = v_reuseFailAlloc_5718_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5711_);
                    leanh::lean_dec(v_head_5708_);
                    v_a_5705_ = v_tail_5709_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_a_5705_ = v_tail_5709_;
                v_a_5706_ = v___x_5716_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indent_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5721_ = leanh::lean_unsigned_to_nat(2);
    v_indent_5722_ = lean_nat_to_int(v___x_5721_);
    return v_indent_5722_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1(
    mut v_as_5737_: *mut leanh::LeanObject,
    mut v_sz_5738_: usize,
    mut v_i_5739_: usize,
    mut v_b_5740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_5742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: usize = 0;
    let mut v___x_5744_: usize = 0;
    let mut v___x_5746_: u8 = 0;
    let mut v_a_5747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_names_5748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_x3f_5750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indent_5751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: u8 = 0;
    let mut v___x_5760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: u8 = 0;
    let mut v___x_5770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5775_: u8 = 0;
    let mut v___x_5777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: u8 = 0;
    let mut v___x_5792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5795_: u8 = 0;
    let mut v___x_5796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: u8 = 0;
    let mut v___x_5804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5746_ = lean_usize_dec_lt(v_i_5739_, v_sz_5738_);
                if v___x_5746_ == 0 {
                    return v_b_5740_;
                } else {
                    v_a_5747_ = lean_array_uget_borrowed(v_as_5737_, v_i_5739_);
                    v_names_5748_ = leanh::lean_ctor_get(v_a_5747_, 0);
                    v_type_5749_ = leanh::lean_ctor_get(v_a_5747_, 2);
                    v_val_x3f_5750_ = leanh::lean_ctor_get(v_a_5747_, 3);
                    leanh::lean_inc(v_val_x3f_5750_);
                    v_indent_5751_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__0);
                    v___x_5752_ = l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_InteractiveGoalCore_pretty_addLine(v_b_5740_);
                    v___x_5753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__1;
                    leanh::lean_inc_ref(v_names_5748_);
                    v___x_5754_ = lean_array_to_list(v_names_5748_);
                    v___x_5755_ = leanh::lean_box(0);
                    v___x_5756_ = l_List_filterTR_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__0(v___x_5754_, v___x_5755_);
                    v___x_5757_ = l_String_intercalate(v___x_5753_, v___x_5756_);
                    v___x_5758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__2;
                    v___x_5759_ = lean_string_dec_eq(v___x_5757_, v___x_5758_);
                    if v___x_5759_ == 0 {
                        if leanh::lean_obj_tag(v_val_x3f_5750_) == 0 {
                            v___x_5760_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_5760_, 0, v___x_5757_);
                            v___x_5761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__4;
                            v___x_5762_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5762_, 0, v___x_5760_);
                            leanh::lean_ctor_set(v___x_5762_, 1, v___x_5761_);
                            v___x_5763_ = leanh::lean_box(1);
                            leanh::lean_inc_ref(v_type_5749_);
                            v___x_5764_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_type_5749_);
                            v___x_5765_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_5765_, 0, v___x_5764_);
                            v___x_5766_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5766_, 0, v___x_5763_);
                            leanh::lean_ctor_set(v___x_5766_, 1, v___x_5765_);
                            v___x_5767_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5767_, 0, v_indent_5751_);
                            leanh::lean_ctor_set(v___x_5767_, 1, v___x_5766_);
                            v___x_5768_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5768_, 0, v___x_5762_);
                            leanh::lean_ctor_set(v___x_5768_, 1, v___x_5767_);
                            v___x_5769_ = 0;
                            v___x_5770_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                            leanh::lean_ctor_set(v___x_5770_, 0, v___x_5768_);
                            leanh::lean_ctor_set_uint8(
                                v___x_5770_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                                v___x_5769_,
                            );
                            v___x_5771_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5771_, 0, v___x_5752_);
                            leanh::lean_ctor_set(v___x_5771_, 1, v___x_5770_);
                            v_a_5742_ = v___x_5771_;
                            state = 1;
                            continue;
                        } else {
                            v_val_5772_ = leanh::lean_ctor_get(v_val_x3f_5750_, 0);
                            v_isSharedCheck_5795_ =
                                (!leanh::lean_is_exclusive(v_val_x3f_5750_)) as u8;
                            if v_isSharedCheck_5795_ == 0 {
                                v___x_5774_ = v_val_x3f_5750_;
                                v_isShared_5775_ = v_isSharedCheck_5795_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_5772_);
                                leanh::lean_dec(v_val_x3f_5750_);
                                v___x_5774_ = leanh::lean_box(0);
                                v_isShared_5775_ = v_isSharedCheck_5795_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_5757_);
                        leanh::lean_dec(v_val_x3f_5750_);
                        v___x_5796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__10;
                        v___x_5797_ = leanh::lean_box(1);
                        leanh::lean_inc_ref(v_type_5749_);
                        v___x_5798_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_type_5749_);
                        v___x_5799_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5799_, 0, v___x_5798_);
                        v___x_5800_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5800_, 0, v___x_5797_);
                        leanh::lean_ctor_set(v___x_5800_, 1, v___x_5799_);
                        v___x_5801_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5801_, 0, v_indent_5751_);
                        leanh::lean_ctor_set(v___x_5801_, 1, v___x_5800_);
                        v___x_5802_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5802_, 0, v___x_5796_);
                        leanh::lean_ctor_set(v___x_5802_, 1, v___x_5801_);
                        v___x_5803_ = 0;
                        v___x_5804_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_5804_, 0, v___x_5802_);
                        leanh::lean_ctor_set_uint8(
                            v___x_5804_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_5803_,
                        );
                        v___x_5805_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5805_, 0, v___x_5752_);
                        leanh::lean_ctor_set(v___x_5805_, 1, v___x_5804_);
                        v_a_5742_ = v___x_5805_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5743_ = 1usize;
                v___x_5744_ = lean_usize_add(v_i_5739_, v___x_5743_);
                v_i_5739_ = v___x_5744_;
                v_b_5740_ = v_a_5742_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_5775_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5774_, 3);
                    leanh::lean_ctor_set(v___x_5774_, 0, v___x_5757_);
                    v___x_5777_ = v___x_5774_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5794_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5794_, 0, v___x_5757_);
                    v___x_5777_ = v_reuseFailAlloc_5794_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__6;
                v___x_5779_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5779_, 0, v___x_5777_);
                leanh::lean_ctor_set(v___x_5779_, 1, v___x_5778_);
                leanh::lean_inc_ref(v_type_5749_);
                v___x_5780_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_type_5749_);
                v___x_5781_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5781_, 0, v___x_5780_);
                v___x_5782_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5782_, 0, v___x_5779_);
                leanh::lean_ctor_set(v___x_5782_, 1, v___x_5781_);
                v___x_5783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__8;
                v___x_5784_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5784_, 0, v___x_5782_);
                leanh::lean_ctor_set(v___x_5784_, 1, v___x_5783_);
                v___x_5785_ = leanh::lean_box(1);
                v___x_5786_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_val_5772_);
                v___x_5787_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5787_, 0, v___x_5786_);
                v___x_5788_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5788_, 0, v___x_5785_);
                leanh::lean_ctor_set(v___x_5788_, 1, v___x_5787_);
                v___x_5789_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5789_, 0, v_indent_5751_);
                leanh::lean_ctor_set(v___x_5789_, 1, v___x_5788_);
                v___x_5790_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5790_, 0, v___x_5784_);
                leanh::lean_ctor_set(v___x_5790_, 1, v___x_5789_);
                v___x_5791_ = 0;
                v___x_5792_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_5792_, 0, v___x_5790_);
                leanh::lean_ctor_set_uint8(
                    v___x_5792_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_5791_,
                );
                v___x_5793_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5793_, 0, v___x_5752_);
                leanh::lean_ctor_set(v___x_5793_, 1, v___x_5792_);
                v_a_5742_ = v___x_5793_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___boxed(
    mut v_as_5806_: *mut leanh::LeanObject,
    mut v_sz_5807_: *mut leanh::LeanObject,
    mut v_i_5808_: *mut leanh::LeanObject,
    mut v_b_5809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5810_: usize = 0;
    let mut v_i_boxed_5811_: usize = 0;
    let mut v_res_5812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5810_ = leanh::lean_unbox_usize(v_sz_5807_);
    leanh::lean_dec(v_sz_5807_);
    v_i_boxed_5811_ = leanh::lean_unbox_usize(v_i_5808_);
    leanh::lean_dec(v_i_5808_);
    v_res_5812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1(v_as_5806_, v_sz_boxed_5810_, v_i_boxed_5811_, v_b_5809_);
    leanh::lean_dec_ref(v_as_5806_);
    return v_res_5812_;
}
pub unsafe fn l_Lean_Widget_InteractiveGoalCore_pretty(
    mut v_g_5816_: *mut leanh::LeanObject,
    mut v_userName_x3f_5817_: *mut leanh::LeanObject,
    mut v_goalPrefix_5818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_indent_5819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_5822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5824_: usize = 0;
    let mut v___x_5825_: usize = 0;
    let mut v___x_5826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5838_: u8 = 0;
    let mut v___x_5839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5844_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_indent_5819_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__0);
                if leanh::lean_obj_tag(v_userName_x3f_5817_) == 0 {
                    v___x_5834_ = leanh::lean_box(0);
                    v___y_5821_ = v___x_5834_;
                    state = 1;
                    continue;
                } else {
                    v_val_5835_ = leanh::lean_ctor_get(v_userName_x3f_5817_, 0);
                    v_isSharedCheck_5844_ =
                        (!leanh::lean_is_exclusive(v_userName_x3f_5817_)) as u8;
                    if v_isSharedCheck_5844_ == 0 {
                        v___x_5837_ = v_userName_x3f_5817_;
                        v_isShared_5838_ = v_isSharedCheck_5844_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5835_);
                        leanh::lean_dec(v_userName_x3f_5817_);
                        v___x_5837_ = leanh::lean_box(0);
                        v_isShared_5838_ = v_isSharedCheck_5844_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v_hyps_5822_ = leanh::lean_ctor_get(v_g_5816_, 0);
                leanh::lean_inc_ref(v_hyps_5822_);
                v_type_5823_ = leanh::lean_ctor_get(v_g_5816_, 1);
                leanh::lean_inc_ref(v_type_5823_);
                leanh::lean_dec_ref(v_g_5816_);
                v_sz_5824_ = lean_array_size(v_hyps_5822_);
                v___x_5825_ = 0usize;
                v___x_5826_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1(v_hyps_5822_, v_sz_5824_, v___x_5825_, v___y_5821_);
                leanh::lean_dec_ref(v_hyps_5822_);
                v___x_5827_ = l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_InteractiveGoalCore_pretty_addLine(v___x_5826_);
                v___x_5828_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5828_, 0, v_goalPrefix_5818_);
                v___x_5829_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_type_5823_);
                v___x_5830_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5830_, 0, v___x_5829_);
                v___x_5831_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5831_, 0, v_indent_5819_);
                leanh::lean_ctor_set(v___x_5831_, 1, v___x_5830_);
                v___x_5832_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5832_, 0, v___x_5828_);
                leanh::lean_ctor_set(v___x_5832_, 1, v___x_5831_);
                v___x_5833_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5833_, 0, v___x_5827_);
                leanh::lean_ctor_set(v___x_5833_, 1, v___x_5832_);
                return v___x_5833_;
            }
            2 => {
                v___x_5839_ = l_Lean_Widget_InteractiveGoalCore_pretty___closed__1;
                if v_isShared_5838_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5837_, 3);
                    v___x_5841_ = v___x_5837_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5843_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5843_, 0, v_val_5835_);
                    v___x_5841_ = v_reuseFailAlloc_5843_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5842_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5842_, 0, v___x_5839_);
                leanh::lean_ctor_set(v___x_5842_, 1, v___x_5841_);
                v___y_5821_ = v___x_5842_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_InteractiveGoal_pretty(
    mut v_g_5845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toInteractiveGoalCore_5846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_x3f_5847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_goalPrefix_5848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toInteractiveGoalCore_5846_ = leanh::lean_ctor_get(v_g_5845_, 0);
    leanh::lean_inc_ref(v_toInteractiveGoalCore_5846_);
    v_userName_x3f_5847_ = leanh::lean_ctor_get(v_g_5845_, 1);
    leanh::lean_inc(v_userName_x3f_5847_);
    v_goalPrefix_5848_ = leanh::lean_ctor_get(v_g_5845_, 2);
    leanh::lean_inc_ref(v_goalPrefix_5848_);
    leanh::lean_dec_ref(v_g_5845_);
    v___x_5849_ = l_Lean_Widget_InteractiveGoalCore_pretty(
        v_toInteractiveGoalCore_5846_,
        v_userName_x3f_5847_,
        v_goalPrefix_5848_,
    );
    return v___x_5849_;
}
pub unsafe fn l_Lean_Widget_InteractiveTermGoal_pretty(
    mut v_g_5851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toInteractiveGoalCore_5852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toInteractiveGoalCore_5852_ = leanh::lean_ctor_get(v_g_5851_, 0);
    leanh::lean_inc_ref(v_toInteractiveGoalCore_5852_);
    leanh::lean_dec_ref(v_g_5851_);
    v___x_5853_ = leanh::lean_box(0);
    v___x_5854_ = l_Lean_Widget_InteractiveTermGoal_pretty___closed__0;
    v___x_5855_ = l_Lean_Widget_InteractiveGoalCore_pretty(
        v_toInteractiveGoalCore_5852_,
        v___x_5853_,
        v___x_5854_,
    );
    return v___x_5855_;
}
pub unsafe fn l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10_(
    mut v_json_5857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5863_: u8 = 0;
    let mut v___x_5865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5858_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10_;
                v___x_5859_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_5857_, v___x_5858_);
                v_a_5860_ = leanh::lean_ctor_get(v___x_5859_, 0);
                v_isSharedCheck_5867_ = (!leanh::lean_is_exclusive(v___x_5859_)) as u8;
                if v_isSharedCheck_5867_ == 0 {
                    v___x_5862_ = v___x_5859_;
                    v_isShared_5863_ = v_isSharedCheck_5867_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5860_);
                    leanh::lean_dec(v___x_5859_);
                    v___x_5862_ = leanh::lean_box(0);
                    v_isShared_5863_ = v_isSharedCheck_5867_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_5863_ == 0 {
                    v___x_5865_ = v___x_5862_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5866_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5866_, 0, v_a_5860_);
                    v___x_5865_ = v_reuseFailAlloc_5866_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_28_(
    mut v_x_5870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5871_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10_;
    v___x_5872_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5872_, 0, v___x_5871_);
    leanh::lean_ctor_set(v___x_5872_, 1, v_x_5870_);
    v___x_5873_ = leanh::lean_box(0);
    v___x_5874_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5874_, 0, v___x_5872_);
    leanh::lean_ctor_set(v___x_5874_, 1, v___x_5873_);
    v___x_5875_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5875_, 0, v___x_5874_);
    leanh::lean_ctor_set(v___x_5875_, 1, v___x_5873_);
    v___x_5876_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47_;
    v___x_5877_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__1(v___x_5875_, v___x_5876_);
    v___x_5878_ = l_Lean_Json_mkObj(v___x_5877_);
    leanh::lean_dec(v___x_5877_);
    return v___x_5878_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoals_enc_00___x40_Lean_Widget_InteractiveGoal_1490754142____hygCtx___hyg_1__spec__0(
    mut v_sz_5881_: usize,
    mut v_i_5882_: usize,
    mut v_bs_5883_: *mut leanh::LeanObject,
    mut v___y_5884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5885_: u8 = 0;
    let mut v___x_5886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: usize = 0;
    let mut v___x_5894_: usize = 0;
    let mut v___x_5895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5885_ = lean_usize_dec_lt(v_i_5882_, v_sz_5881_);
                if v___x_5885_ == 0 {
                    v___x_5886_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5886_, 0, v_bs_5883_);
                    leanh::lean_ctor_set(v___x_5886_, 1, v___y_5884_);
                    return v___x_5886_;
                } else {
                    v_v_5887_ = lean_array_uget_borrowed(v_bs_5883_, v_i_5882_);
                    leanh::lean_inc(v_v_5887_);
                    v___x_5888_ = l_Lean_Widget_instRpcEncodableInteractiveGoal_enc_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1_(v_v_5887_, v___y_5884_);
                    v_fst_5889_ = leanh::lean_ctor_get(v___x_5888_, 0);
                    leanh::lean_inc(v_fst_5889_);
                    v_snd_5890_ = leanh::lean_ctor_get(v___x_5888_, 1);
                    leanh::lean_inc(v_snd_5890_);
                    leanh::lean_dec_ref(v___x_5888_);
                    v___x_5891_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5892_ = lean_array_uset(v_bs_5883_, v_i_5882_, v___x_5891_);
                    v___x_5893_ = 1usize;
                    v___x_5894_ = lean_usize_add(v_i_5882_, v___x_5893_);
                    v___x_5895_ = lean_array_uset(v_bs_x27_5892_, v_i_5882_, v_fst_5889_);
                    v_i_5882_ = v___x_5894_;
                    v_bs_5883_ = v___x_5895_;
                    v___y_5884_ = v_snd_5890_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoals_enc_00___x40_Lean_Widget_InteractiveGoal_1490754142____hygCtx___hyg_1__spec__0___boxed(
    mut v_sz_5897_: *mut leanh::LeanObject,
    mut v_i_5898_: *mut leanh::LeanObject,
    mut v_bs_5899_: *mut leanh::LeanObject,
    mut v___y_5900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5901_: usize = 0;
    let mut v_i_boxed_5902_: usize = 0;
    let mut v_res_5903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5901_ = leanh::lean_unbox_usize(v_sz_5897_);
    leanh::lean_dec(v_sz_5897_);
    v_i_boxed_5902_ = leanh::lean_unbox_usize(v_i_5898_);
    leanh::lean_dec(v_i_5898_);
    v_res_5903_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoals_enc_00___x40_Lean_Widget_InteractiveGoal_1490754142____hygCtx___hyg_1__spec__0(v_sz_boxed_5901_, v_i_boxed_5902_, v_bs_5899_, v___y_5900_);
    return v_res_5903_;
}
pub unsafe fn l_Lean_Widget_instRpcEncodableInteractiveGoals_enc_00___x40_Lean_Widget_InteractiveGoal_1490754142____hygCtx___hyg_1_(
    mut v_a_5904_: *mut leanh::LeanObject,
    mut v_a_5905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_5906_: usize = 0;
    let mut v___x_5907_: usize = 0;
    let mut v___x_5908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5913_: u8 = 0;
    let mut v___x_5914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5919_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_5906_ = lean_array_size(v_a_5904_);
                v___x_5907_ = 0usize;
                v___x_5908_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoals_enc_00___x40_Lean_Widget_InteractiveGoal_1490754142____hygCtx___hyg_1__spec__0(v_sz_5906_, v___x_5907_, v_a_5904_, v_a_5905_);
                v_fst_5909_ = leanh::lean_ctor_get(v___x_5908_, 0);
                v_snd_5910_ = leanh::lean_ctor_get(v___x_5908_, 1);
                v_isSharedCheck_5919_ = (!leanh::lean_is_exclusive(v___x_5908_)) as u8;
                if v_isSharedCheck_5919_ == 0 {
                    v___x_5912_ = v___x_5908_;
                    v_isShared_5913_ = v_isSharedCheck_5919_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_5910_);
                    leanh::lean_inc(v_fst_5909_);
                    leanh::lean_dec(v___x_5908_);
                    v___x_5912_ = leanh::lean_box(0);
                    v_isShared_5913_ = v_isSharedCheck_5919_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5914_ = l_Array_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3(v_fst_5909_);
                v___x_5915_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_28_(v___x_5914_);
                if v_isShared_5913_ == 0 {
                    leanh::lean_ctor_set(v___x_5912_, 0, v___x_5915_);
                    v___x_5917_ = v___x_5912_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5918_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5918_, 0, v___x_5915_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5918_, 1, v_snd_5910_);
                    v___x_5917_ = v_reuseFailAlloc_5918_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5917_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoals_dec_00___x40_Lean_Widget_InteractiveGoal_1490754142____hygCtx___hyg_1__spec__0(
    mut v_sz_5920_: usize,
    mut v_i_5921_: usize,
    mut v_bs_5922_: *mut leanh::LeanObject,
    mut v___y_5923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5924_: u8 = 0;
    let mut v___x_5925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5931_: u8 = 0;
    let mut v___x_5933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5935_: u8 = 0;
    let mut v_a_5936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: usize = 0;
    let mut v___x_5940_: usize = 0;
    let mut v___x_5941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5924_ = lean_usize_dec_lt(v_i_5921_, v_sz_5920_);
                if v___x_5924_ == 0 {
                    v___x_5925_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5925_, 0, v_bs_5922_);
                    return v___x_5925_;
                } else {
                    v_v_5926_ = lean_array_uget_borrowed(v_bs_5922_, v_i_5921_);
                    leanh::lean_inc(v_v_5926_);
                    v___x_5927_ = l_Lean_Widget_instRpcEncodableInteractiveGoal_dec_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1_(v_v_5926_, v___y_5923_);
                    if leanh::lean_obj_tag(v___x_5927_) == 0 {
                        leanh::lean_dec_ref(v_bs_5922_);
                        v_a_5928_ = leanh::lean_ctor_get(v___x_5927_, 0);
                        v_isSharedCheck_5935_ =
                            (!leanh::lean_is_exclusive(v___x_5927_)) as u8;
                        if v_isSharedCheck_5935_ == 0 {
                            v___x_5930_ = v___x_5927_;
                            v_isShared_5931_ = v_isSharedCheck_5935_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5928_);
                            leanh::lean_dec(v___x_5927_);
                            v___x_5930_ = leanh::lean_box(0);
                            v_isShared_5931_ = v_isSharedCheck_5935_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5936_ = leanh::lean_ctor_get(v___x_5927_, 0);
                        leanh::lean_inc(v_a_5936_);
                        leanh::lean_dec_ref_known(v___x_5927_, 1);
                        v___x_5937_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_5938_ = lean_array_uset(v_bs_5922_, v_i_5921_, v___x_5937_);
                        v___x_5939_ = 1usize;
                        v___x_5940_ = lean_usize_add(v_i_5921_, v___x_5939_);
                        v___x_5941_ = lean_array_uset(v_bs_x27_5938_, v_i_5921_, v_a_5936_);
                        v_i_5921_ = v___x_5940_;
                        v_bs_5922_ = v___x_5941_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5931_ == 0 {
                    v___x_5933_ = v___x_5930_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5934_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5934_, 0, v_a_5928_);
                    v___x_5933_ = v_reuseFailAlloc_5934_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5933_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoals_dec_00___x40_Lean_Widget_InteractiveGoal_1490754142____hygCtx___hyg_1__spec__0___boxed(
    mut v_sz_5943_: *mut leanh::LeanObject,
    mut v_i_5944_: *mut leanh::LeanObject,
    mut v_bs_5945_: *mut leanh::LeanObject,
    mut v___y_5946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5947_: usize = 0;
    let mut v_i_boxed_5948_: usize = 0;
    let mut v_res_5949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5947_ = leanh::lean_unbox_usize(v_sz_5943_);
    leanh::lean_dec(v_sz_5943_);
    v_i_boxed_5948_ = leanh::lean_unbox_usize(v_i_5944_);
    leanh::lean_dec(v_i_5944_);
    v_res_5949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoals_dec_00___x40_Lean_Widget_InteractiveGoal_1490754142____hygCtx___hyg_1__spec__0(v_sz_boxed_5947_, v_i_boxed_5948_, v_bs_5945_, v___y_5946_);
    leanh::lean_dec_ref(v___y_5946_);
    return v_res_5949_;
}
pub unsafe fn l_Lean_Widget_instRpcEncodableInteractiveGoals_dec_00___x40_Lean_Widget_InteractiveGoal_1490754142____hygCtx___hyg_1_(
    mut v_j_5950_: *mut leanh::LeanObject,
    mut v_a_5951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5956_: u8 = 0;
    let mut v___x_5958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5960_: u8 = 0;
    let mut v_a_5961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5966_: u8 = 0;
    let mut v___x_5968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5970_: u8 = 0;
    let mut v_a_5971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5972_: usize = 0;
    let mut v___x_5973_: usize = 0;
    let mut v___x_5974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5978_: u8 = 0;
    let mut v___x_5980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5982_: u8 = 0;
    let mut v_a_5983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5986_: u8 = 0;
    let mut v___x_5988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5990_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5952_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10_(v_j_5950_);
                if leanh::lean_obj_tag(v___x_5952_) == 0 {
                    v_a_5953_ = leanh::lean_ctor_get(v___x_5952_, 0);
                    v_isSharedCheck_5960_ = (!leanh::lean_is_exclusive(v___x_5952_)) as u8;
                    if v_isSharedCheck_5960_ == 0 {
                        v___x_5955_ = v___x_5952_;
                        v_isShared_5956_ = v_isSharedCheck_5960_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5953_);
                        leanh::lean_dec(v___x_5952_);
                        v___x_5955_ = leanh::lean_box(0);
                        v_isShared_5956_ = v_isSharedCheck_5960_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5961_ = leanh::lean_ctor_get(v___x_5952_, 0);
                    leanh::lean_inc(v_a_5961_);
                    leanh::lean_dec_ref_known(v___x_5952_, 1);
                    v___x_5962_ = l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0(v_a_5961_);
                    if leanh::lean_obj_tag(v___x_5962_) == 0 {
                        v_a_5963_ = leanh::lean_ctor_get(v___x_5962_, 0);
                        v_isSharedCheck_5970_ =
                            (!leanh::lean_is_exclusive(v___x_5962_)) as u8;
                        if v_isSharedCheck_5970_ == 0 {
                            v___x_5965_ = v___x_5962_;
                            v_isShared_5966_ = v_isSharedCheck_5970_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5963_);
                            leanh::lean_dec(v___x_5962_);
                            v___x_5965_ = leanh::lean_box(0);
                            v_isShared_5966_ = v_isSharedCheck_5970_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5971_ = leanh::lean_ctor_get(v___x_5962_, 0);
                        leanh::lean_inc(v_a_5971_);
                        leanh::lean_dec_ref_known(v___x_5962_, 1);
                        v_sz_5972_ = lean_array_size(v_a_5971_);
                        v___x_5973_ = 0usize;
                        v___x_5974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoals_dec_00___x40_Lean_Widget_InteractiveGoal_1490754142____hygCtx___hyg_1__spec__0(v_sz_5972_, v___x_5973_, v_a_5971_, v_a_5951_);
                        if leanh::lean_obj_tag(v___x_5974_) == 0 {
                            v_a_5975_ = leanh::lean_ctor_get(v___x_5974_, 0);
                            v_isSharedCheck_5982_ =
                                (!leanh::lean_is_exclusive(v___x_5974_)) as u8;
                            if v_isSharedCheck_5982_ == 0 {
                                v___x_5977_ = v___x_5974_;
                                v_isShared_5978_ = v_isSharedCheck_5982_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5975_);
                                leanh::lean_dec(v___x_5974_);
                                v___x_5977_ = leanh::lean_box(0);
                                v_isShared_5978_ = v_isSharedCheck_5982_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v_a_5983_ = leanh::lean_ctor_get(v___x_5974_, 0);
                            v_isSharedCheck_5990_ =
                                (!leanh::lean_is_exclusive(v___x_5974_)) as u8;
                            if v_isSharedCheck_5990_ == 0 {
                                v___x_5985_ = v___x_5974_;
                                v_isShared_5986_ = v_isSharedCheck_5990_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5983_);
                                leanh::lean_dec(v___x_5974_);
                                v___x_5985_ = leanh::lean_box(0);
                                v_isShared_5986_ = v_isSharedCheck_5990_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5956_ == 0 {
                    v___x_5958_ = v___x_5955_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5959_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5959_, 0, v_a_5953_);
                    v___x_5958_ = v_reuseFailAlloc_5959_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5958_;
            }
            3 => {
                if v_isShared_5966_ == 0 {
                    v___x_5968_ = v___x_5965_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5969_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5969_, 0, v_a_5963_);
                    v___x_5968_ = v_reuseFailAlloc_5969_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5968_;
            }
            5 => {
                if v_isShared_5978_ == 0 {
                    v___x_5980_ = v___x_5977_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5981_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5981_, 0, v_a_5975_);
                    v___x_5980_ = v_reuseFailAlloc_5981_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5980_;
            }
            7 => {
                if v_isShared_5986_ == 0 {
                    v___x_5988_ = v___x_5985_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5989_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5989_, 0, v_a_5983_);
                    v___x_5988_ = v_reuseFailAlloc_5989_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5988_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_instRpcEncodableInteractiveGoals_dec_00___x40_Lean_Widget_InteractiveGoal_1490754142____hygCtx___hyg_1____boxed(
    mut v_j_5991_: *mut leanh::LeanObject,
    mut v_a_5992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5993_ = l_Lean_Widget_instRpcEncodableInteractiveGoals_dec_00___x40_Lean_Widget_InteractiveGoal_1490754142____hygCtx___hyg_1_(v_j_5991_, v_a_5992_);
    leanh::lean_dec_ref(v_a_5992_);
    return v_res_5993_;
}
pub unsafe fn l_Lean_Widget_InteractiveGoals_append(
    mut v_l_6000_: *mut leanh::LeanObject,
    mut v_r_6001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6002_ = l_Array_append___redArg(v_l_6000_, v_r_6001_);
    return v___x_6002_;
}
pub unsafe fn l_Lean_Widget_InteractiveGoals_append___boxed(
    mut v_l_6003_: *mut leanh::LeanObject,
    mut v_r_6004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6005_ = l_Lean_Widget_InteractiveGoals_append(v_l_6003_, v_r_6004_);
    leanh::lean_dec_ref(v_r_6004_);
    return v_res_6005_;
}
pub unsafe fn l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged(
    mut v_tactic_6014_: u8,
    mut v_value_6015_: *mut leanh::LeanObject,
    mut v_a_6016_: *mut leanh::LeanObject,
    mut v_a_6017_: *mut leanh::LeanObject,
    mut v_a_6018_: *mut leanh::LeanObject,
    mut v_a_6019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: u8 = 0;
    let mut v___x_6029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6036_: u8 = 0;
    let mut v___x_6038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6040_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6021_ = l_Lean_Meta_ppGoal_shouldShowLetValue___redArg(
                    v_tactic_6014_,
                    v_value_6015_,
                    v_a_6018_,
                );
                if leanh::lean_obj_tag(v___x_6021_) == 0 {
                    v_a_6022_ = leanh::lean_ctor_get(v___x_6021_, 0);
                    leanh::lean_inc(v_a_6022_);
                    leanh::lean_dec_ref_known(v___x_6021_, 1);
                    v___x_6028_ = (leanh::lean_unbox(v_a_6022_) as u8);
                    leanh::lean_dec(v_a_6022_);
                    if v___x_6028_ == 0 {
                        if v_tactic_6014_ == 0 {
                            v___x_6029_ = l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged___closed__0;
                            v___y_6024_ = v___x_6029_;
                            state = 1;
                            continue;
                        } else {
                            v___x_6030_ = l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged___closed__1;
                            v___y_6024_ = v___x_6030_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_6031_ = l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged___closed__2;
                        v___x_6032_ = l_Lean_Widget_ppExprTagged(
                            v_value_6015_,
                            v___x_6031_,
                            v_a_6016_,
                            v_a_6017_,
                            v_a_6018_,
                            v_a_6019_,
                        );
                        return v___x_6032_;
                    }
                } else {
                    leanh::lean_dec_ref(v_value_6015_);
                    v_a_6033_ = leanh::lean_ctor_get(v___x_6021_, 0);
                    v_isSharedCheck_6040_ = (!leanh::lean_is_exclusive(v___x_6021_)) as u8;
                    if v_isSharedCheck_6040_ == 0 {
                        v___x_6035_ = v___x_6021_;
                        v_isShared_6036_ = v_isSharedCheck_6040_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6033_);
                        leanh::lean_dec(v___x_6021_);
                        v___x_6035_ = leanh::lean_box(0);
                        v_isShared_6036_ = v_isSharedCheck_6040_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_6024_);
                v___x_6025_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6025_, 0, v___y_6024_);
                v___x_6026_ = leanh::lean_alloc_closure(
                    l_Lean_PrettyPrinter_Delaborator_omission___boxed as *mut core::ffi::c_void,
                    8,
                    1,
                );
                leanh::lean_closure_set(v___x_6026_, 0, v___x_6025_);
                v___x_6027_ = l_Lean_Widget_ppExprTagged(
                    v_value_6015_,
                    v___x_6026_,
                    v_a_6016_,
                    v_a_6017_,
                    v_a_6018_,
                    v_a_6019_,
                );
                return v___x_6027_;
            }
            2 => {
                if v_isShared_6036_ == 0 {
                    v___x_6038_ = v___x_6035_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6039_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6039_, 0, v_a_6033_);
                    v___x_6038_ = v_reuseFailAlloc_6039_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6038_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged___boxed(
    mut v_tactic_6041_: *mut leanh::LeanObject,
    mut v_value_6042_: *mut leanh::LeanObject,
    mut v_a_6043_: *mut leanh::LeanObject,
    mut v_a_6044_: *mut leanh::LeanObject,
    mut v_a_6045_: *mut leanh::LeanObject,
    mut v_a_6046_: *mut leanh::LeanObject,
    mut v_a_6047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tactic_boxed_6048_: u8 = 0;
    let mut v_res_6049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_tactic_boxed_6048_ = (leanh::lean_unbox(v_tactic_6041_) as u8);
    v_res_6049_ = l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged(v_tactic_boxed_6048_, v_value_6042_, v_a_6043_, v_a_6044_, v_a_6045_, v_a_6046_);
    leanh::lean_dec(v_a_6046_);
    leanh::lean_dec_ref(v_a_6045_);
    leanh::lean_dec(v_a_6044_);
    leanh::lean_dec_ref(v_a_6043_);
    return v_res_6049_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(
    mut v_e_6050_: *mut leanh::LeanObject,
    mut v___y_6051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6053_: u8 = 0;
    let mut v___x_6054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6067_: u8 = 0;
    let mut v___x_6069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6073_: u8 = 0;
    let mut v_unused_6074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6053_ = l_Lean_Expr_hasMVar(v_e_6050_);
                if v___x_6053_ == 0 {
                    v___x_6054_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6054_, 0, v_e_6050_);
                    return v___x_6054_;
                } else {
                    v___x_6055_ = lean_st_ref_get(v___y_6051_);
                    v_mctx_6056_ = leanh::lean_ctor_get(v___x_6055_, 0);
                    leanh::lean_inc_ref(v_mctx_6056_);
                    leanh::lean_dec(v___x_6055_);
                    v___x_6057_ = l_Lean_instantiateMVarsCore(v_mctx_6056_, v_e_6050_);
                    v_fst_6058_ = leanh::lean_ctor_get(v___x_6057_, 0);
                    leanh::lean_inc(v_fst_6058_);
                    v_snd_6059_ = leanh::lean_ctor_get(v___x_6057_, 1);
                    leanh::lean_inc(v_snd_6059_);
                    leanh::lean_dec_ref(v___x_6057_);
                    v___x_6060_ = lean_st_ref_take(v___y_6051_);
                    v_cache_6061_ = leanh::lean_ctor_get(v___x_6060_, 1);
                    v_zetaDeltaFVarIds_6062_ = leanh::lean_ctor_get(v___x_6060_, 2);
                    v_postponed_6063_ = leanh::lean_ctor_get(v___x_6060_, 3);
                    v_diag_6064_ = leanh::lean_ctor_get(v___x_6060_, 4);
                    v_isSharedCheck_6073_ = (!leanh::lean_is_exclusive(v___x_6060_)) as u8;
                    if v_isSharedCheck_6073_ == 0 {
                        v_unused_6074_ = leanh::lean_ctor_get(v___x_6060_, 0);
                        leanh::lean_dec(v_unused_6074_);
                        v___x_6066_ = v___x_6060_;
                        v_isShared_6067_ = v_isSharedCheck_6073_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_6064_);
                        leanh::lean_inc(v_postponed_6063_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_6062_);
                        leanh::lean_inc(v_cache_6061_);
                        leanh::lean_dec(v___x_6060_);
                        v___x_6066_ = leanh::lean_box(0);
                        v_isShared_6067_ = v_isSharedCheck_6073_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6067_ == 0 {
                    leanh::lean_ctor_set(v___x_6066_, 0, v_snd_6059_);
                    v___x_6069_ = v___x_6066_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6072_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6072_, 0, v_snd_6059_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6072_, 1, v_cache_6061_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6072_,
                        2,
                        v_zetaDeltaFVarIds_6062_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_6072_, 3, v_postponed_6063_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6072_, 4, v_diag_6064_);
                    v___x_6069_ = v_reuseFailAlloc_6072_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6070_ = lean_st_ref_set(v___y_6051_, v___x_6069_);
                v___x_6071_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6071_, 0, v_fst_6058_);
                return v___x_6071_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg___boxed(
    mut v_e_6075_: *mut leanh::LeanObject,
    mut v___y_6076_: *mut leanh::LeanObject,
    mut v___y_6077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6078_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_e_6075_, v___y_6076_);
    leanh::lean_dec(v___y_6076_);
    return v_res_6078_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2(
    mut v_e_6079_: *mut leanh::LeanObject,
    mut v___y_6080_: *mut leanh::LeanObject,
    mut v___y_6081_: *mut leanh::LeanObject,
    mut v___y_6082_: *mut leanh::LeanObject,
    mut v___y_6083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6085_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_e_6079_, v___y_6081_);
    return v___x_6085_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___boxed(
    mut v_e_6086_: *mut leanh::LeanObject,
    mut v___y_6087_: *mut leanh::LeanObject,
    mut v___y_6088_: *mut leanh::LeanObject,
    mut v___y_6089_: *mut leanh::LeanObject,
    mut v___y_6090_: *mut leanh::LeanObject,
    mut v___y_6091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6092_ =
        l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2(
            v_e_6086_,
            v___y_6087_,
            v___y_6088_,
            v___y_6089_,
            v___y_6090_,
        );
    leanh::lean_dec(v___y_6090_);
    leanh::lean_dec_ref(v___y_6089_);
    leanh::lean_dec(v___y_6088_);
    leanh::lean_dec_ref(v___y_6087_);
    return v_res_6092_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__0(
    mut v_sz_6093_: usize,
    mut v_i_6094_: usize,
    mut v_bs_6095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6096_: u8 = 0;
    let mut v_v_6097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: usize = 0;
    let mut v___x_6102_: usize = 0;
    let mut v___x_6103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6096_ = lean_usize_dec_lt(v_i_6094_, v_sz_6093_);
                if v___x_6096_ == 0 {
                    return v_bs_6095_;
                } else {
                    v_v_6097_ = lean_array_uget_borrowed(v_bs_6095_, v_i_6094_);
                    v_snd_6098_ = leanh::lean_ctor_get(v_v_6097_, 1);
                    leanh::lean_inc(v_snd_6098_);
                    v___x_6099_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_6100_ = lean_array_uset(v_bs_6095_, v_i_6094_, v___x_6099_);
                    v___x_6101_ = 1usize;
                    v___x_6102_ = lean_usize_add(v_i_6094_, v___x_6101_);
                    v___x_6103_ = lean_array_uset(v_bs_x27_6100_, v_i_6094_, v_snd_6098_);
                    v_i_6094_ = v___x_6102_;
                    v_bs_6095_ = v___x_6103_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__0___boxed(
    mut v_sz_6105_: *mut leanh::LeanObject,
    mut v_i_6106_: *mut leanh::LeanObject,
    mut v_bs_6107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6108_: usize = 0;
    let mut v_i_boxed_6109_: usize = 0;
    let mut v_res_6110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6108_ = leanh::lean_unbox_usize(v_sz_6105_);
    leanh::lean_dec(v_sz_6105_);
    v_i_boxed_6109_ = leanh::lean_unbox_usize(v_i_6106_);
    leanh::lean_dec(v_i_6106_);
    v_res_6110_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__0(v_sz_boxed_6108_, v_i_boxed_6109_, v_bs_6107_);
    return v_res_6110_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__1(
    mut v_sz_6111_: usize,
    mut v_i_6112_: usize,
    mut v_bs_6113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6114_: u8 = 0;
    let mut v_v_6115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6119_: usize = 0;
    let mut v___x_6120_: usize = 0;
    let mut v___x_6121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6114_ = lean_usize_dec_lt(v_i_6112_, v_sz_6111_);
                if v___x_6114_ == 0 {
                    return v_bs_6113_;
                } else {
                    v_v_6115_ = lean_array_uget_borrowed(v_bs_6113_, v_i_6112_);
                    v_fst_6116_ = leanh::lean_ctor_get(v_v_6115_, 0);
                    leanh::lean_inc(v_fst_6116_);
                    v___x_6117_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_6118_ = lean_array_uset(v_bs_6113_, v_i_6112_, v___x_6117_);
                    v___x_6119_ = 1usize;
                    v___x_6120_ = lean_usize_add(v_i_6112_, v___x_6119_);
                    v___x_6121_ = lean_array_uset(v_bs_x27_6118_, v_i_6112_, v_fst_6116_);
                    v_i_6112_ = v___x_6120_;
                    v_bs_6113_ = v___x_6121_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__1___boxed(
    mut v_sz_6123_: *mut leanh::LeanObject,
    mut v_i_6124_: *mut leanh::LeanObject,
    mut v_bs_6125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6126_: usize = 0;
    let mut v_i_boxed_6127_: usize = 0;
    let mut v_res_6128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6126_ = leanh::lean_unbox_usize(v_sz_6123_);
    leanh::lean_dec(v_sz_6123_);
    v_i_boxed_6127_ = leanh::lean_unbox_usize(v_i_6124_);
    leanh::lean_dec(v_i_6124_);
    v_res_6128_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__1(v_sz_boxed_6126_, v_i_boxed_6127_, v_bs_6125_);
    return v_res_6128_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__3_spec__3(
    mut v_msgData_6129_: *mut leanh::LeanObject,
    mut v___y_6130_: *mut leanh::LeanObject,
    mut v___y_6131_: *mut leanh::LeanObject,
    mut v___y_6132_: *mut leanh::LeanObject,
    mut v___y_6133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_6139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6135_ = lean_st_ref_get(v___y_6133_);
    v_env_6136_ = leanh::lean_ctor_get(v___x_6135_, 0);
    leanh::lean_inc_ref(v_env_6136_);
    leanh::lean_dec(v___x_6135_);
    v___x_6137_ = lean_st_ref_get(v___y_6131_);
    v_mctx_6138_ = leanh::lean_ctor_get(v___x_6137_, 0);
    leanh::lean_inc_ref(v_mctx_6138_);
    leanh::lean_dec(v___x_6137_);
    v_lctx_6139_ = leanh::lean_ctor_get(v___y_6130_, 2);
    v_options_6140_ = leanh::lean_ctor_get(v___y_6132_, 2);
    leanh::lean_inc_ref(v_options_6140_);
    leanh::lean_inc_ref(v_lctx_6139_);
    v___x_6141_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_6141_, 0, v_env_6136_);
    leanh::lean_ctor_set(v___x_6141_, 1, v_mctx_6138_);
    leanh::lean_ctor_set(v___x_6141_, 2, v_lctx_6139_);
    leanh::lean_ctor_set(v___x_6141_, 3, v_options_6140_);
    v___x_6142_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6142_, 0, v___x_6141_);
    leanh::lean_ctor_set(v___x_6142_, 1, v_msgData_6129_);
    v___x_6143_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6143_, 0, v___x_6142_);
    return v___x_6143_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__3_spec__3___boxed(
    mut v_msgData_6144_: *mut leanh::LeanObject,
    mut v___y_6145_: *mut leanh::LeanObject,
    mut v___y_6146_: *mut leanh::LeanObject,
    mut v___y_6147_: *mut leanh::LeanObject,
    mut v___y_6148_: *mut leanh::LeanObject,
    mut v___y_6149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6150_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__3_spec__3(v_msgData_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_);
    leanh::lean_dec(v___y_6148_);
    leanh::lean_dec_ref(v___y_6147_);
    leanh::lean_dec(v___y_6146_);
    leanh::lean_dec_ref(v___y_6145_);
    return v_res_6150_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__3___redArg(
    mut v_msg_6151_: *mut leanh::LeanObject,
    mut v___y_6152_: *mut leanh::LeanObject,
    mut v___y_6153_: *mut leanh::LeanObject,
    mut v___y_6154_: *mut leanh::LeanObject,
    mut v___y_6155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_6157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6162_: u8 = 0;
    let mut v___x_6163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6167_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_6157_ = leanh::lean_ctor_get(v___y_6154_, 5);
                v___x_6158_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__3_spec__3(v_msg_6151_, v___y_6152_, v___y_6153_, v___y_6154_, v___y_6155_);
                v_a_6159_ = leanh::lean_ctor_get(v___x_6158_, 0);
                v_isSharedCheck_6167_ = (!leanh::lean_is_exclusive(v___x_6158_)) as u8;
                if v_isSharedCheck_6167_ == 0 {
                    v___x_6161_ = v___x_6158_;
                    v_isShared_6162_ = v_isSharedCheck_6167_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_6159_);
                    leanh::lean_dec(v___x_6158_);
                    v___x_6161_ = leanh::lean_box(0);
                    v_isShared_6162_ = v_isSharedCheck_6167_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_6157_);
                v___x_6163_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6163_, 0, v_ref_6157_);
                leanh::lean_ctor_set(v___x_6163_, 1, v_a_6159_);
                if v_isShared_6162_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6161_, 1);
                    leanh::lean_ctor_set(v___x_6161_, 0, v___x_6163_);
                    v___x_6165_ = v___x_6161_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6166_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6166_, 0, v___x_6163_);
                    v___x_6165_ = v_reuseFailAlloc_6166_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6165_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__3___redArg___boxed(
    mut v_msg_6168_: *mut leanh::LeanObject,
    mut v___y_6169_: *mut leanh::LeanObject,
    mut v___y_6170_: *mut leanh::LeanObject,
    mut v___y_6171_: *mut leanh::LeanObject,
    mut v___y_6172_: *mut leanh::LeanObject,
    mut v___y_6173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6174_ =
        l_Lean_throwError___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__3___redArg(
            v_msg_6168_,
            v___y_6169_,
            v___y_6170_,
            v___y_6171_,
            v___y_6172_,
        );
    leanh::lean_dec(v___y_6172_);
    leanh::lean_dec_ref(v___y_6171_);
    leanh::lean_dec(v___y_6170_);
    leanh::lean_dec_ref(v___y_6169_);
    return v_res_6174_;
}
pub unsafe fn _init_l_Lean_Widget_addInteractiveHypothesisBundle___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_6179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6179_ = l_Lean_Widget_addInteractiveHypothesisBundle___closed__1;
    v___x_6180_ = l_Lean_stringToMessageData(v___x_6179_);
    return v___x_6180_;
}
pub unsafe fn l_Lean_Widget_addInteractiveHypothesisBundle(
    mut v_hyps_6181_: *mut leanh::LeanObject,
    mut v_ids_6182_: *mut leanh::LeanObject,
    mut v_type_6183_: *mut leanh::LeanObject,
    mut v_value_x3f_6184_: *mut leanh::LeanObject,
    mut v_tactic_6185_: u8,
    mut v_a_6186_: *mut leanh::LeanObject,
    mut v_a_6187_: *mut leanh::LeanObject,
    mut v_a_6188_: *mut leanh::LeanObject,
    mut v_a_6189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6204_: u8 = 0;
    let mut v___y_6205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6210_: u8 = 0;
    let mut v___x_6211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: u8 = 0;
    let mut v___x_6228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: u8 = 0;
    let mut v___x_6231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6235_: u8 = 0;
    let mut v___x_6237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6239_: u8 = 0;
    let mut v___y_6241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6248_: usize = 0;
    let mut v___x_6249_: usize = 0;
    let mut v_fvarIds_6250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_names_6251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6256_: u8 = 0;
    let mut v___x_6257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6265_: u8 = 0;
    let mut v___x_6267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6269_: u8 = 0;
    let mut v_isSharedCheck_6270_: u8 = 0;
    let mut v_a_6271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6274_: u8 = 0;
    let mut v___x_6276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6278_: u8 = 0;
    let mut v___x_6279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: u8 = 0;
    let mut v___x_6282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6287_: u8 = 0;
    let mut v___x_6289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6291_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6279_ = lean_array_get_size(v_ids_6182_);
                v___x_6280_ = leanh::lean_unsigned_to_nat(0);
                v___x_6281_ = lean_nat_dec_eq(v___x_6279_, v___x_6280_);
                if v___x_6281_ == 0 {
                    v___y_6241_ = v_a_6186_;
                    v___y_6242_ = v_a_6187_;
                    v___y_6243_ = v_a_6188_;
                    v___y_6244_ = v_a_6189_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec(v_value_x3f_6184_);
                    leanh::lean_dec_ref(v_type_6183_);
                    leanh::lean_dec_ref(v_ids_6182_);
                    leanh::lean_dec_ref(v_hyps_6181_);
                    v___x_6282_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Widget_addInteractiveHypothesisBundle___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Widget_addInteractiveHypothesisBundle___closed__2_once
                        ),
                        _init_l_Lean_Widget_addInteractiveHypothesisBundle___closed__2,
                    );
                    v___x_6283_ = l_Lean_throwError___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__3___redArg(v___x_6282_, v_a_6186_, v_a_6187_, v_a_6188_, v_a_6189_);
                    v_a_6284_ = leanh::lean_ctor_get(v___x_6283_, 0);
                    v_isSharedCheck_6291_ = (!leanh::lean_is_exclusive(v___x_6283_)) as u8;
                    if v_isSharedCheck_6291_ == 0 {
                        v___x_6286_ = v___x_6283_;
                        v_isShared_6287_ = v_isSharedCheck_6291_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6284_);
                        leanh::lean_dec(v___x_6283_);
                        v___x_6286_ = leanh::lean_box(0);
                        v_isShared_6287_ = v_isSharedCheck_6291_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6198_ = leanh::lean_box(0);
                leanh::lean_inc(v___y_6193_);
                v___x_6199_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                leanh::lean_ctor_set(v___x_6199_, 0, v___y_6195_);
                leanh::lean_ctor_set(v___x_6199_, 1, v___y_6194_);
                leanh::lean_ctor_set(v___x_6199_, 2, v___y_6192_);
                leanh::lean_ctor_set(v___x_6199_, 3, v___y_6196_);
                leanh::lean_ctor_set(v___x_6199_, 4, v___y_6193_);
                leanh::lean_ctor_set(v___x_6199_, 5, v___y_6197_);
                leanh::lean_ctor_set(v___x_6199_, 6, v___x_6198_);
                leanh::lean_ctor_set(v___x_6199_, 7, v___x_6198_);
                v___x_6200_ = lean_array_push(v_hyps_6181_, v___x_6199_);
                v___x_6201_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6201_, 0, v___x_6200_);
                return v___x_6201_;
            }
            2 => {
                v___x_6210_ = l_Lean_Expr_isSort(v___y_6208_);
                leanh::lean_dec_ref(v___y_6208_);
                if v___x_6210_ == 0 {
                    v___x_6211_ = leanh::lean_box(0);
                    v___y_6192_ = v___y_6203_;
                    v___y_6193_ = v___y_6209_;
                    v___y_6194_ = v___y_6205_;
                    v___y_6195_ = v___y_6206_;
                    v___y_6196_ = v___y_6207_;
                    v___y_6197_ = v___x_6211_;
                    state = 1;
                    continue;
                } else {
                    v___x_6212_ = leanh::lean_box((v___y_6204_) as usize);
                    v___x_6213_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6213_, 0, v___x_6212_);
                    v___y_6192_ = v___y_6203_;
                    v___y_6193_ = v___y_6209_;
                    v___y_6194_ = v___y_6205_;
                    v___y_6195_ = v___y_6206_;
                    v___y_6196_ = v___y_6207_;
                    v___y_6197_ = v___x_6213_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc_ref(v_type_6183_);
                v___x_6223_ = l_Lean_Meta_isClass_x3f(
                    v_type_6183_,
                    v___y_6218_,
                    v___y_6220_,
                    v___y_6221_,
                    v___y_6219_,
                );
                if leanh::lean_obj_tag(v___x_6223_) == 0 {
                    v_a_6224_ = leanh::lean_ctor_get(v___x_6223_, 0);
                    leanh::lean_inc(v_a_6224_);
                    leanh::lean_dec_ref_known(v___x_6223_, 1);
                    v___x_6225_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_6183_, v___y_6220_);
                    if leanh::lean_obj_tag(v_a_6224_) == 0 {
                        v_a_6226_ = leanh::lean_ctor_get(v___x_6225_, 0);
                        leanh::lean_inc(v_a_6226_);
                        leanh::lean_dec_ref(v___x_6225_);
                        v___x_6227_ = 1;
                        v___x_6228_ = leanh::lean_box(0);
                        v___y_6203_ = v___y_6215_;
                        v___y_6204_ = v___x_6227_;
                        v___y_6205_ = v___y_6216_;
                        v___y_6206_ = v___y_6217_;
                        v___y_6207_ = v_a_6222_;
                        v___y_6208_ = v_a_6226_;
                        v___y_6209_ = v___x_6228_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec_ref_known(v_a_6224_, 1);
                        v_a_6229_ = leanh::lean_ctor_get(v___x_6225_, 0);
                        leanh::lean_inc(v_a_6229_);
                        leanh::lean_dec_ref(v___x_6225_);
                        v___x_6230_ = 1;
                        v___x_6231_ = l_Lean_Widget_addInteractiveHypothesisBundle___closed__0;
                        v___y_6203_ = v___y_6215_;
                        v___y_6204_ = v___x_6230_;
                        v___y_6205_ = v___y_6216_;
                        v___y_6206_ = v___y_6217_;
                        v___y_6207_ = v_a_6222_;
                        v___y_6208_ = v_a_6229_;
                        v___y_6209_ = v___x_6231_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_6222_);
                    leanh::lean_dec_ref(v___y_6217_);
                    leanh::lean_dec_ref(v___y_6216_);
                    leanh::lean_dec_ref(v___y_6215_);
                    leanh::lean_dec_ref(v_type_6183_);
                    leanh::lean_dec_ref(v_hyps_6181_);
                    v_a_6232_ = leanh::lean_ctor_get(v___x_6223_, 0);
                    v_isSharedCheck_6239_ = (!leanh::lean_is_exclusive(v___x_6223_)) as u8;
                    if v_isSharedCheck_6239_ == 0 {
                        v___x_6234_ = v___x_6223_;
                        v_isShared_6235_ = v_isSharedCheck_6239_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6232_);
                        leanh::lean_dec(v___x_6223_);
                        v___x_6234_ = leanh::lean_box(0);
                        v_isShared_6235_ = v_isSharedCheck_6239_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_6235_ == 0 {
                    v___x_6237_ = v___x_6234_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6238_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6238_, 0, v_a_6232_);
                    v___x_6237_ = v_reuseFailAlloc_6238_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6237_;
            }
            6 => {
                v___x_6245_ = l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged___closed__2;
                leanh::lean_inc_ref(v_type_6183_);
                v___x_6246_ = l_Lean_Widget_ppExprTagged(
                    v_type_6183_,
                    v___x_6245_,
                    v___y_6241_,
                    v___y_6242_,
                    v___y_6243_,
                    v___y_6244_,
                );
                if leanh::lean_obj_tag(v___x_6246_) == 0 {
                    v_a_6247_ = leanh::lean_ctor_get(v___x_6246_, 0);
                    leanh::lean_inc(v_a_6247_);
                    leanh::lean_dec_ref_known(v___x_6246_, 1);
                    v_sz_6248_ = lean_array_size(v_ids_6182_);
                    v___x_6249_ = 0usize;
                    leanh::lean_inc_ref(v_ids_6182_);
                    v_fvarIds_6250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__0(v_sz_6248_, v___x_6249_, v_ids_6182_);
                    v_names_6251_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__1(v_sz_6248_, v___x_6249_, v_ids_6182_);
                    if leanh::lean_obj_tag(v_value_x3f_6184_) == 0 {
                        v___x_6252_ = leanh::lean_box(0);
                        v___y_6215_ = v_a_6247_;
                        v___y_6216_ = v_fvarIds_6250_;
                        v___y_6217_ = v_names_6251_;
                        v___y_6218_ = v___y_6241_;
                        v___y_6219_ = v___y_6244_;
                        v___y_6220_ = v___y_6242_;
                        v___y_6221_ = v___y_6243_;
                        v_a_6222_ = v___x_6252_;
                        state = 3;
                        continue;
                    } else {
                        v_val_6253_ = leanh::lean_ctor_get(v_value_x3f_6184_, 0);
                        v_isSharedCheck_6270_ =
                            (!leanh::lean_is_exclusive(v_value_x3f_6184_)) as u8;
                        if v_isSharedCheck_6270_ == 0 {
                            v___x_6255_ = v_value_x3f_6184_;
                            v_isShared_6256_ = v_isSharedCheck_6270_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_6253_);
                            leanh::lean_dec(v_value_x3f_6184_);
                            v___x_6255_ = leanh::lean_box(0);
                            v_isShared_6256_ = v_isSharedCheck_6270_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_value_x3f_6184_);
                    leanh::lean_dec_ref(v_type_6183_);
                    leanh::lean_dec_ref(v_ids_6182_);
                    leanh::lean_dec_ref(v_hyps_6181_);
                    v_a_6271_ = leanh::lean_ctor_get(v___x_6246_, 0);
                    v_isSharedCheck_6278_ = (!leanh::lean_is_exclusive(v___x_6246_)) as u8;
                    if v_isSharedCheck_6278_ == 0 {
                        v___x_6273_ = v___x_6246_;
                        v_isShared_6274_ = v_isSharedCheck_6278_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6271_);
                        leanh::lean_dec(v___x_6246_);
                        v___x_6273_ = leanh::lean_box(0);
                        v_isShared_6274_ = v_isSharedCheck_6278_;
                        state = 11;
                        continue;
                    }
                }
            }
            7 => {
                v___x_6257_ = l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged(v_tactic_6185_, v_val_6253_, v___y_6241_, v___y_6242_, v___y_6243_, v___y_6244_);
                if leanh::lean_obj_tag(v___x_6257_) == 0 {
                    v_a_6258_ = leanh::lean_ctor_get(v___x_6257_, 0);
                    leanh::lean_inc(v_a_6258_);
                    leanh::lean_dec_ref_known(v___x_6257_, 1);
                    if v_isShared_6256_ == 0 {
                        leanh::lean_ctor_set(v___x_6255_, 0, v_a_6258_);
                        v___x_6260_ = v___x_6255_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6261_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6261_, 0, v_a_6258_);
                        v___x_6260_ = v_reuseFailAlloc_6261_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6255_);
                    leanh::lean_dec_ref(v_names_6251_);
                    leanh::lean_dec_ref(v_fvarIds_6250_);
                    leanh::lean_dec(v_a_6247_);
                    leanh::lean_dec_ref(v_type_6183_);
                    leanh::lean_dec_ref(v_hyps_6181_);
                    v_a_6262_ = leanh::lean_ctor_get(v___x_6257_, 0);
                    v_isSharedCheck_6269_ = (!leanh::lean_is_exclusive(v___x_6257_)) as u8;
                    if v_isSharedCheck_6269_ == 0 {
                        v___x_6264_ = v___x_6257_;
                        v_isShared_6265_ = v_isSharedCheck_6269_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6262_);
                        leanh::lean_dec(v___x_6257_);
                        v___x_6264_ = leanh::lean_box(0);
                        v_isShared_6265_ = v_isSharedCheck_6269_;
                        state = 9;
                        continue;
                    }
                }
            }
            8 => {
                v___y_6215_ = v_a_6247_;
                v___y_6216_ = v_fvarIds_6250_;
                v___y_6217_ = v_names_6251_;
                v___y_6218_ = v___y_6241_;
                v___y_6219_ = v___y_6244_;
                v___y_6220_ = v___y_6242_;
                v___y_6221_ = v___y_6243_;
                v_a_6222_ = v___x_6260_;
                state = 3;
                continue;
            }
            9 => {
                if v_isShared_6265_ == 0 {
                    v___x_6267_ = v___x_6264_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6268_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6268_, 0, v_a_6262_);
                    v___x_6267_ = v_reuseFailAlloc_6268_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6267_;
            }
            11 => {
                if v_isShared_6274_ == 0 {
                    v___x_6276_ = v___x_6273_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6277_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6277_, 0, v_a_6271_);
                    v___x_6276_ = v_reuseFailAlloc_6277_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6276_;
            }
            13 => {
                if v_isShared_6287_ == 0 {
                    v___x_6289_ = v___x_6286_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6290_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6290_, 0, v_a_6284_);
                    v___x_6289_ = v_reuseFailAlloc_6290_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6289_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_addInteractiveHypothesisBundle___boxed(
    mut v_hyps_6292_: *mut leanh::LeanObject,
    mut v_ids_6293_: *mut leanh::LeanObject,
    mut v_type_6294_: *mut leanh::LeanObject,
    mut v_value_x3f_6295_: *mut leanh::LeanObject,
    mut v_tactic_6296_: *mut leanh::LeanObject,
    mut v_a_6297_: *mut leanh::LeanObject,
    mut v_a_6298_: *mut leanh::LeanObject,
    mut v_a_6299_: *mut leanh::LeanObject,
    mut v_a_6300_: *mut leanh::LeanObject,
    mut v_a_6301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tactic_boxed_6302_: u8 = 0;
    let mut v_res_6303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_tactic_boxed_6302_ = (leanh::lean_unbox(v_tactic_6296_) as u8);
    v_res_6303_ = l_Lean_Widget_addInteractiveHypothesisBundle(
        v_hyps_6292_,
        v_ids_6293_,
        v_type_6294_,
        v_value_x3f_6295_,
        v_tactic_boxed_6302_,
        v_a_6297_,
        v_a_6298_,
        v_a_6299_,
        v_a_6300_,
    );
    leanh::lean_dec(v_a_6300_);
    leanh::lean_dec_ref(v_a_6299_);
    leanh::lean_dec(v_a_6298_);
    leanh::lean_dec_ref(v_a_6297_);
    return v_res_6303_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__3(
    mut v_00_u03b1_6304_: *mut leanh::LeanObject,
    mut v_msg_6305_: *mut leanh::LeanObject,
    mut v___y_6306_: *mut leanh::LeanObject,
    mut v___y_6307_: *mut leanh::LeanObject,
    mut v___y_6308_: *mut leanh::LeanObject,
    mut v___y_6309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6311_ =
        l_Lean_throwError___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__3___redArg(
            v_msg_6305_,
            v___y_6306_,
            v___y_6307_,
            v___y_6308_,
            v___y_6309_,
        );
    return v___x_6311_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__3___boxed(
    mut v_00_u03b1_6312_: *mut leanh::LeanObject,
    mut v_msg_6313_: *mut leanh::LeanObject,
    mut v___y_6314_: *mut leanh::LeanObject,
    mut v___y_6315_: *mut leanh::LeanObject,
    mut v___y_6316_: *mut leanh::LeanObject,
    mut v___y_6317_: *mut leanh::LeanObject,
    mut v___y_6318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6319_ = l_Lean_throwError___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__3(
        v_00_u03b1_6312_,
        v_msg_6313_,
        v___y_6314_,
        v___y_6315_,
        v___y_6316_,
        v___y_6317_,
    );
    leanh::lean_dec(v___y_6317_);
    leanh::lean_dec_ref(v___y_6316_);
    leanh::lean_dec(v___y_6315_);
    leanh::lean_dec_ref(v___y_6314_);
    return v_res_6319_;
}
pub unsafe fn l_Lean_Widget_withGoalCtx___redArg___lam__0(
    mut v_val_6320_: *mut leanh::LeanObject,
    mut v_action_6321_: *mut leanh::LeanObject,
    mut v_inst_6322_: *mut leanh::LeanObject,
    mut v_inst_6323_: *mut leanh::LeanObject,
    mut v_____do__lift_6324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lctx_6325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_6326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lctx_6325_ = leanh::lean_ctor_get(v_val_6320_, 1);
    v_localInstances_6326_ = leanh::lean_ctor_get(v_val_6320_, 4);
    leanh::lean_inc_ref(v_localInstances_6326_);
    v___x_6327_ = leanh::lean_box(1);
    v___x_6328_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_6328_, 0, v_____do__lift_6324_);
    leanh::lean_ctor_set(v___x_6328_, 1, v___x_6327_);
    leanh::lean_ctor_set(v___x_6328_, 2, v___x_6327_);
    leanh::lean_inc_ref(v_lctx_6325_);
    v___x_6329_ = l_Lean_LocalContext_sanitizeNames(v_lctx_6325_, v___x_6328_);
    v_fst_6330_ = leanh::lean_ctor_get(v___x_6329_, 0);
    leanh::lean_inc_n(v_fst_6330_, 2);
    leanh::lean_dec_ref(v___x_6329_);
    v___x_6331_ = leanh::lean_apply_2(v_action_6321_, v_fst_6330_, v_val_6320_);
    v___x_6332_ = l_Lean_Meta_withLCtx___redArg(
        v_inst_6322_,
        v_inst_6323_,
        v_fst_6330_,
        v_localInstances_6326_,
        v___x_6331_,
    );
    return v___x_6332_;
}
pub unsafe fn _init_l_Lean_Widget_withGoalCtx___redArg___lam__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6334_ = l_Lean_Widget_withGoalCtx___redArg___lam__1___closed__0;
    v___x_6335_ = l_Lean_stringToMessageData(v___x_6334_);
    return v___x_6335_;
}
pub unsafe fn l_Lean_Widget_withGoalCtx___redArg___lam__1(
    mut v_goal_6336_: *mut leanh::LeanObject,
    mut v_action_6337_: *mut leanh::LeanObject,
    mut v_inst_6338_: *mut leanh::LeanObject,
    mut v_inst_6339_: *mut leanh::LeanObject,
    mut v_toBind_6340_: *mut leanh::LeanObject,
    mut v_inst_6341_: *mut leanh::LeanObject,
    mut v_inst_6342_: *mut leanh::LeanObject,
    mut v_mctx_6343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6344_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_6343_, v_goal_6336_);
    if leanh::lean_obj_tag(v___x_6344_) == 1 {
        let mut v_val_6345_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6346_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6347_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_6342_);
        leanh::lean_dec(v_goal_6336_);
        v_val_6345_ = leanh::lean_ctor_get(v___x_6344_, 0);
        leanh::lean_inc(v_val_6345_);
        leanh::lean_dec_ref_known(v___x_6344_, 1);
        v___f_6346_ = leanh::lean_alloc_closure(
            l_Lean_Widget_withGoalCtx___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_6346_, 0, v_val_6345_);
        leanh::lean_closure_set(v___f_6346_, 1, v_action_6337_);
        leanh::lean_closure_set(v___f_6346_, 2, v_inst_6338_);
        leanh::lean_closure_set(v___f_6346_, 3, v_inst_6339_);
        v___x_6347_ = leanh::lean_apply_4(
            v_toBind_6340_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_inst_6341_,
            v___f_6346_,
        );
        return v___x_6347_;
    } else {
        let mut v___x_6348_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6349_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6350_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6351_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_6344_);
        leanh::lean_dec(v_inst_6341_);
        leanh::lean_dec(v_toBind_6340_);
        leanh::lean_dec_ref(v_inst_6338_);
        leanh::lean_dec(v_action_6337_);
        v___x_6348_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Widget_withGoalCtx___redArg___lam__1___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Widget_withGoalCtx___redArg___lam__1___closed__1_once),
            _init_l_Lean_Widget_withGoalCtx___redArg___lam__1___closed__1,
        );
        v___x_6349_ = l_Lean_MessageData_ofName(v_goal_6336_);
        v___x_6350_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_6350_, 0, v___x_6348_);
        leanh::lean_ctor_set(v___x_6350_, 1, v___x_6349_);
        v___x_6351_ = l_Lean_throwError___redArg(v_inst_6339_, v_inst_6342_, v___x_6350_);
        return v___x_6351_;
    }
}
pub unsafe fn l_Lean_Widget_withGoalCtx___redArg___lam__1___boxed(
    mut v_goal_6352_: *mut leanh::LeanObject,
    mut v_action_6353_: *mut leanh::LeanObject,
    mut v_inst_6354_: *mut leanh::LeanObject,
    mut v_inst_6355_: *mut leanh::LeanObject,
    mut v_toBind_6356_: *mut leanh::LeanObject,
    mut v_inst_6357_: *mut leanh::LeanObject,
    mut v_inst_6358_: *mut leanh::LeanObject,
    mut v_mctx_6359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6360_ = l_Lean_Widget_withGoalCtx___redArg___lam__1(
        v_goal_6352_,
        v_action_6353_,
        v_inst_6354_,
        v_inst_6355_,
        v_toBind_6356_,
        v_inst_6357_,
        v_inst_6358_,
        v_mctx_6359_,
    );
    leanh::lean_dec_ref(v_mctx_6359_);
    return v_res_6360_;
}
pub unsafe fn l_Lean_Widget_withGoalCtx___redArg(
    mut v_inst_6361_: *mut leanh::LeanObject,
    mut v_inst_6362_: *mut leanh::LeanObject,
    mut v_inst_6363_: *mut leanh::LeanObject,
    mut v_inst_6364_: *mut leanh::LeanObject,
    mut v_inst_6365_: *mut leanh::LeanObject,
    mut v_goal_6366_: *mut leanh::LeanObject,
    mut v_action_6367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_6368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getMCtx_6369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_6368_ = leanh::lean_ctor_get(v_inst_6362_, 1);
    leanh::lean_inc_n(v_toBind_6368_, 2);
    v_getMCtx_6369_ = leanh::lean_ctor_get(v_inst_6365_, 0);
    leanh::lean_inc(v_getMCtx_6369_);
    leanh::lean_dec_ref(v_inst_6365_);
    v___f_6370_ = leanh::lean_alloc_closure(
        l_Lean_Widget_withGoalCtx___redArg___lam__1___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_6370_, 0, v_goal_6366_);
    leanh::lean_closure_set(v___f_6370_, 1, v_action_6367_);
    leanh::lean_closure_set(v___f_6370_, 2, v_inst_6361_);
    leanh::lean_closure_set(v___f_6370_, 3, v_inst_6362_);
    leanh::lean_closure_set(v___f_6370_, 4, v_toBind_6368_);
    leanh::lean_closure_set(v___f_6370_, 5, v_inst_6364_);
    leanh::lean_closure_set(v___f_6370_, 6, v_inst_6363_);
    v___x_6371_ = leanh::lean_apply_4(
        v_toBind_6368_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getMCtx_6369_,
        v___f_6370_,
    );
    return v___x_6371_;
}
pub unsafe fn l_Lean_Widget_withGoalCtx(
    mut v_n_6372_: *mut leanh::LeanObject,
    mut v_inst_6373_: *mut leanh::LeanObject,
    mut v_inst_6374_: *mut leanh::LeanObject,
    mut v_inst_6375_: *mut leanh::LeanObject,
    mut v_inst_6376_: *mut leanh::LeanObject,
    mut v_inst_6377_: *mut leanh::LeanObject,
    mut v_00_u03b1_6378_: *mut leanh::LeanObject,
    mut v_goal_6379_: *mut leanh::LeanObject,
    mut v_action_6380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6381_ = l_Lean_Widget_withGoalCtx___redArg(
        v_inst_6373_,
        v_inst_6374_,
        v_inst_6375_,
        v_inst_6376_,
        v_inst_6377_,
        v_goal_6379_,
        v_action_6380_,
    );
    return v___x_6381_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Widget_goalToInteractive_spec__0(
    mut v_opts_6382_: *mut leanh::LeanObject,
    mut v_opt_6383_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_6384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_6385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_6386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_6384_ = leanh::lean_ctor_get(v_opt_6383_, 0);
    v_defValue_6385_ = leanh::lean_ctor_get(v_opt_6383_, 1);
    v_map_6386_ = leanh::lean_ctor_get(v_opts_6382_, 0);
    v___x_6387_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_6386_,
            v_name_6384_,
        );
    if leanh::lean_obj_tag(v___x_6387_) == 0 {
        let mut v___x_6388_: u8 = 0;
        v___x_6388_ = (leanh::lean_unbox(v_defValue_6385_) as u8);
        return v___x_6388_;
    } else {
        let mut v_val_6389_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_6389_ = leanh::lean_ctor_get(v___x_6387_, 0);
        leanh::lean_inc(v_val_6389_);
        leanh::lean_dec_ref_known(v___x_6387_, 1);
        if leanh::lean_obj_tag(v_val_6389_) == 1 {
            let mut v_v_6390_: u8 = 0;
            v_v_6390_ = leanh::lean_ctor_get_uint8(v_val_6389_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_6389_, 0);
            return v_v_6390_;
        } else {
            let mut v___x_6391_: u8 = 0;
            leanh::lean_dec(v_val_6389_);
            v___x_6391_ = (leanh::lean_unbox(v_defValue_6385_) as u8);
            return v___x_6391_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Widget_goalToInteractive_spec__0___boxed(
    mut v_opts_6392_: *mut leanh::LeanObject,
    mut v_opt_6393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6394_: u8 = 0;
    let mut v_r_6395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6394_ =
        l_Lean_Option_get___at___00Lean_Widget_goalToInteractive_spec__0(v_opts_6392_, v_opt_6393_);
    leanh::lean_dec_ref(v_opt_6393_);
    leanh::lean_dec_ref(v_opts_6392_);
    v_r_6395_ = leanh::lean_box((v_res_6394_) as usize);
    return v_r_6395_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Widget_goalToInteractive_spec__1(
    mut v_x_6396_: *mut leanh::LeanObject,
    mut v_x_6397_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_6396_) == 0 {
        if leanh::lean_obj_tag(v_x_6397_) == 0 {
            let mut v___x_6398_: u8 = 0;
            v___x_6398_ = 1;
            return v___x_6398_;
        } else {
            let mut v___x_6399_: u8 = 0;
            v___x_6399_ = 0;
            return v___x_6399_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_6397_) == 0 {
            let mut v___x_6400_: u8 = 0;
            v___x_6400_ = 0;
            return v___x_6400_;
        } else {
            let mut v_val_6401_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_6402_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6403_: u8 = 0;
            v_val_6401_ = leanh::lean_ctor_get(v_x_6396_, 0);
            v_val_6402_ = leanh::lean_ctor_get(v_x_6397_, 0);
            v___x_6403_ = lean_expr_eqv(v_val_6401_, v_val_6402_);
            return v___x_6403_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Widget_goalToInteractive_spec__1___boxed(
    mut v_x_6404_: *mut leanh::LeanObject,
    mut v_x_6405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6406_: u8 = 0;
    let mut v_r_6407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6406_ =
        l_Option_instBEq_beq___at___00Lean_Widget_goalToInteractive_spec__1(v_x_6404_, v_x_6405_);
    leanh::lean_dec(v_x_6405_);
    leanh::lean_dec(v_x_6404_);
    v_r_6407_ = leanh::lean_box((v_res_6406_) as usize);
    return v_r_6407_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3___lam__0(
    mut v_ids_6408_: *mut leanh::LeanObject,
    mut v_type_x3f_6409_: *mut leanh::LeanObject,
    mut v_hyps_6410_: *mut leanh::LeanObject,
    mut v___y_6411_: *mut leanh::LeanObject,
    mut v___y_6412_: *mut leanh::LeanObject,
    mut v___y_6413_: *mut leanh::LeanObject,
    mut v___y_6414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6418_: u8 = 0;
    v___x_6416_ = lean_array_get_size(v_ids_6408_);
    v___x_6417_ = leanh::lean_unsigned_to_nat(0);
    v___x_6418_ = lean_nat_dec_eq(v___x_6416_, v___x_6417_);
    if v___x_6418_ == 0 {
        if leanh::lean_obj_tag(v_type_x3f_6409_) == 0 {
            let mut v___x_6419_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_ids_6408_);
            v___x_6419_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_6419_, 0, v_hyps_6410_);
            return v___x_6419_;
        } else {
            let mut v_val_6420_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6421_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6422_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_6420_ = leanh::lean_ctor_get(v_type_x3f_6409_, 0);
            leanh::lean_inc(v_val_6420_);
            leanh::lean_dec_ref_known(v_type_x3f_6409_, 1);
            v___x_6421_ = leanh::lean_box(0);
            v___x_6422_ = l_Lean_Widget_addInteractiveHypothesisBundle(
                v_hyps_6410_,
                v_ids_6408_,
                v_val_6420_,
                v___x_6421_,
                v___x_6418_,
                v___y_6411_,
                v___y_6412_,
                v___y_6413_,
                v___y_6414_,
            );
            return v___x_6422_;
        }
    } else {
        let mut v___x_6423_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_type_x3f_6409_);
        leanh::lean_dec_ref(v_ids_6408_);
        v___x_6423_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6423_, 0, v_hyps_6410_);
        return v___x_6423_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3___lam__0___boxed(
    mut v_ids_6424_: *mut leanh::LeanObject,
    mut v_type_x3f_6425_: *mut leanh::LeanObject,
    mut v_hyps_6426_: *mut leanh::LeanObject,
    mut v___y_6427_: *mut leanh::LeanObject,
    mut v___y_6428_: *mut leanh::LeanObject,
    mut v___y_6429_: *mut leanh::LeanObject,
    mut v___y_6430_: *mut leanh::LeanObject,
    mut v___y_6431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3___lam__0(v_ids_6424_, v_type_x3f_6425_, v_hyps_6426_, v___y_6427_, v___y_6428_, v___y_6429_, v___y_6430_);
    leanh::lean_dec(v___y_6430_);
    leanh::lean_dec_ref(v___y_6429_);
    leanh::lean_dec(v___y_6428_);
    leanh::lean_dec_ref(v___y_6427_);
    return v_res_6432_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4_spec__9(
    mut v___x_6435_: u8,
    mut v___x_6436_: u8,
    mut v___x_6437_: u8,
    mut v_as_6438_: *mut leanh::LeanObject,
    mut v_sz_6439_: usize,
    mut v_i_6440_: usize,
    mut v_b_6441_: *mut leanh::LeanObject,
    mut v___y_6442_: *mut leanh::LeanObject,
    mut v___y_6443_: *mut leanh::LeanObject,
    mut v___y_6444_: *mut leanh::LeanObject,
    mut v___y_6445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6447_: u8 = 0;
    let mut v___x_6448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6452_: u8 = 0;
    let mut v___x_6453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6458_: usize = 0;
    let mut v___x_6459_: usize = 0;
    let mut v_reuseFailAlloc_6461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varNames_6464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_6465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varNames_6471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_6472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6481_: u8 = 0;
    let mut v_fst_6482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6485_: u8 = 0;
    let mut v_fst_6486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6490_: u8 = 0;
    let mut v___x_6493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6502_: u8 = 0;
    let mut v___x_6503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6512_: u8 = 0;
    let mut v___x_6514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6516_: u8 = 0;
    let mut v___x_6517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6523_: u8 = 0;
    let mut v___x_6524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6533_: u8 = 0;
    let mut v___x_6535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6537_: u8 = 0;
    let mut v___x_6538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_6543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6548_: u8 = 0;
    let mut v___x_6550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: u8 = 0;
    let mut v_reuseFailAlloc_6552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6556_: u8 = 0;
    let mut v___x_6558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6560_: u8 = 0;
    let mut v_nondep_6561_: u8 = 0;
    let mut v_fvarId_6562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_6563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6586_: u8 = 0;
    let mut v___x_6588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6590_: u8 = 0;
    let mut v_reuseFailAlloc_6591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6595_: u8 = 0;
    let mut v___x_6597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6599_: u8 = 0;
    let mut v_a_6600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6603_: u8 = 0;
    let mut v___x_6605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6607_: u8 = 0;
    let mut v_a_6608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6611_: u8 = 0;
    let mut v___x_6613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6615_: u8 = 0;
    let mut v_fvarId_6616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_6617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6622_: u8 = 0;
    let mut v___x_6624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6625_: u8 = 0;
    let mut v_reuseFailAlloc_6626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6630_: u8 = 0;
    let mut v___x_6632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6634_: u8 = 0;
    let mut v___x_6636_: u8 = 0;
    let mut v___x_6637_: u8 = 0;
    let mut v_isSharedCheck_6638_: u8 = 0;
    let mut v_isSharedCheck_6639_: u8 = 0;
    let mut v_unused_6640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6641_: u8 = 0;
    let mut v_isSharedCheck_6642_: u8 = 0;
    let mut v_unused_6643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6447_ = lean_usize_dec_lt(v_i_6440_, v_sz_6439_);
                if v___x_6447_ == 0 {
                    v___x_6448_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6448_, 0, v_b_6441_);
                    return v___x_6448_;
                } else {
                    v_snd_6449_ = leanh::lean_ctor_get(v_b_6441_, 1);
                    v_isSharedCheck_6642_ = (!leanh::lean_is_exclusive(v_b_6441_)) as u8;
                    if v_isSharedCheck_6642_ == 0 {
                        v_unused_6643_ = leanh::lean_ctor_get(v_b_6441_, 0);
                        leanh::lean_dec(v_unused_6643_);
                        v___x_6451_ = v_b_6441_;
                        v_isShared_6452_ = v_isSharedCheck_6642_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_6449_);
                        leanh::lean_dec(v_b_6441_);
                        v___x_6451_ = leanh::lean_box(0);
                        v_isShared_6452_ = v_isSharedCheck_6642_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6453_ = leanh::lean_box(0);
                v_a_6476_ = lean_array_uget(v_as_6438_, v_i_6440_);
                if leanh::lean_obj_tag(v_a_6476_) == 0 {
                    v_a_6455_ = v_snd_6449_;
                    state = 2;
                    continue;
                } else {
                    v_snd_6477_ = leanh::lean_ctor_get(v_snd_6449_, 1);
                    leanh::lean_inc(v_snd_6477_);
                    v_val_6478_ = leanh::lean_ctor_get(v_a_6476_, 0);
                    v_isSharedCheck_6641_ = (!leanh::lean_is_exclusive(v_a_6476_)) as u8;
                    if v_isSharedCheck_6641_ == 0 {
                        v___x_6480_ = v_a_6476_;
                        v_isShared_6481_ = v_isSharedCheck_6641_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6478_);
                        leanh::lean_dec(v_a_6476_);
                        v___x_6480_ = leanh::lean_box(0);
                        v_isShared_6481_ = v_isSharedCheck_6641_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6452_ == 0 {
                    leanh::lean_ctor_set(v___x_6451_, 1, v_a_6455_);
                    leanh::lean_ctor_set(v___x_6451_, 0, v___x_6453_);
                    v___x_6457_ = v___x_6451_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6461_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6461_, 0, v___x_6453_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6461_, 1, v_a_6455_);
                    v___x_6457_ = v_reuseFailAlloc_6461_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6458_ = 1usize;
                v___x_6459_ = lean_usize_add(v_i_6440_, v___x_6458_);
                v_i_6440_ = v___x_6459_;
                v_b_6441_ = v___x_6457_;
                state = 0;
                continue;
            }
            4 => {
                v___x_6466_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6466_, 0, v___y_6463_);
                v___x_6467_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6467_, 0, v___x_6466_);
                leanh::lean_ctor_set(v___x_6467_, 1, v_hyps_6465_);
                v___x_6468_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6468_, 0, v_varNames_6464_);
                leanh::lean_ctor_set(v___x_6468_, 1, v___x_6467_);
                v_a_6455_ = v___x_6468_;
                state = 2;
                continue;
            }
            5 => {
                v___x_6473_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6473_, 0, v___y_6470_);
                v___x_6474_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6474_, 0, v___x_6473_);
                leanh::lean_ctor_set(v___x_6474_, 1, v_hyps_6472_);
                v___x_6475_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6475_, 0, v_varNames_6471_);
                leanh::lean_ctor_set(v___x_6475_, 1, v___x_6474_);
                v_a_6455_ = v___x_6475_;
                state = 2;
                continue;
            }
            6 => {
                v_fst_6482_ = leanh::lean_ctor_get(v_snd_6449_, 0);
                v_isSharedCheck_6639_ = (!leanh::lean_is_exclusive(v_snd_6449_)) as u8;
                if v_isSharedCheck_6639_ == 0 {
                    v_unused_6640_ = leanh::lean_ctor_get(v_snd_6449_, 1);
                    leanh::lean_dec(v_unused_6640_);
                    v___x_6484_ = v_snd_6449_;
                    v_isShared_6485_ = v_isSharedCheck_6639_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_6482_);
                    leanh::lean_dec(v_snd_6449_);
                    v___x_6484_ = leanh::lean_box(0);
                    v_isShared_6485_ = v_isSharedCheck_6639_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_fst_6486_ = leanh::lean_ctor_get(v_snd_6477_, 0);
                v_snd_6487_ = leanh::lean_ctor_get(v_snd_6477_, 1);
                v_isSharedCheck_6638_ = (!leanh::lean_is_exclusive(v_snd_6477_)) as u8;
                if v_isSharedCheck_6638_ == 0 {
                    v___x_6489_ = v_snd_6477_;
                    v_isShared_6490_ = v_isSharedCheck_6638_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_6487_);
                    leanh::lean_inc(v_fst_6486_);
                    leanh::lean_dec(v_snd_6477_);
                    v___x_6489_ = leanh::lean_box(0);
                    v_isShared_6490_ = v_isSharedCheck_6638_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_6540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4_spec__9___closed__0;
                if v___x_6437_ == 0 {
                    v___x_6637_ = l_Lean_LocalDecl_isAuxDecl(v_val_6478_);
                    if v___x_6637_ == 0 {
                        state = 34;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_6480_);
                        leanh::lean_dec(v_val_6478_);
                        state = 9;
                        continue;
                    }
                } else {
                    state = 34;
                    continue;
                }
            }
            9 => {
                if v_isShared_6490_ == 0 {
                    v___x_6493_ = v___x_6489_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6497_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6497_, 0, v_fst_6486_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6497_, 1, v_snd_6487_);
                    v___x_6493_ = v_reuseFailAlloc_6497_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_6485_ == 0 {
                    leanh::lean_ctor_set(v___x_6484_, 1, v___x_6493_);
                    v___x_6495_ = v___x_6484_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6496_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6496_, 0, v_fst_6482_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6496_, 1, v___x_6493_);
                    v___x_6495_ = v_reuseFailAlloc_6496_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_a_6455_ = v___x_6495_;
                state = 2;
                continue;
            }
            12 => {
                if v___y_6502_ == 0 {
                    v___x_6503_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3___lam__0(v_fst_6482_, v_fst_6486_, v_snd_6487_, v___y_6442_, v___y_6443_, v___y_6444_, v___y_6445_);
                    if leanh::lean_obj_tag(v___x_6503_) == 0 {
                        v_a_6504_ = leanh::lean_ctor_get(v___x_6503_, 0);
                        leanh::lean_inc(v_a_6504_);
                        leanh::lean_dec_ref_known(v___x_6503_, 1);
                        v___x_6505_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6505_, 0, v___y_6500_);
                        leanh::lean_ctor_set(v___x_6505_, 1, v___y_6501_);
                        v___x_6506_ = leanh::lean_unsigned_to_nat(1);
                        v___x_6507_ = lean_mk_empty_array_with_capacity(v___x_6506_);
                        v___x_6508_ = lean_array_push(v___x_6507_, v___x_6505_);
                        v___y_6463_ = v___y_6499_;
                        v_varNames_6464_ = v___x_6508_;
                        v_hyps_6465_ = v_a_6504_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v___y_6501_);
                        leanh::lean_dec_ref(v___y_6500_);
                        leanh::lean_dec_ref(v___y_6499_);
                        leanh::lean_del_object(v___x_6451_);
                        v_a_6509_ = leanh::lean_ctor_get(v___x_6503_, 0);
                        v_isSharedCheck_6516_ =
                            (!leanh::lean_is_exclusive(v___x_6503_)) as u8;
                        if v_isSharedCheck_6516_ == 0 {
                            v___x_6511_ = v___x_6503_;
                            v_isShared_6512_ = v_isSharedCheck_6516_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6509_);
                            leanh::lean_dec(v___x_6503_);
                            v___x_6511_ = leanh::lean_box(0);
                            v_isShared_6512_ = v_isSharedCheck_6516_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_fst_6486_);
                    v___x_6517_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6517_, 0, v___y_6500_);
                    leanh::lean_ctor_set(v___x_6517_, 1, v___y_6501_);
                    v___x_6518_ = lean_array_push(v_fst_6482_, v___x_6517_);
                    v___y_6463_ = v___y_6499_;
                    v_varNames_6464_ = v___x_6518_;
                    v_hyps_6465_ = v_snd_6487_;
                    state = 4;
                    continue;
                }
            }
            13 => {
                if v_isShared_6512_ == 0 {
                    v___x_6514_ = v___x_6511_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6515_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6515_, 0, v_a_6509_);
                    v___x_6514_ = v_reuseFailAlloc_6515_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6514_;
            }
            15 => {
                if v___y_6523_ == 0 {
                    v___x_6524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3___lam__0(v_fst_6482_, v_fst_6486_, v_snd_6487_, v___y_6442_, v___y_6443_, v___y_6444_, v___y_6445_);
                    if leanh::lean_obj_tag(v___x_6524_) == 0 {
                        v_a_6525_ = leanh::lean_ctor_get(v___x_6524_, 0);
                        leanh::lean_inc(v_a_6525_);
                        leanh::lean_dec_ref_known(v___x_6524_, 1);
                        v___x_6526_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6526_, 0, v___y_6520_);
                        leanh::lean_ctor_set(v___x_6526_, 1, v___y_6522_);
                        v___x_6527_ = leanh::lean_unsigned_to_nat(1);
                        v___x_6528_ = lean_mk_empty_array_with_capacity(v___x_6527_);
                        v___x_6529_ = lean_array_push(v___x_6528_, v___x_6526_);
                        v___y_6470_ = v___y_6521_;
                        v_varNames_6471_ = v___x_6529_;
                        v_hyps_6472_ = v_a_6525_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___y_6522_);
                        leanh::lean_dec_ref(v___y_6521_);
                        leanh::lean_dec_ref(v___y_6520_);
                        leanh::lean_del_object(v___x_6451_);
                        v_a_6530_ = leanh::lean_ctor_get(v___x_6524_, 0);
                        v_isSharedCheck_6537_ =
                            (!leanh::lean_is_exclusive(v___x_6524_)) as u8;
                        if v_isSharedCheck_6537_ == 0 {
                            v___x_6532_ = v___x_6524_;
                            v_isShared_6533_ = v_isSharedCheck_6537_;
                            state = 16;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6530_);
                            leanh::lean_dec(v___x_6524_);
                            v___x_6532_ = leanh::lean_box(0);
                            v_isShared_6533_ = v_isSharedCheck_6537_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_fst_6486_);
                    v___x_6538_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6538_, 0, v___y_6520_);
                    leanh::lean_ctor_set(v___x_6538_, 1, v___y_6522_);
                    v___x_6539_ = lean_array_push(v_fst_6482_, v___x_6538_);
                    v___y_6470_ = v___y_6521_;
                    v_varNames_6471_ = v___x_6539_;
                    v_hyps_6472_ = v_snd_6487_;
                    state = 5;
                    continue;
                }
            }
            16 => {
                if v_isShared_6533_ == 0 {
                    v___x_6535_ = v___x_6532_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6536_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6536_, 0, v_a_6530_);
                    v___x_6535_ = v_reuseFailAlloc_6536_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6535_;
            }
            18 => {
                if leanh::lean_obj_tag(v_val_6478_) == 0 {
                    v_fvarId_6542_ = leanh::lean_ctor_get(v_val_6478_, 1);
                    leanh::lean_inc(v_fvarId_6542_);
                    v_userName_6543_ = leanh::lean_ctor_get(v_val_6478_, 2);
                    leanh::lean_inc(v_userName_6543_);
                    v_type_6544_ = leanh::lean_ctor_get(v_val_6478_, 3);
                    leanh::lean_inc_ref(v_type_6544_);
                    leanh::lean_dec_ref_known(v_val_6478_, 4);
                    v___x_6545_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_6544_, v___y_6443_);
                    if leanh::lean_obj_tag(v___x_6545_) == 0 {
                        v_a_6546_ = leanh::lean_ctor_get(v___x_6545_, 0);
                        leanh::lean_inc(v_a_6546_);
                        leanh::lean_dec_ref_known(v___x_6545_, 1);
                        v___x_6547_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_userName_6543_,
                                v___x_6447_,
                            );
                        v___x_6548_ =
                            l_Option_instBEq_beq___at___00Lean_Widget_goalToInteractive_spec__1(
                                v_fst_6486_,
                                v___x_6453_,
                            );
                        if v___x_6548_ == 0 {
                            leanh::lean_inc(v_a_6546_);
                            if v_isShared_6481_ == 0 {
                                leanh::lean_ctor_set(v___x_6480_, 0, v_a_6546_);
                                v___x_6550_ = v___x_6480_;
                                state = 19;
                                continue;
                            } else {
                                v_reuseFailAlloc_6552_ =
                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_6552_, 0, v_a_6546_);
                                v___x_6550_ = v_reuseFailAlloc_6552_;
                                state = 19;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_6480_);
                            v___y_6499_ = v_a_6546_;
                            v___y_6500_ = v___x_6547_;
                            v___y_6501_ = v_fvarId_6542_;
                            v___y_6502_ = v___x_6548_;
                            state = 12;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_userName_6543_);
                        leanh::lean_dec(v_fvarId_6542_);
                        leanh::lean_dec(v_snd_6487_);
                        leanh::lean_dec(v_fst_6486_);
                        leanh::lean_dec(v_fst_6482_);
                        leanh::lean_del_object(v___x_6480_);
                        leanh::lean_del_object(v___x_6451_);
                        v_a_6553_ = leanh::lean_ctor_get(v___x_6545_, 0);
                        v_isSharedCheck_6560_ =
                            (!leanh::lean_is_exclusive(v___x_6545_)) as u8;
                        if v_isSharedCheck_6560_ == 0 {
                            v___x_6555_ = v___x_6545_;
                            v_isShared_6556_ = v_isSharedCheck_6560_;
                            state = 20;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6553_);
                            leanh::lean_dec(v___x_6545_);
                            v___x_6555_ = leanh::lean_box(0);
                            v_isShared_6556_ = v_isSharedCheck_6560_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    v_nondep_6561_ = leanh::lean_ctor_get_uint8(
                        v_val_6478_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    );
                    if v_nondep_6561_ == 0 {
                        v_fvarId_6562_ = leanh::lean_ctor_get(v_val_6478_, 1);
                        leanh::lean_inc(v_fvarId_6562_);
                        v_userName_6563_ = leanh::lean_ctor_get(v_val_6478_, 2);
                        leanh::lean_inc(v_userName_6563_);
                        v_type_6564_ = leanh::lean_ctor_get(v_val_6478_, 3);
                        leanh::lean_inc_ref(v_type_6564_);
                        v_value_6565_ = leanh::lean_ctor_get(v_val_6478_, 4);
                        leanh::lean_inc_ref(v_value_6565_);
                        leanh::lean_dec_ref_known(v_val_6478_, 5);
                        v___x_6566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3___lam__0(v_fst_6482_, v_fst_6486_, v_snd_6487_, v___y_6442_, v___y_6443_, v___y_6444_, v___y_6445_);
                        if leanh::lean_obj_tag(v___x_6566_) == 0 {
                            v_a_6567_ = leanh::lean_ctor_get(v___x_6566_, 0);
                            leanh::lean_inc(v_a_6567_);
                            leanh::lean_dec_ref_known(v___x_6566_, 1);
                            v___x_6568_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_6564_, v___y_6443_);
                            if leanh::lean_obj_tag(v___x_6568_) == 0 {
                                v_a_6569_ = leanh::lean_ctor_get(v___x_6568_, 0);
                                leanh::lean_inc(v_a_6569_);
                                leanh::lean_dec_ref_known(v___x_6568_, 1);
                                v___x_6570_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_value_6565_, v___y_6443_);
                                if leanh::lean_obj_tag(v___x_6570_) == 0 {
                                    v_a_6571_ = leanh::lean_ctor_get(v___x_6570_, 0);
                                    leanh::lean_inc(v_a_6571_);
                                    leanh::lean_dec_ref_known(v___x_6570_, 1);
                                    v___x_6572_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_6563_, v___x_6447_);
                                    v___x_6573_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_6573_, 0, v___x_6572_);
                                    leanh::lean_ctor_set(v___x_6573_, 1, v_fvarId_6562_);
                                    v___x_6574_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_6575_ = lean_mk_empty_array_with_capacity(v___x_6574_);
                                    v___x_6576_ = lean_array_push(v___x_6575_, v___x_6573_);
                                    if v_isShared_6481_ == 0 {
                                        leanh::lean_ctor_set(v___x_6480_, 0, v_a_6571_);
                                        v___x_6578_ = v___x_6480_;
                                        state = 22;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_6591_ =
                                            leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_6591_,
                                            0,
                                            v_a_6571_,
                                        );
                                        v___x_6578_ = v_reuseFailAlloc_6591_;
                                        state = 22;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_6569_);
                                    leanh::lean_dec(v_a_6567_);
                                    leanh::lean_dec(v_userName_6563_);
                                    leanh::lean_dec(v_fvarId_6562_);
                                    leanh::lean_del_object(v___x_6480_);
                                    leanh::lean_del_object(v___x_6451_);
                                    v_a_6592_ = leanh::lean_ctor_get(v___x_6570_, 0);
                                    v_isSharedCheck_6599_ =
                                        (!leanh::lean_is_exclusive(v___x_6570_)) as u8;
                                    if v_isSharedCheck_6599_ == 0 {
                                        v___x_6594_ = v___x_6570_;
                                        v_isShared_6595_ = v_isSharedCheck_6599_;
                                        state = 25;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_6592_);
                                        leanh::lean_dec(v___x_6570_);
                                        v___x_6594_ = leanh::lean_box(0);
                                        v_isShared_6595_ = v_isSharedCheck_6599_;
                                        state = 25;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_6567_);
                                leanh::lean_dec_ref(v_value_6565_);
                                leanh::lean_dec(v_userName_6563_);
                                leanh::lean_dec(v_fvarId_6562_);
                                leanh::lean_del_object(v___x_6480_);
                                leanh::lean_del_object(v___x_6451_);
                                v_a_6600_ = leanh::lean_ctor_get(v___x_6568_, 0);
                                v_isSharedCheck_6607_ =
                                    (!leanh::lean_is_exclusive(v___x_6568_)) as u8;
                                if v_isSharedCheck_6607_ == 0 {
                                    v___x_6602_ = v___x_6568_;
                                    v_isShared_6603_ = v_isSharedCheck_6607_;
                                    state = 27;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6600_);
                                    leanh::lean_dec(v___x_6568_);
                                    v___x_6602_ = leanh::lean_box(0);
                                    v_isShared_6603_ = v_isSharedCheck_6607_;
                                    state = 27;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_value_6565_);
                            leanh::lean_dec_ref(v_type_6564_);
                            leanh::lean_dec(v_userName_6563_);
                            leanh::lean_dec(v_fvarId_6562_);
                            leanh::lean_del_object(v___x_6480_);
                            leanh::lean_del_object(v___x_6451_);
                            v_a_6608_ = leanh::lean_ctor_get(v___x_6566_, 0);
                            v_isSharedCheck_6615_ =
                                (!leanh::lean_is_exclusive(v___x_6566_)) as u8;
                            if v_isSharedCheck_6615_ == 0 {
                                v___x_6610_ = v___x_6566_;
                                v_isShared_6611_ = v_isSharedCheck_6615_;
                                state = 29;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6608_);
                                leanh::lean_dec(v___x_6566_);
                                v___x_6610_ = leanh::lean_box(0);
                                v_isShared_6611_ = v_isSharedCheck_6615_;
                                state = 29;
                                continue;
                            }
                        }
                    } else {
                        v_fvarId_6616_ = leanh::lean_ctor_get(v_val_6478_, 1);
                        leanh::lean_inc(v_fvarId_6616_);
                        v_userName_6617_ = leanh::lean_ctor_get(v_val_6478_, 2);
                        leanh::lean_inc(v_userName_6617_);
                        v_type_6618_ = leanh::lean_ctor_get(v_val_6478_, 3);
                        leanh::lean_inc_ref(v_type_6618_);
                        leanh::lean_dec_ref_known(v_val_6478_, 5);
                        v___x_6619_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_6618_, v___y_6443_);
                        if leanh::lean_obj_tag(v___x_6619_) == 0 {
                            v_a_6620_ = leanh::lean_ctor_get(v___x_6619_, 0);
                            leanh::lean_inc(v_a_6620_);
                            leanh::lean_dec_ref_known(v___x_6619_, 1);
                            v___x_6621_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_userName_6617_,
                                    v_nondep_6561_,
                                );
                            v___x_6622_ =
                                l_Option_instBEq_beq___at___00Lean_Widget_goalToInteractive_spec__1(
                                    v_fst_6486_,
                                    v___x_6453_,
                                );
                            if v___x_6622_ == 0 {
                                leanh::lean_inc(v_a_6620_);
                                if v_isShared_6481_ == 0 {
                                    leanh::lean_ctor_set(v___x_6480_, 0, v_a_6620_);
                                    v___x_6624_ = v___x_6480_;
                                    state = 31;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6626_ =
                                        leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6626_,
                                        0,
                                        v_a_6620_,
                                    );
                                    v___x_6624_ = v_reuseFailAlloc_6626_;
                                    state = 31;
                                    continue;
                                }
                            } else {
                                leanh::lean_del_object(v___x_6480_);
                                v___y_6520_ = v___x_6621_;
                                v___y_6521_ = v_a_6620_;
                                v___y_6522_ = v_fvarId_6616_;
                                v___y_6523_ = v___x_6622_;
                                state = 15;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_userName_6617_);
                            leanh::lean_dec(v_fvarId_6616_);
                            leanh::lean_dec(v_snd_6487_);
                            leanh::lean_dec(v_fst_6486_);
                            leanh::lean_dec(v_fst_6482_);
                            leanh::lean_del_object(v___x_6480_);
                            leanh::lean_del_object(v___x_6451_);
                            v_a_6627_ = leanh::lean_ctor_get(v___x_6619_, 0);
                            v_isSharedCheck_6634_ =
                                (!leanh::lean_is_exclusive(v___x_6619_)) as u8;
                            if v_isSharedCheck_6634_ == 0 {
                                v___x_6629_ = v___x_6619_;
                                v_isShared_6630_ = v_isSharedCheck_6634_;
                                state = 32;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6627_);
                                leanh::lean_dec(v___x_6619_);
                                v___x_6629_ = leanh::lean_box(0);
                                v_isShared_6630_ = v_isSharedCheck_6634_;
                                state = 32;
                                continue;
                            }
                        }
                    }
                }
            }
            19 => {
                v___x_6551_ = l_Option_instBEq_beq___at___00Lean_Widget_goalToInteractive_spec__1(
                    v_fst_6486_,
                    v___x_6550_,
                );
                leanh::lean_dec_ref(v___x_6550_);
                v___y_6499_ = v_a_6546_;
                v___y_6500_ = v___x_6547_;
                v___y_6501_ = v_fvarId_6542_;
                v___y_6502_ = v___x_6551_;
                state = 12;
                continue;
            }
            20 => {
                if v_isShared_6556_ == 0 {
                    v___x_6558_ = v___x_6555_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_6559_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6559_, 0, v_a_6553_);
                    v___x_6558_ = v_reuseFailAlloc_6559_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_6558_;
            }
            22 => {
                v___x_6579_ = l_Lean_Widget_addInteractiveHypothesisBundle(
                    v_a_6567_,
                    v___x_6576_,
                    v_a_6569_,
                    v___x_6578_,
                    v___x_6435_,
                    v___y_6442_,
                    v___y_6443_,
                    v___y_6444_,
                    v___y_6445_,
                );
                if leanh::lean_obj_tag(v___x_6579_) == 0 {
                    v_a_6580_ = leanh::lean_ctor_get(v___x_6579_, 0);
                    leanh::lean_inc(v_a_6580_);
                    leanh::lean_dec_ref_known(v___x_6579_, 1);
                    v___x_6581_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6581_, 0, v___x_6453_);
                    leanh::lean_ctor_set(v___x_6581_, 1, v_a_6580_);
                    v___x_6582_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6582_, 0, v___x_6540_);
                    leanh::lean_ctor_set(v___x_6582_, 1, v___x_6581_);
                    v_a_6455_ = v___x_6582_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_6451_);
                    v_a_6583_ = leanh::lean_ctor_get(v___x_6579_, 0);
                    v_isSharedCheck_6590_ = (!leanh::lean_is_exclusive(v___x_6579_)) as u8;
                    if v_isSharedCheck_6590_ == 0 {
                        v___x_6585_ = v___x_6579_;
                        v_isShared_6586_ = v_isSharedCheck_6590_;
                        state = 23;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6583_);
                        leanh::lean_dec(v___x_6579_);
                        v___x_6585_ = leanh::lean_box(0);
                        v_isShared_6586_ = v_isSharedCheck_6590_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_6586_ == 0 {
                    v___x_6588_ = v___x_6585_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_6589_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6589_, 0, v_a_6583_);
                    v___x_6588_ = v_reuseFailAlloc_6589_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_6588_;
            }
            25 => {
                if v_isShared_6595_ == 0 {
                    v___x_6597_ = v___x_6594_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_6598_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6598_, 0, v_a_6592_);
                    v___x_6597_ = v_reuseFailAlloc_6598_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_6597_;
            }
            27 => {
                if v_isShared_6603_ == 0 {
                    v___x_6605_ = v___x_6602_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_6606_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6606_, 0, v_a_6600_);
                    v___x_6605_ = v_reuseFailAlloc_6606_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_6605_;
            }
            29 => {
                if v_isShared_6611_ == 0 {
                    v___x_6613_ = v___x_6610_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_6614_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6614_, 0, v_a_6608_);
                    v___x_6613_ = v_reuseFailAlloc_6614_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_6613_;
            }
            31 => {
                v___x_6625_ = l_Option_instBEq_beq___at___00Lean_Widget_goalToInteractive_spec__1(
                    v_fst_6486_,
                    v___x_6624_,
                );
                leanh::lean_dec_ref(v___x_6624_);
                v___y_6520_ = v___x_6621_;
                v___y_6521_ = v_a_6620_;
                v___y_6522_ = v_fvarId_6616_;
                v___y_6523_ = v___x_6625_;
                state = 15;
                continue;
            }
            32 => {
                if v_isShared_6630_ == 0 {
                    v___x_6632_ = v___x_6629_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_6633_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6633_, 0, v_a_6627_);
                    v___x_6632_ = v_reuseFailAlloc_6633_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_6632_;
            }
            34 => {
                if v___x_6436_ == 0 {
                    v___x_6636_ = l_Lean_LocalDecl_isImplementationDetail(v_val_6478_);
                    if v___x_6636_ == 0 {
                        leanh::lean_del_object(v___x_6489_);
                        leanh::lean_del_object(v___x_6484_);
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_6480_);
                        leanh::lean_dec(v_val_6478_);
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6489_);
                    leanh::lean_del_object(v___x_6484_);
                    state = 18;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4_spec__9___boxed(
    mut v___x_6644_: *mut leanh::LeanObject,
    mut v___x_6645_: *mut leanh::LeanObject,
    mut v___x_6646_: *mut leanh::LeanObject,
    mut v_as_6647_: *mut leanh::LeanObject,
    mut v_sz_6648_: *mut leanh::LeanObject,
    mut v_i_6649_: *mut leanh::LeanObject,
    mut v_b_6650_: *mut leanh::LeanObject,
    mut v___y_6651_: *mut leanh::LeanObject,
    mut v___y_6652_: *mut leanh::LeanObject,
    mut v___y_6653_: *mut leanh::LeanObject,
    mut v___y_6654_: *mut leanh::LeanObject,
    mut v___y_6655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_11682__boxed_6656_: u8 = 0;
    let mut v___x_11683__boxed_6657_: u8 = 0;
    let mut v___x_11684__boxed_6658_: u8 = 0;
    let mut v_sz_boxed_6659_: usize = 0;
    let mut v_i_boxed_6660_: usize = 0;
    let mut v_res_6661_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_11682__boxed_6656_ = (leanh::lean_unbox(v___x_6644_) as u8);
    v___x_11683__boxed_6657_ = (leanh::lean_unbox(v___x_6645_) as u8);
    v___x_11684__boxed_6658_ = (leanh::lean_unbox(v___x_6646_) as u8);
    v_sz_boxed_6659_ = leanh::lean_unbox_usize(v_sz_6648_);
    leanh::lean_dec(v_sz_6648_);
    v_i_boxed_6660_ = leanh::lean_unbox_usize(v_i_6649_);
    leanh::lean_dec(v_i_6649_);
    v_res_6661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4_spec__9(v___x_11682__boxed_6656_, v___x_11683__boxed_6657_, v___x_11684__boxed_6658_, v_as_6647_, v_sz_boxed_6659_, v_i_boxed_6660_, v_b_6650_, v___y_6651_, v___y_6652_, v___y_6653_, v___y_6654_);
    leanh::lean_dec(v___y_6654_);
    leanh::lean_dec_ref(v___y_6653_);
    leanh::lean_dec(v___y_6652_);
    leanh::lean_dec_ref(v___y_6651_);
    leanh::lean_dec_ref(v_as_6647_);
    return v_res_6661_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4(
    mut v___x_6662_: u8,
    mut v___x_6663_: u8,
    mut v___x_6664_: u8,
    mut v_as_6665_: *mut leanh::LeanObject,
    mut v_sz_6666_: usize,
    mut v_i_6667_: usize,
    mut v_b_6668_: *mut leanh::LeanObject,
    mut v___y_6669_: *mut leanh::LeanObject,
    mut v___y_6670_: *mut leanh::LeanObject,
    mut v___y_6671_: *mut leanh::LeanObject,
    mut v___y_6672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6674_: u8 = 0;
    let mut v___x_6675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6679_: u8 = 0;
    let mut v___x_6680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: usize = 0;
    let mut v___x_6686_: usize = 0;
    let mut v___x_6687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varNames_6691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_6692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varNames_6698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_6699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6708_: u8 = 0;
    let mut v_fst_6709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6712_: u8 = 0;
    let mut v_fst_6713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6717_: u8 = 0;
    let mut v___x_6720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6729_: u8 = 0;
    let mut v___x_6730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6739_: u8 = 0;
    let mut v___x_6741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6743_: u8 = 0;
    let mut v___x_6744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6750_: u8 = 0;
    let mut v___x_6751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6760_: u8 = 0;
    let mut v___x_6762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6764_: u8 = 0;
    let mut v___x_6765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_6770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6775_: u8 = 0;
    let mut v___x_6777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6778_: u8 = 0;
    let mut v_reuseFailAlloc_6779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6783_: u8 = 0;
    let mut v___x_6785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6787_: u8 = 0;
    let mut v_nondep_6788_: u8 = 0;
    let mut v_fvarId_6789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_6790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6813_: u8 = 0;
    let mut v___x_6815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6817_: u8 = 0;
    let mut v_reuseFailAlloc_6818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6822_: u8 = 0;
    let mut v___x_6824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6826_: u8 = 0;
    let mut v_a_6827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6830_: u8 = 0;
    let mut v___x_6832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6834_: u8 = 0;
    let mut v_a_6835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6838_: u8 = 0;
    let mut v___x_6840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6842_: u8 = 0;
    let mut v_fvarId_6843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_6844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: u8 = 0;
    let mut v___x_6851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: u8 = 0;
    let mut v_reuseFailAlloc_6853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6857_: u8 = 0;
    let mut v___x_6859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6861_: u8 = 0;
    let mut v___x_6863_: u8 = 0;
    let mut v___x_6864_: u8 = 0;
    let mut v_isSharedCheck_6865_: u8 = 0;
    let mut v_isSharedCheck_6866_: u8 = 0;
    let mut v_unused_6867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6868_: u8 = 0;
    let mut v_isSharedCheck_6869_: u8 = 0;
    let mut v_unused_6870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6674_ = lean_usize_dec_lt(v_i_6667_, v_sz_6666_);
                if v___x_6674_ == 0 {
                    v___x_6675_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6675_, 0, v_b_6668_);
                    return v___x_6675_;
                } else {
                    v_snd_6676_ = leanh::lean_ctor_get(v_b_6668_, 1);
                    v_isSharedCheck_6869_ = (!leanh::lean_is_exclusive(v_b_6668_)) as u8;
                    if v_isSharedCheck_6869_ == 0 {
                        v_unused_6870_ = leanh::lean_ctor_get(v_b_6668_, 0);
                        leanh::lean_dec(v_unused_6870_);
                        v___x_6678_ = v_b_6668_;
                        v_isShared_6679_ = v_isSharedCheck_6869_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_6676_);
                        leanh::lean_dec(v_b_6668_);
                        v___x_6678_ = leanh::lean_box(0);
                        v_isShared_6679_ = v_isSharedCheck_6869_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6680_ = leanh::lean_box(0);
                v_a_6703_ = lean_array_uget(v_as_6665_, v_i_6667_);
                if leanh::lean_obj_tag(v_a_6703_) == 0 {
                    v_a_6682_ = v_snd_6676_;
                    state = 2;
                    continue;
                } else {
                    v_snd_6704_ = leanh::lean_ctor_get(v_snd_6676_, 1);
                    leanh::lean_inc(v_snd_6704_);
                    v_val_6705_ = leanh::lean_ctor_get(v_a_6703_, 0);
                    v_isSharedCheck_6868_ = (!leanh::lean_is_exclusive(v_a_6703_)) as u8;
                    if v_isSharedCheck_6868_ == 0 {
                        v___x_6707_ = v_a_6703_;
                        v_isShared_6708_ = v_isSharedCheck_6868_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6705_);
                        leanh::lean_dec(v_a_6703_);
                        v___x_6707_ = leanh::lean_box(0);
                        v_isShared_6708_ = v_isSharedCheck_6868_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6679_ == 0 {
                    leanh::lean_ctor_set(v___x_6678_, 1, v_a_6682_);
                    leanh::lean_ctor_set(v___x_6678_, 0, v___x_6680_);
                    v___x_6684_ = v___x_6678_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6688_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6688_, 0, v___x_6680_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6688_, 1, v_a_6682_);
                    v___x_6684_ = v_reuseFailAlloc_6688_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6685_ = 1usize;
                v___x_6686_ = lean_usize_add(v_i_6667_, v___x_6685_);
                v___x_6687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4_spec__9(v___x_6662_, v___x_6663_, v___x_6664_, v_as_6665_, v_sz_6666_, v___x_6686_, v___x_6684_, v___y_6669_, v___y_6670_, v___y_6671_, v___y_6672_);
                return v___x_6687_;
            }
            4 => {
                v___x_6693_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6693_, 0, v___y_6690_);
                v___x_6694_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6694_, 0, v___x_6693_);
                leanh::lean_ctor_set(v___x_6694_, 1, v_hyps_6692_);
                v___x_6695_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6695_, 0, v_varNames_6691_);
                leanh::lean_ctor_set(v___x_6695_, 1, v___x_6694_);
                v_a_6682_ = v___x_6695_;
                state = 2;
                continue;
            }
            5 => {
                v___x_6700_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6700_, 0, v___y_6697_);
                v___x_6701_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6701_, 0, v___x_6700_);
                leanh::lean_ctor_set(v___x_6701_, 1, v_hyps_6699_);
                v___x_6702_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6702_, 0, v_varNames_6698_);
                leanh::lean_ctor_set(v___x_6702_, 1, v___x_6701_);
                v_a_6682_ = v___x_6702_;
                state = 2;
                continue;
            }
            6 => {
                v_fst_6709_ = leanh::lean_ctor_get(v_snd_6676_, 0);
                v_isSharedCheck_6866_ = (!leanh::lean_is_exclusive(v_snd_6676_)) as u8;
                if v_isSharedCheck_6866_ == 0 {
                    v_unused_6867_ = leanh::lean_ctor_get(v_snd_6676_, 1);
                    leanh::lean_dec(v_unused_6867_);
                    v___x_6711_ = v_snd_6676_;
                    v_isShared_6712_ = v_isSharedCheck_6866_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_6709_);
                    leanh::lean_dec(v_snd_6676_);
                    v___x_6711_ = leanh::lean_box(0);
                    v_isShared_6712_ = v_isSharedCheck_6866_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_fst_6713_ = leanh::lean_ctor_get(v_snd_6704_, 0);
                v_snd_6714_ = leanh::lean_ctor_get(v_snd_6704_, 1);
                v_isSharedCheck_6865_ = (!leanh::lean_is_exclusive(v_snd_6704_)) as u8;
                if v_isSharedCheck_6865_ == 0 {
                    v___x_6716_ = v_snd_6704_;
                    v_isShared_6717_ = v_isSharedCheck_6865_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_6714_);
                    leanh::lean_inc(v_fst_6713_);
                    leanh::lean_dec(v_snd_6704_);
                    v___x_6716_ = leanh::lean_box(0);
                    v_isShared_6717_ = v_isSharedCheck_6865_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_6767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4_spec__9___closed__0;
                if v___x_6664_ == 0 {
                    v___x_6864_ = l_Lean_LocalDecl_isAuxDecl(v_val_6705_);
                    if v___x_6864_ == 0 {
                        state = 34;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_6707_);
                        leanh::lean_dec(v_val_6705_);
                        state = 9;
                        continue;
                    }
                } else {
                    state = 34;
                    continue;
                }
            }
            9 => {
                if v_isShared_6717_ == 0 {
                    v___x_6720_ = v___x_6716_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6724_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6724_, 0, v_fst_6713_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6724_, 1, v_snd_6714_);
                    v___x_6720_ = v_reuseFailAlloc_6724_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_6712_ == 0 {
                    leanh::lean_ctor_set(v___x_6711_, 1, v___x_6720_);
                    v___x_6722_ = v___x_6711_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6723_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6723_, 0, v_fst_6709_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6723_, 1, v___x_6720_);
                    v___x_6722_ = v_reuseFailAlloc_6723_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_a_6682_ = v___x_6722_;
                state = 2;
                continue;
            }
            12 => {
                if v___y_6729_ == 0 {
                    v___x_6730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3___lam__0(v_fst_6709_, v_fst_6713_, v_snd_6714_, v___y_6669_, v___y_6670_, v___y_6671_, v___y_6672_);
                    if leanh::lean_obj_tag(v___x_6730_) == 0 {
                        v_a_6731_ = leanh::lean_ctor_get(v___x_6730_, 0);
                        leanh::lean_inc(v_a_6731_);
                        leanh::lean_dec_ref_known(v___x_6730_, 1);
                        v___x_6732_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6732_, 0, v___y_6728_);
                        leanh::lean_ctor_set(v___x_6732_, 1, v___y_6727_);
                        v___x_6733_ = leanh::lean_unsigned_to_nat(1);
                        v___x_6734_ = lean_mk_empty_array_with_capacity(v___x_6733_);
                        v___x_6735_ = lean_array_push(v___x_6734_, v___x_6732_);
                        v___y_6690_ = v___y_6726_;
                        v_varNames_6691_ = v___x_6735_;
                        v_hyps_6692_ = v_a_6731_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___y_6728_);
                        leanh::lean_dec(v___y_6727_);
                        leanh::lean_dec_ref(v___y_6726_);
                        leanh::lean_del_object(v___x_6678_);
                        v_a_6736_ = leanh::lean_ctor_get(v___x_6730_, 0);
                        v_isSharedCheck_6743_ =
                            (!leanh::lean_is_exclusive(v___x_6730_)) as u8;
                        if v_isSharedCheck_6743_ == 0 {
                            v___x_6738_ = v___x_6730_;
                            v_isShared_6739_ = v_isSharedCheck_6743_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6736_);
                            leanh::lean_dec(v___x_6730_);
                            v___x_6738_ = leanh::lean_box(0);
                            v_isShared_6739_ = v_isSharedCheck_6743_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_fst_6713_);
                    v___x_6744_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6744_, 0, v___y_6728_);
                    leanh::lean_ctor_set(v___x_6744_, 1, v___y_6727_);
                    v___x_6745_ = lean_array_push(v_fst_6709_, v___x_6744_);
                    v___y_6690_ = v___y_6726_;
                    v_varNames_6691_ = v___x_6745_;
                    v_hyps_6692_ = v_snd_6714_;
                    state = 4;
                    continue;
                }
            }
            13 => {
                if v_isShared_6739_ == 0 {
                    v___x_6741_ = v___x_6738_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6742_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6742_, 0, v_a_6736_);
                    v___x_6741_ = v_reuseFailAlloc_6742_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6741_;
            }
            15 => {
                if v___y_6750_ == 0 {
                    v___x_6751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3___lam__0(v_fst_6709_, v_fst_6713_, v_snd_6714_, v___y_6669_, v___y_6670_, v___y_6671_, v___y_6672_);
                    if leanh::lean_obj_tag(v___x_6751_) == 0 {
                        v_a_6752_ = leanh::lean_ctor_get(v___x_6751_, 0);
                        leanh::lean_inc(v_a_6752_);
                        leanh::lean_dec_ref_known(v___x_6751_, 1);
                        v___x_6753_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6753_, 0, v___y_6747_);
                        leanh::lean_ctor_set(v___x_6753_, 1, v___y_6748_);
                        v___x_6754_ = leanh::lean_unsigned_to_nat(1);
                        v___x_6755_ = lean_mk_empty_array_with_capacity(v___x_6754_);
                        v___x_6756_ = lean_array_push(v___x_6755_, v___x_6753_);
                        v___y_6697_ = v___y_6749_;
                        v_varNames_6698_ = v___x_6756_;
                        v_hyps_6699_ = v_a_6752_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___y_6749_);
                        leanh::lean_dec(v___y_6748_);
                        leanh::lean_dec_ref(v___y_6747_);
                        leanh::lean_del_object(v___x_6678_);
                        v_a_6757_ = leanh::lean_ctor_get(v___x_6751_, 0);
                        v_isSharedCheck_6764_ =
                            (!leanh::lean_is_exclusive(v___x_6751_)) as u8;
                        if v_isSharedCheck_6764_ == 0 {
                            v___x_6759_ = v___x_6751_;
                            v_isShared_6760_ = v_isSharedCheck_6764_;
                            state = 16;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6757_);
                            leanh::lean_dec(v___x_6751_);
                            v___x_6759_ = leanh::lean_box(0);
                            v_isShared_6760_ = v_isSharedCheck_6764_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_fst_6713_);
                    v___x_6765_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6765_, 0, v___y_6747_);
                    leanh::lean_ctor_set(v___x_6765_, 1, v___y_6748_);
                    v___x_6766_ = lean_array_push(v_fst_6709_, v___x_6765_);
                    v___y_6697_ = v___y_6749_;
                    v_varNames_6698_ = v___x_6766_;
                    v_hyps_6699_ = v_snd_6714_;
                    state = 5;
                    continue;
                }
            }
            16 => {
                if v_isShared_6760_ == 0 {
                    v___x_6762_ = v___x_6759_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6763_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6763_, 0, v_a_6757_);
                    v___x_6762_ = v_reuseFailAlloc_6763_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6762_;
            }
            18 => {
                if leanh::lean_obj_tag(v_val_6705_) == 0 {
                    v_fvarId_6769_ = leanh::lean_ctor_get(v_val_6705_, 1);
                    leanh::lean_inc(v_fvarId_6769_);
                    v_userName_6770_ = leanh::lean_ctor_get(v_val_6705_, 2);
                    leanh::lean_inc(v_userName_6770_);
                    v_type_6771_ = leanh::lean_ctor_get(v_val_6705_, 3);
                    leanh::lean_inc_ref(v_type_6771_);
                    leanh::lean_dec_ref_known(v_val_6705_, 4);
                    v___x_6772_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_6771_, v___y_6670_);
                    if leanh::lean_obj_tag(v___x_6772_) == 0 {
                        v_a_6773_ = leanh::lean_ctor_get(v___x_6772_, 0);
                        leanh::lean_inc(v_a_6773_);
                        leanh::lean_dec_ref_known(v___x_6772_, 1);
                        v___x_6774_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_userName_6770_,
                                v___x_6674_,
                            );
                        v___x_6775_ =
                            l_Option_instBEq_beq___at___00Lean_Widget_goalToInteractive_spec__1(
                                v_fst_6713_,
                                v___x_6680_,
                            );
                        if v___x_6775_ == 0 {
                            leanh::lean_inc(v_a_6773_);
                            if v_isShared_6708_ == 0 {
                                leanh::lean_ctor_set(v___x_6707_, 0, v_a_6773_);
                                v___x_6777_ = v___x_6707_;
                                state = 19;
                                continue;
                            } else {
                                v_reuseFailAlloc_6779_ =
                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_6779_, 0, v_a_6773_);
                                v___x_6777_ = v_reuseFailAlloc_6779_;
                                state = 19;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_6707_);
                            v___y_6726_ = v_a_6773_;
                            v___y_6727_ = v_fvarId_6769_;
                            v___y_6728_ = v___x_6774_;
                            v___y_6729_ = v___x_6775_;
                            state = 12;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_userName_6770_);
                        leanh::lean_dec(v_fvarId_6769_);
                        leanh::lean_dec(v_snd_6714_);
                        leanh::lean_dec(v_fst_6713_);
                        leanh::lean_dec(v_fst_6709_);
                        leanh::lean_del_object(v___x_6707_);
                        leanh::lean_del_object(v___x_6678_);
                        v_a_6780_ = leanh::lean_ctor_get(v___x_6772_, 0);
                        v_isSharedCheck_6787_ =
                            (!leanh::lean_is_exclusive(v___x_6772_)) as u8;
                        if v_isSharedCheck_6787_ == 0 {
                            v___x_6782_ = v___x_6772_;
                            v_isShared_6783_ = v_isSharedCheck_6787_;
                            state = 20;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6780_);
                            leanh::lean_dec(v___x_6772_);
                            v___x_6782_ = leanh::lean_box(0);
                            v_isShared_6783_ = v_isSharedCheck_6787_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    v_nondep_6788_ = leanh::lean_ctor_get_uint8(
                        v_val_6705_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    );
                    if v_nondep_6788_ == 0 {
                        v_fvarId_6789_ = leanh::lean_ctor_get(v_val_6705_, 1);
                        leanh::lean_inc(v_fvarId_6789_);
                        v_userName_6790_ = leanh::lean_ctor_get(v_val_6705_, 2);
                        leanh::lean_inc(v_userName_6790_);
                        v_type_6791_ = leanh::lean_ctor_get(v_val_6705_, 3);
                        leanh::lean_inc_ref(v_type_6791_);
                        v_value_6792_ = leanh::lean_ctor_get(v_val_6705_, 4);
                        leanh::lean_inc_ref(v_value_6792_);
                        leanh::lean_dec_ref_known(v_val_6705_, 5);
                        v___x_6793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3___lam__0(v_fst_6709_, v_fst_6713_, v_snd_6714_, v___y_6669_, v___y_6670_, v___y_6671_, v___y_6672_);
                        if leanh::lean_obj_tag(v___x_6793_) == 0 {
                            v_a_6794_ = leanh::lean_ctor_get(v___x_6793_, 0);
                            leanh::lean_inc(v_a_6794_);
                            leanh::lean_dec_ref_known(v___x_6793_, 1);
                            v___x_6795_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_6791_, v___y_6670_);
                            if leanh::lean_obj_tag(v___x_6795_) == 0 {
                                v_a_6796_ = leanh::lean_ctor_get(v___x_6795_, 0);
                                leanh::lean_inc(v_a_6796_);
                                leanh::lean_dec_ref_known(v___x_6795_, 1);
                                v___x_6797_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_value_6792_, v___y_6670_);
                                if leanh::lean_obj_tag(v___x_6797_) == 0 {
                                    v_a_6798_ = leanh::lean_ctor_get(v___x_6797_, 0);
                                    leanh::lean_inc(v_a_6798_);
                                    leanh::lean_dec_ref_known(v___x_6797_, 1);
                                    v___x_6799_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_6790_, v___x_6674_);
                                    v___x_6800_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_6800_, 0, v___x_6799_);
                                    leanh::lean_ctor_set(v___x_6800_, 1, v_fvarId_6789_);
                                    v___x_6801_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_6802_ = lean_mk_empty_array_with_capacity(v___x_6801_);
                                    v___x_6803_ = lean_array_push(v___x_6802_, v___x_6800_);
                                    if v_isShared_6708_ == 0 {
                                        leanh::lean_ctor_set(v___x_6707_, 0, v_a_6798_);
                                        v___x_6805_ = v___x_6707_;
                                        state = 22;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_6818_ =
                                            leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_6818_,
                                            0,
                                            v_a_6798_,
                                        );
                                        v___x_6805_ = v_reuseFailAlloc_6818_;
                                        state = 22;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_6796_);
                                    leanh::lean_dec(v_a_6794_);
                                    leanh::lean_dec(v_userName_6790_);
                                    leanh::lean_dec(v_fvarId_6789_);
                                    leanh::lean_del_object(v___x_6707_);
                                    leanh::lean_del_object(v___x_6678_);
                                    v_a_6819_ = leanh::lean_ctor_get(v___x_6797_, 0);
                                    v_isSharedCheck_6826_ =
                                        (!leanh::lean_is_exclusive(v___x_6797_)) as u8;
                                    if v_isSharedCheck_6826_ == 0 {
                                        v___x_6821_ = v___x_6797_;
                                        v_isShared_6822_ = v_isSharedCheck_6826_;
                                        state = 25;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_6819_);
                                        leanh::lean_dec(v___x_6797_);
                                        v___x_6821_ = leanh::lean_box(0);
                                        v_isShared_6822_ = v_isSharedCheck_6826_;
                                        state = 25;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_6794_);
                                leanh::lean_dec_ref(v_value_6792_);
                                leanh::lean_dec(v_userName_6790_);
                                leanh::lean_dec(v_fvarId_6789_);
                                leanh::lean_del_object(v___x_6707_);
                                leanh::lean_del_object(v___x_6678_);
                                v_a_6827_ = leanh::lean_ctor_get(v___x_6795_, 0);
                                v_isSharedCheck_6834_ =
                                    (!leanh::lean_is_exclusive(v___x_6795_)) as u8;
                                if v_isSharedCheck_6834_ == 0 {
                                    v___x_6829_ = v___x_6795_;
                                    v_isShared_6830_ = v_isSharedCheck_6834_;
                                    state = 27;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6827_);
                                    leanh::lean_dec(v___x_6795_);
                                    v___x_6829_ = leanh::lean_box(0);
                                    v_isShared_6830_ = v_isSharedCheck_6834_;
                                    state = 27;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_value_6792_);
                            leanh::lean_dec_ref(v_type_6791_);
                            leanh::lean_dec(v_userName_6790_);
                            leanh::lean_dec(v_fvarId_6789_);
                            leanh::lean_del_object(v___x_6707_);
                            leanh::lean_del_object(v___x_6678_);
                            v_a_6835_ = leanh::lean_ctor_get(v___x_6793_, 0);
                            v_isSharedCheck_6842_ =
                                (!leanh::lean_is_exclusive(v___x_6793_)) as u8;
                            if v_isSharedCheck_6842_ == 0 {
                                v___x_6837_ = v___x_6793_;
                                v_isShared_6838_ = v_isSharedCheck_6842_;
                                state = 29;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6835_);
                                leanh::lean_dec(v___x_6793_);
                                v___x_6837_ = leanh::lean_box(0);
                                v_isShared_6838_ = v_isSharedCheck_6842_;
                                state = 29;
                                continue;
                            }
                        }
                    } else {
                        v_fvarId_6843_ = leanh::lean_ctor_get(v_val_6705_, 1);
                        leanh::lean_inc(v_fvarId_6843_);
                        v_userName_6844_ = leanh::lean_ctor_get(v_val_6705_, 2);
                        leanh::lean_inc(v_userName_6844_);
                        v_type_6845_ = leanh::lean_ctor_get(v_val_6705_, 3);
                        leanh::lean_inc_ref(v_type_6845_);
                        leanh::lean_dec_ref_known(v_val_6705_, 5);
                        v___x_6846_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_6845_, v___y_6670_);
                        if leanh::lean_obj_tag(v___x_6846_) == 0 {
                            v_a_6847_ = leanh::lean_ctor_get(v___x_6846_, 0);
                            leanh::lean_inc(v_a_6847_);
                            leanh::lean_dec_ref_known(v___x_6846_, 1);
                            v___x_6848_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_userName_6844_,
                                    v_nondep_6788_,
                                );
                            v___x_6849_ =
                                l_Option_instBEq_beq___at___00Lean_Widget_goalToInteractive_spec__1(
                                    v_fst_6713_,
                                    v___x_6680_,
                                );
                            if v___x_6849_ == 0 {
                                leanh::lean_inc(v_a_6847_);
                                if v_isShared_6708_ == 0 {
                                    leanh::lean_ctor_set(v___x_6707_, 0, v_a_6847_);
                                    v___x_6851_ = v___x_6707_;
                                    state = 31;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6853_ =
                                        leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6853_,
                                        0,
                                        v_a_6847_,
                                    );
                                    v___x_6851_ = v_reuseFailAlloc_6853_;
                                    state = 31;
                                    continue;
                                }
                            } else {
                                leanh::lean_del_object(v___x_6707_);
                                v___y_6747_ = v___x_6848_;
                                v___y_6748_ = v_fvarId_6843_;
                                v___y_6749_ = v_a_6847_;
                                v___y_6750_ = v___x_6849_;
                                state = 15;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_userName_6844_);
                            leanh::lean_dec(v_fvarId_6843_);
                            leanh::lean_dec(v_snd_6714_);
                            leanh::lean_dec(v_fst_6713_);
                            leanh::lean_dec(v_fst_6709_);
                            leanh::lean_del_object(v___x_6707_);
                            leanh::lean_del_object(v___x_6678_);
                            v_a_6854_ = leanh::lean_ctor_get(v___x_6846_, 0);
                            v_isSharedCheck_6861_ =
                                (!leanh::lean_is_exclusive(v___x_6846_)) as u8;
                            if v_isSharedCheck_6861_ == 0 {
                                v___x_6856_ = v___x_6846_;
                                v_isShared_6857_ = v_isSharedCheck_6861_;
                                state = 32;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6854_);
                                leanh::lean_dec(v___x_6846_);
                                v___x_6856_ = leanh::lean_box(0);
                                v_isShared_6857_ = v_isSharedCheck_6861_;
                                state = 32;
                                continue;
                            }
                        }
                    }
                }
            }
            19 => {
                v___x_6778_ = l_Option_instBEq_beq___at___00Lean_Widget_goalToInteractive_spec__1(
                    v_fst_6713_,
                    v___x_6777_,
                );
                leanh::lean_dec_ref(v___x_6777_);
                v___y_6726_ = v_a_6773_;
                v___y_6727_ = v_fvarId_6769_;
                v___y_6728_ = v___x_6774_;
                v___y_6729_ = v___x_6778_;
                state = 12;
                continue;
            }
            20 => {
                if v_isShared_6783_ == 0 {
                    v___x_6785_ = v___x_6782_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_6786_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6786_, 0, v_a_6780_);
                    v___x_6785_ = v_reuseFailAlloc_6786_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_6785_;
            }
            22 => {
                v___x_6806_ = l_Lean_Widget_addInteractiveHypothesisBundle(
                    v_a_6794_,
                    v___x_6803_,
                    v_a_6796_,
                    v___x_6805_,
                    v___x_6662_,
                    v___y_6669_,
                    v___y_6670_,
                    v___y_6671_,
                    v___y_6672_,
                );
                if leanh::lean_obj_tag(v___x_6806_) == 0 {
                    v_a_6807_ = leanh::lean_ctor_get(v___x_6806_, 0);
                    leanh::lean_inc(v_a_6807_);
                    leanh::lean_dec_ref_known(v___x_6806_, 1);
                    v___x_6808_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6808_, 0, v___x_6680_);
                    leanh::lean_ctor_set(v___x_6808_, 1, v_a_6807_);
                    v___x_6809_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6809_, 0, v___x_6767_);
                    leanh::lean_ctor_set(v___x_6809_, 1, v___x_6808_);
                    v_a_6682_ = v___x_6809_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_6678_);
                    v_a_6810_ = leanh::lean_ctor_get(v___x_6806_, 0);
                    v_isSharedCheck_6817_ = (!leanh::lean_is_exclusive(v___x_6806_)) as u8;
                    if v_isSharedCheck_6817_ == 0 {
                        v___x_6812_ = v___x_6806_;
                        v_isShared_6813_ = v_isSharedCheck_6817_;
                        state = 23;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6810_);
                        leanh::lean_dec(v___x_6806_);
                        v___x_6812_ = leanh::lean_box(0);
                        v_isShared_6813_ = v_isSharedCheck_6817_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_6813_ == 0 {
                    v___x_6815_ = v___x_6812_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_6816_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6816_, 0, v_a_6810_);
                    v___x_6815_ = v_reuseFailAlloc_6816_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_6815_;
            }
            25 => {
                if v_isShared_6822_ == 0 {
                    v___x_6824_ = v___x_6821_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_6825_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6825_, 0, v_a_6819_);
                    v___x_6824_ = v_reuseFailAlloc_6825_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_6824_;
            }
            27 => {
                if v_isShared_6830_ == 0 {
                    v___x_6832_ = v___x_6829_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_6833_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6833_, 0, v_a_6827_);
                    v___x_6832_ = v_reuseFailAlloc_6833_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_6832_;
            }
            29 => {
                if v_isShared_6838_ == 0 {
                    v___x_6840_ = v___x_6837_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_6841_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6841_, 0, v_a_6835_);
                    v___x_6840_ = v_reuseFailAlloc_6841_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_6840_;
            }
            31 => {
                v___x_6852_ = l_Option_instBEq_beq___at___00Lean_Widget_goalToInteractive_spec__1(
                    v_fst_6713_,
                    v___x_6851_,
                );
                leanh::lean_dec_ref(v___x_6851_);
                v___y_6747_ = v___x_6848_;
                v___y_6748_ = v_fvarId_6843_;
                v___y_6749_ = v_a_6847_;
                v___y_6750_ = v___x_6852_;
                state = 15;
                continue;
            }
            32 => {
                if v_isShared_6857_ == 0 {
                    v___x_6859_ = v___x_6856_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_6860_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6860_, 0, v_a_6854_);
                    v___x_6859_ = v_reuseFailAlloc_6860_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_6859_;
            }
            34 => {
                if v___x_6663_ == 0 {
                    v___x_6863_ = l_Lean_LocalDecl_isImplementationDetail(v_val_6705_);
                    if v___x_6863_ == 0 {
                        leanh::lean_del_object(v___x_6716_);
                        leanh::lean_del_object(v___x_6711_);
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_6707_);
                        leanh::lean_dec(v_val_6705_);
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6716_);
                    leanh::lean_del_object(v___x_6711_);
                    state = 18;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4___boxed(
    mut v___x_6871_: *mut leanh::LeanObject,
    mut v___x_6872_: *mut leanh::LeanObject,
    mut v___x_6873_: *mut leanh::LeanObject,
    mut v_as_6874_: *mut leanh::LeanObject,
    mut v_sz_6875_: *mut leanh::LeanObject,
    mut v_i_6876_: *mut leanh::LeanObject,
    mut v_b_6877_: *mut leanh::LeanObject,
    mut v___y_6878_: *mut leanh::LeanObject,
    mut v___y_6879_: *mut leanh::LeanObject,
    mut v___y_6880_: *mut leanh::LeanObject,
    mut v___y_6881_: *mut leanh::LeanObject,
    mut v___y_6882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_12087__boxed_6883_: u8 = 0;
    let mut v___x_12088__boxed_6884_: u8 = 0;
    let mut v___x_12089__boxed_6885_: u8 = 0;
    let mut v_sz_boxed_6886_: usize = 0;
    let mut v_i_boxed_6887_: usize = 0;
    let mut v_res_6888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_12087__boxed_6883_ = (leanh::lean_unbox(v___x_6871_) as u8);
    v___x_12088__boxed_6884_ = (leanh::lean_unbox(v___x_6872_) as u8);
    v___x_12089__boxed_6885_ = (leanh::lean_unbox(v___x_6873_) as u8);
    v_sz_boxed_6886_ = leanh::lean_unbox_usize(v_sz_6875_);
    leanh::lean_dec(v_sz_6875_);
    v_i_boxed_6887_ = leanh::lean_unbox_usize(v_i_6876_);
    leanh::lean_dec(v_i_6876_);
    v_res_6888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4(v___x_12087__boxed_6883_, v___x_12088__boxed_6884_, v___x_12089__boxed_6885_, v_as_6874_, v_sz_boxed_6886_, v_i_boxed_6887_, v_b_6877_, v___y_6878_, v___y_6879_, v___y_6880_, v___y_6881_);
    leanh::lean_dec(v___y_6881_);
    leanh::lean_dec_ref(v___y_6880_);
    leanh::lean_dec(v___y_6879_);
    leanh::lean_dec_ref(v___y_6878_);
    leanh::lean_dec_ref(v_as_6874_);
    return v_res_6888_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2(
    mut v_init_6889_: *mut leanh::LeanObject,
    mut v___x_6890_: u8,
    mut v___x_6891_: u8,
    mut v___x_6892_: u8,
    mut v_n_6893_: *mut leanh::LeanObject,
    mut v_b_6894_: *mut leanh::LeanObject,
    mut v___y_6895_: *mut leanh::LeanObject,
    mut v___y_6896_: *mut leanh::LeanObject,
    mut v___y_6897_: *mut leanh::LeanObject,
    mut v___y_6898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_6900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6903_: usize = 0;
    let mut v___x_6904_: usize = 0;
    let mut v___x_6905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6909_: u8 = 0;
    let mut v_fst_6910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6920_: u8 = 0;
    let mut v_a_6921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6924_: u8 = 0;
    let mut v___x_6926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6928_: u8 = 0;
    let mut v_vs_6929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6932_: usize = 0;
    let mut v___x_6933_: usize = 0;
    let mut v___x_6934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6938_: u8 = 0;
    let mut v_fst_6939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6949_: u8 = 0;
    let mut v_a_6950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6953_: u8 = 0;
    let mut v___x_6955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6957_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_6893_) == 0 {
                    v_cs_6900_ = leanh::lean_ctor_get(v_n_6893_, 0);
                    v___x_6901_ = leanh::lean_box(0);
                    v___x_6902_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6902_, 0, v___x_6901_);
                    leanh::lean_ctor_set(v___x_6902_, 1, v_b_6894_);
                    v_sz_6903_ = lean_array_size(v_cs_6900_);
                    v___x_6904_ = 0usize;
                    v___x_6905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__3(v_init_6889_, v___x_6890_, v___x_6891_, v___x_6892_, v_cs_6900_, v_sz_6903_, v___x_6904_, v___x_6902_, v___y_6895_, v___y_6896_, v___y_6897_, v___y_6898_);
                    if leanh::lean_obj_tag(v___x_6905_) == 0 {
                        v_a_6906_ = leanh::lean_ctor_get(v___x_6905_, 0);
                        v_isSharedCheck_6920_ =
                            (!leanh::lean_is_exclusive(v___x_6905_)) as u8;
                        if v_isSharedCheck_6920_ == 0 {
                            v___x_6908_ = v___x_6905_;
                            v_isShared_6909_ = v_isSharedCheck_6920_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6906_);
                            leanh::lean_dec(v___x_6905_);
                            v___x_6908_ = leanh::lean_box(0);
                            v_isShared_6909_ = v_isSharedCheck_6920_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6921_ = leanh::lean_ctor_get(v___x_6905_, 0);
                        v_isSharedCheck_6928_ =
                            (!leanh::lean_is_exclusive(v___x_6905_)) as u8;
                        if v_isSharedCheck_6928_ == 0 {
                            v___x_6923_ = v___x_6905_;
                            v_isShared_6924_ = v_isSharedCheck_6928_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6921_);
                            leanh::lean_dec(v___x_6905_);
                            v___x_6923_ = leanh::lean_box(0);
                            v_isShared_6924_ = v_isSharedCheck_6928_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_6929_ = leanh::lean_ctor_get(v_n_6893_, 0);
                    v___x_6930_ = leanh::lean_box(0);
                    v___x_6931_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6931_, 0, v___x_6930_);
                    leanh::lean_ctor_set(v___x_6931_, 1, v_b_6894_);
                    v_sz_6932_ = lean_array_size(v_vs_6929_);
                    v___x_6933_ = 0usize;
                    v___x_6934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4(v___x_6890_, v___x_6891_, v___x_6892_, v_vs_6929_, v_sz_6932_, v___x_6933_, v___x_6931_, v___y_6895_, v___y_6896_, v___y_6897_, v___y_6898_);
                    if leanh::lean_obj_tag(v___x_6934_) == 0 {
                        v_a_6935_ = leanh::lean_ctor_get(v___x_6934_, 0);
                        v_isSharedCheck_6949_ =
                            (!leanh::lean_is_exclusive(v___x_6934_)) as u8;
                        if v_isSharedCheck_6949_ == 0 {
                            v___x_6937_ = v___x_6934_;
                            v_isShared_6938_ = v_isSharedCheck_6949_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6935_);
                            leanh::lean_dec(v___x_6934_);
                            v___x_6937_ = leanh::lean_box(0);
                            v_isShared_6938_ = v_isSharedCheck_6949_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_6950_ = leanh::lean_ctor_get(v___x_6934_, 0);
                        v_isSharedCheck_6957_ =
                            (!leanh::lean_is_exclusive(v___x_6934_)) as u8;
                        if v_isSharedCheck_6957_ == 0 {
                            v___x_6952_ = v___x_6934_;
                            v_isShared_6953_ = v_isSharedCheck_6957_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6950_);
                            leanh::lean_dec(v___x_6934_);
                            v___x_6952_ = leanh::lean_box(0);
                            v_isShared_6953_ = v_isSharedCheck_6957_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_6910_ = leanh::lean_ctor_get(v_a_6906_, 0);
                if leanh::lean_obj_tag(v_fst_6910_) == 0 {
                    v_snd_6911_ = leanh::lean_ctor_get(v_a_6906_, 1);
                    leanh::lean_inc(v_snd_6911_);
                    leanh::lean_dec(v_a_6906_);
                    v___x_6912_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6912_, 0, v_snd_6911_);
                    if v_isShared_6909_ == 0 {
                        leanh::lean_ctor_set(v___x_6908_, 0, v___x_6912_);
                        v___x_6914_ = v___x_6908_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6915_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6915_, 0, v___x_6912_);
                        v___x_6914_ = v_reuseFailAlloc_6915_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_6910_);
                    leanh::lean_dec(v_a_6906_);
                    v_val_6916_ = leanh::lean_ctor_get(v_fst_6910_, 0);
                    leanh::lean_inc(v_val_6916_);
                    leanh::lean_dec_ref_known(v_fst_6910_, 1);
                    if v_isShared_6909_ == 0 {
                        leanh::lean_ctor_set(v___x_6908_, 0, v_val_6916_);
                        v___x_6918_ = v___x_6908_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6919_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6919_, 0, v_val_6916_);
                        v___x_6918_ = v_reuseFailAlloc_6919_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6914_;
            }
            3 => {
                return v___x_6918_;
            }
            4 => {
                if v_isShared_6924_ == 0 {
                    v___x_6926_ = v___x_6923_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6927_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6927_, 0, v_a_6921_);
                    v___x_6926_ = v_reuseFailAlloc_6927_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6926_;
            }
            6 => {
                v_fst_6939_ = leanh::lean_ctor_get(v_a_6935_, 0);
                if leanh::lean_obj_tag(v_fst_6939_) == 0 {
                    v_snd_6940_ = leanh::lean_ctor_get(v_a_6935_, 1);
                    leanh::lean_inc(v_snd_6940_);
                    leanh::lean_dec(v_a_6935_);
                    v___x_6941_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6941_, 0, v_snd_6940_);
                    if v_isShared_6938_ == 0 {
                        leanh::lean_ctor_set(v___x_6937_, 0, v___x_6941_);
                        v___x_6943_ = v___x_6937_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6944_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6944_, 0, v___x_6941_);
                        v___x_6943_ = v_reuseFailAlloc_6944_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_6939_);
                    leanh::lean_dec(v_a_6935_);
                    v_val_6945_ = leanh::lean_ctor_get(v_fst_6939_, 0);
                    leanh::lean_inc(v_val_6945_);
                    leanh::lean_dec_ref_known(v_fst_6939_, 1);
                    if v_isShared_6938_ == 0 {
                        leanh::lean_ctor_set(v___x_6937_, 0, v_val_6945_);
                        v___x_6947_ = v___x_6937_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6948_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6948_, 0, v_val_6945_);
                        v___x_6947_ = v_reuseFailAlloc_6948_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_6943_;
            }
            8 => {
                return v___x_6947_;
            }
            9 => {
                if v_isShared_6953_ == 0 {
                    v___x_6955_ = v___x_6952_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6956_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6956_, 0, v_a_6950_);
                    v___x_6955_ = v_reuseFailAlloc_6956_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6955_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__3(
    mut v_init_6958_: *mut leanh::LeanObject,
    mut v___x_6959_: u8,
    mut v___x_6960_: u8,
    mut v___x_6961_: u8,
    mut v_as_6962_: *mut leanh::LeanObject,
    mut v_sz_6963_: usize,
    mut v_i_6964_: usize,
    mut v_b_6965_: *mut leanh::LeanObject,
    mut v___y_6966_: *mut leanh::LeanObject,
    mut v___y_6967_: *mut leanh::LeanObject,
    mut v___y_6968_: *mut leanh::LeanObject,
    mut v___y_6969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6971_: u8 = 0;
    let mut v___x_6972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6976_: u8 = 0;
    let mut v_a_6977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6982_: u8 = 0;
    let mut v___x_6983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6994_: usize = 0;
    let mut v___x_6995_: usize = 0;
    let mut v_reuseFailAlloc_6997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6998_: u8 = 0;
    let mut v_a_6999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7002_: u8 = 0;
    let mut v___x_7004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7006_: u8 = 0;
    let mut v_isSharedCheck_7007_: u8 = 0;
    let mut v_unused_7008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6971_ = lean_usize_dec_lt(v_i_6964_, v_sz_6963_);
                if v___x_6971_ == 0 {
                    v___x_6972_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6972_, 0, v_b_6965_);
                    return v___x_6972_;
                } else {
                    v_snd_6973_ = leanh::lean_ctor_get(v_b_6965_, 1);
                    v_isSharedCheck_7007_ = (!leanh::lean_is_exclusive(v_b_6965_)) as u8;
                    if v_isSharedCheck_7007_ == 0 {
                        v_unused_7008_ = leanh::lean_ctor_get(v_b_6965_, 0);
                        leanh::lean_dec(v_unused_7008_);
                        v___x_6975_ = v_b_6965_;
                        v_isShared_6976_ = v_isSharedCheck_7007_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_6973_);
                        leanh::lean_dec(v_b_6965_);
                        v___x_6975_ = leanh::lean_box(0);
                        v_isShared_6976_ = v_isSharedCheck_7007_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_6977_ = lean_array_uget_borrowed(v_as_6962_, v_i_6964_);
                leanh::lean_inc(v_snd_6973_);
                v___x_6978_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2(v_init_6958_, v___x_6959_, v___x_6960_, v___x_6961_, v_a_6977_, v_snd_6973_, v___y_6966_, v___y_6967_, v___y_6968_, v___y_6969_);
                if leanh::lean_obj_tag(v___x_6978_) == 0 {
                    v_a_6979_ = leanh::lean_ctor_get(v___x_6978_, 0);
                    v_isSharedCheck_6998_ = (!leanh::lean_is_exclusive(v___x_6978_)) as u8;
                    if v_isSharedCheck_6998_ == 0 {
                        v___x_6981_ = v___x_6978_;
                        v_isShared_6982_ = v_isSharedCheck_6998_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6979_);
                        leanh::lean_dec(v___x_6978_);
                        v___x_6981_ = leanh::lean_box(0);
                        v_isShared_6982_ = v_isSharedCheck_6998_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6975_);
                    leanh::lean_dec(v_snd_6973_);
                    v_a_6999_ = leanh::lean_ctor_get(v___x_6978_, 0);
                    v_isSharedCheck_7006_ = (!leanh::lean_is_exclusive(v___x_6978_)) as u8;
                    if v_isSharedCheck_7006_ == 0 {
                        v___x_7001_ = v___x_6978_;
                        v_isShared_7002_ = v_isSharedCheck_7006_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6999_);
                        leanh::lean_dec(v___x_6978_);
                        v___x_7001_ = leanh::lean_box(0);
                        v_isShared_7002_ = v_isSharedCheck_7006_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_6979_) == 0 {
                    v___x_6983_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6983_, 0, v_a_6979_);
                    if v_isShared_6976_ == 0 {
                        leanh::lean_ctor_set(v___x_6975_, 0, v___x_6983_);
                        v___x_6985_ = v___x_6975_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6989_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6989_, 0, v___x_6983_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6989_, 1, v_snd_6973_);
                        v___x_6985_ = v_reuseFailAlloc_6989_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6981_);
                    leanh::lean_dec(v_snd_6973_);
                    v_a_6990_ = leanh::lean_ctor_get(v_a_6979_, 0);
                    leanh::lean_inc(v_a_6990_);
                    leanh::lean_dec_ref_known(v_a_6979_, 1);
                    v___x_6991_ = leanh::lean_box(0);
                    if v_isShared_6976_ == 0 {
                        leanh::lean_ctor_set(v___x_6975_, 1, v_a_6990_);
                        leanh::lean_ctor_set(v___x_6975_, 0, v___x_6991_);
                        v___x_6993_ = v___x_6975_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6997_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6997_, 0, v___x_6991_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6997_, 1, v_a_6990_);
                        v___x_6993_ = v_reuseFailAlloc_6997_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6982_ == 0 {
                    leanh::lean_ctor_set(v___x_6981_, 0, v___x_6985_);
                    v___x_6987_ = v___x_6981_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6988_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6988_, 0, v___x_6985_);
                    v___x_6987_ = v_reuseFailAlloc_6988_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6987_;
            }
            5 => {
                v___x_6994_ = 1usize;
                v___x_6995_ = lean_usize_add(v_i_6964_, v___x_6994_);
                v_i_6964_ = v___x_6995_;
                v_b_6965_ = v___x_6993_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_7002_ == 0 {
                    v___x_7004_ = v___x_7001_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7005_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7005_, 0, v_a_6999_);
                    v___x_7004_ = v_reuseFailAlloc_7005_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7004_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__3___boxed(
    mut v_init_7009_: *mut leanh::LeanObject,
    mut v___x_7010_: *mut leanh::LeanObject,
    mut v___x_7011_: *mut leanh::LeanObject,
    mut v___x_7012_: *mut leanh::LeanObject,
    mut v_as_7013_: *mut leanh::LeanObject,
    mut v_sz_7014_: *mut leanh::LeanObject,
    mut v_i_7015_: *mut leanh::LeanObject,
    mut v_b_7016_: *mut leanh::LeanObject,
    mut v___y_7017_: *mut leanh::LeanObject,
    mut v___y_7018_: *mut leanh::LeanObject,
    mut v___y_7019_: *mut leanh::LeanObject,
    mut v___y_7020_: *mut leanh::LeanObject,
    mut v___y_7021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_12489__boxed_7022_: u8 = 0;
    let mut v___x_12490__boxed_7023_: u8 = 0;
    let mut v___x_12491__boxed_7024_: u8 = 0;
    let mut v_sz_boxed_7025_: usize = 0;
    let mut v_i_boxed_7026_: usize = 0;
    let mut v_res_7027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_12489__boxed_7022_ = (leanh::lean_unbox(v___x_7010_) as u8);
    v___x_12490__boxed_7023_ = (leanh::lean_unbox(v___x_7011_) as u8);
    v___x_12491__boxed_7024_ = (leanh::lean_unbox(v___x_7012_) as u8);
    v_sz_boxed_7025_ = leanh::lean_unbox_usize(v_sz_7014_);
    leanh::lean_dec(v_sz_7014_);
    v_i_boxed_7026_ = leanh::lean_unbox_usize(v_i_7015_);
    leanh::lean_dec(v_i_7015_);
    v_res_7027_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__3(v_init_7009_, v___x_12489__boxed_7022_, v___x_12490__boxed_7023_, v___x_12491__boxed_7024_, v_as_7013_, v_sz_boxed_7025_, v_i_boxed_7026_, v_b_7016_, v___y_7017_, v___y_7018_, v___y_7019_, v___y_7020_);
    leanh::lean_dec(v___y_7020_);
    leanh::lean_dec_ref(v___y_7019_);
    leanh::lean_dec(v___y_7018_);
    leanh::lean_dec_ref(v___y_7017_);
    leanh::lean_dec_ref(v_as_7013_);
    leanh::lean_dec_ref(v_init_7009_);
    return v_res_7027_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2___boxed(
    mut v_init_7028_: *mut leanh::LeanObject,
    mut v___x_7029_: *mut leanh::LeanObject,
    mut v___x_7030_: *mut leanh::LeanObject,
    mut v___x_7031_: *mut leanh::LeanObject,
    mut v_n_7032_: *mut leanh::LeanObject,
    mut v_b_7033_: *mut leanh::LeanObject,
    mut v___y_7034_: *mut leanh::LeanObject,
    mut v___y_7035_: *mut leanh::LeanObject,
    mut v___y_7036_: *mut leanh::LeanObject,
    mut v___y_7037_: *mut leanh::LeanObject,
    mut v___y_7038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_12513__boxed_7039_: u8 = 0;
    let mut v___x_12514__boxed_7040_: u8 = 0;
    let mut v___x_12515__boxed_7041_: u8 = 0;
    let mut v_res_7042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_12513__boxed_7039_ = (leanh::lean_unbox(v___x_7029_) as u8);
    v___x_12514__boxed_7040_ = (leanh::lean_unbox(v___x_7030_) as u8);
    v___x_12515__boxed_7041_ = (leanh::lean_unbox(v___x_7031_) as u8);
    v_res_7042_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2(v_init_7028_, v___x_12513__boxed_7039_, v___x_12514__boxed_7040_, v___x_12515__boxed_7041_, v_n_7032_, v_b_7033_, v___y_7034_, v___y_7035_, v___y_7036_, v___y_7037_);
    leanh::lean_dec(v___y_7037_);
    leanh::lean_dec_ref(v___y_7036_);
    leanh::lean_dec(v___y_7035_);
    leanh::lean_dec_ref(v___y_7034_);
    leanh::lean_dec_ref(v_n_7032_);
    leanh::lean_dec_ref(v_init_7028_);
    return v_res_7042_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3_spec__6(
    mut v___x_7043_: u8,
    mut v___x_7044_: u8,
    mut v___x_7045_: u8,
    mut v_as_7046_: *mut leanh::LeanObject,
    mut v_sz_7047_: usize,
    mut v_i_7048_: usize,
    mut v_b_7049_: *mut leanh::LeanObject,
    mut v___y_7050_: *mut leanh::LeanObject,
    mut v___y_7051_: *mut leanh::LeanObject,
    mut v___y_7052_: *mut leanh::LeanObject,
    mut v___y_7053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7055_: u8 = 0;
    let mut v___x_7056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7060_: u8 = 0;
    let mut v___x_7061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: usize = 0;
    let mut v___x_7067_: usize = 0;
    let mut v_reuseFailAlloc_7069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varNames_7072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_7073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varNames_7079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_7080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7089_: u8 = 0;
    let mut v_fst_7090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7093_: u8 = 0;
    let mut v_fst_7094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7098_: u8 = 0;
    let mut v___x_7101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7110_: u8 = 0;
    let mut v___x_7111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7120_: u8 = 0;
    let mut v___x_7122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7124_: u8 = 0;
    let mut v___x_7125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7131_: u8 = 0;
    let mut v___x_7132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7141_: u8 = 0;
    let mut v___x_7143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7145_: u8 = 0;
    let mut v___x_7146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_7151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7156_: u8 = 0;
    let mut v___x_7158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7159_: u8 = 0;
    let mut v_reuseFailAlloc_7160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7164_: u8 = 0;
    let mut v___x_7166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7168_: u8 = 0;
    let mut v_nondep_7169_: u8 = 0;
    let mut v_fvarId_7170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_7171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7194_: u8 = 0;
    let mut v___x_7196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7198_: u8 = 0;
    let mut v_reuseFailAlloc_7199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7203_: u8 = 0;
    let mut v___x_7205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7207_: u8 = 0;
    let mut v_a_7208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7211_: u8 = 0;
    let mut v___x_7213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7215_: u8 = 0;
    let mut v_a_7216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7219_: u8 = 0;
    let mut v___x_7221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7223_: u8 = 0;
    let mut v_fvarId_7224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_7225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7230_: u8 = 0;
    let mut v___x_7232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7233_: u8 = 0;
    let mut v_reuseFailAlloc_7234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7238_: u8 = 0;
    let mut v___x_7240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7242_: u8 = 0;
    let mut v___x_7244_: u8 = 0;
    let mut v___x_7245_: u8 = 0;
    let mut v_isSharedCheck_7246_: u8 = 0;
    let mut v_isSharedCheck_7247_: u8 = 0;
    let mut v_unused_7248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7249_: u8 = 0;
    let mut v_isSharedCheck_7250_: u8 = 0;
    let mut v_unused_7251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7055_ = lean_usize_dec_lt(v_i_7048_, v_sz_7047_);
                if v___x_7055_ == 0 {
                    v___x_7056_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7056_, 0, v_b_7049_);
                    return v___x_7056_;
                } else {
                    v_snd_7057_ = leanh::lean_ctor_get(v_b_7049_, 1);
                    v_isSharedCheck_7250_ = (!leanh::lean_is_exclusive(v_b_7049_)) as u8;
                    if v_isSharedCheck_7250_ == 0 {
                        v_unused_7251_ = leanh::lean_ctor_get(v_b_7049_, 0);
                        leanh::lean_dec(v_unused_7251_);
                        v___x_7059_ = v_b_7049_;
                        v_isShared_7060_ = v_isSharedCheck_7250_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_7057_);
                        leanh::lean_dec(v_b_7049_);
                        v___x_7059_ = leanh::lean_box(0);
                        v_isShared_7060_ = v_isSharedCheck_7250_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7061_ = leanh::lean_box(0);
                v_a_7084_ = lean_array_uget(v_as_7046_, v_i_7048_);
                if leanh::lean_obj_tag(v_a_7084_) == 0 {
                    v_a_7063_ = v_snd_7057_;
                    state = 2;
                    continue;
                } else {
                    v_snd_7085_ = leanh::lean_ctor_get(v_snd_7057_, 1);
                    leanh::lean_inc(v_snd_7085_);
                    v_val_7086_ = leanh::lean_ctor_get(v_a_7084_, 0);
                    v_isSharedCheck_7249_ = (!leanh::lean_is_exclusive(v_a_7084_)) as u8;
                    if v_isSharedCheck_7249_ == 0 {
                        v___x_7088_ = v_a_7084_;
                        v_isShared_7089_ = v_isSharedCheck_7249_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_7086_);
                        leanh::lean_dec(v_a_7084_);
                        v___x_7088_ = leanh::lean_box(0);
                        v_isShared_7089_ = v_isSharedCheck_7249_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7060_ == 0 {
                    leanh::lean_ctor_set(v___x_7059_, 1, v_a_7063_);
                    leanh::lean_ctor_set(v___x_7059_, 0, v___x_7061_);
                    v___x_7065_ = v___x_7059_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7069_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7069_, 0, v___x_7061_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7069_, 1, v_a_7063_);
                    v___x_7065_ = v_reuseFailAlloc_7069_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7066_ = 1usize;
                v___x_7067_ = lean_usize_add(v_i_7048_, v___x_7066_);
                v_i_7048_ = v___x_7067_;
                v_b_7049_ = v___x_7065_;
                state = 0;
                continue;
            }
            4 => {
                v___x_7074_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7074_, 0, v___y_7071_);
                v___x_7075_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7075_, 0, v___x_7074_);
                leanh::lean_ctor_set(v___x_7075_, 1, v_hyps_7073_);
                v___x_7076_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7076_, 0, v_varNames_7072_);
                leanh::lean_ctor_set(v___x_7076_, 1, v___x_7075_);
                v_a_7063_ = v___x_7076_;
                state = 2;
                continue;
            }
            5 => {
                v___x_7081_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7081_, 0, v___y_7078_);
                v___x_7082_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7082_, 0, v___x_7081_);
                leanh::lean_ctor_set(v___x_7082_, 1, v_hyps_7080_);
                v___x_7083_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7083_, 0, v_varNames_7079_);
                leanh::lean_ctor_set(v___x_7083_, 1, v___x_7082_);
                v_a_7063_ = v___x_7083_;
                state = 2;
                continue;
            }
            6 => {
                v_fst_7090_ = leanh::lean_ctor_get(v_snd_7057_, 0);
                v_isSharedCheck_7247_ = (!leanh::lean_is_exclusive(v_snd_7057_)) as u8;
                if v_isSharedCheck_7247_ == 0 {
                    v_unused_7248_ = leanh::lean_ctor_get(v_snd_7057_, 1);
                    leanh::lean_dec(v_unused_7248_);
                    v___x_7092_ = v_snd_7057_;
                    v_isShared_7093_ = v_isSharedCheck_7247_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_7090_);
                    leanh::lean_dec(v_snd_7057_);
                    v___x_7092_ = leanh::lean_box(0);
                    v_isShared_7093_ = v_isSharedCheck_7247_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_fst_7094_ = leanh::lean_ctor_get(v_snd_7085_, 0);
                v_snd_7095_ = leanh::lean_ctor_get(v_snd_7085_, 1);
                v_isSharedCheck_7246_ = (!leanh::lean_is_exclusive(v_snd_7085_)) as u8;
                if v_isSharedCheck_7246_ == 0 {
                    v___x_7097_ = v_snd_7085_;
                    v_isShared_7098_ = v_isSharedCheck_7246_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_7095_);
                    leanh::lean_inc(v_fst_7094_);
                    leanh::lean_dec(v_snd_7085_);
                    v___x_7097_ = leanh::lean_box(0);
                    v_isShared_7098_ = v_isSharedCheck_7246_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_7148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4_spec__9___closed__0;
                if v___x_7045_ == 0 {
                    v___x_7245_ = l_Lean_LocalDecl_isAuxDecl(v_val_7086_);
                    if v___x_7245_ == 0 {
                        state = 34;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_7088_);
                        leanh::lean_dec(v_val_7086_);
                        state = 9;
                        continue;
                    }
                } else {
                    state = 34;
                    continue;
                }
            }
            9 => {
                if v_isShared_7098_ == 0 {
                    v___x_7101_ = v___x_7097_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7105_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7105_, 0, v_fst_7094_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7105_, 1, v_snd_7095_);
                    v___x_7101_ = v_reuseFailAlloc_7105_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_7093_ == 0 {
                    leanh::lean_ctor_set(v___x_7092_, 1, v___x_7101_);
                    v___x_7103_ = v___x_7092_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7104_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7104_, 0, v_fst_7090_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7104_, 1, v___x_7101_);
                    v___x_7103_ = v_reuseFailAlloc_7104_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_a_7063_ = v___x_7103_;
                state = 2;
                continue;
            }
            12 => {
                if v___y_7110_ == 0 {
                    v___x_7111_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3___lam__0(v_fst_7090_, v_fst_7094_, v_snd_7095_, v___y_7050_, v___y_7051_, v___y_7052_, v___y_7053_);
                    if leanh::lean_obj_tag(v___x_7111_) == 0 {
                        v_a_7112_ = leanh::lean_ctor_get(v___x_7111_, 0);
                        leanh::lean_inc(v_a_7112_);
                        leanh::lean_dec_ref_known(v___x_7111_, 1);
                        v___x_7113_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_7113_, 0, v___y_7108_);
                        leanh::lean_ctor_set(v___x_7113_, 1, v___y_7107_);
                        v___x_7114_ = leanh::lean_unsigned_to_nat(1);
                        v___x_7115_ = lean_mk_empty_array_with_capacity(v___x_7114_);
                        v___x_7116_ = lean_array_push(v___x_7115_, v___x_7113_);
                        v___y_7071_ = v___y_7109_;
                        v_varNames_7072_ = v___x_7116_;
                        v_hyps_7073_ = v_a_7112_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___y_7109_);
                        leanh::lean_dec_ref(v___y_7108_);
                        leanh::lean_dec(v___y_7107_);
                        leanh::lean_del_object(v___x_7059_);
                        v_a_7117_ = leanh::lean_ctor_get(v___x_7111_, 0);
                        v_isSharedCheck_7124_ =
                            (!leanh::lean_is_exclusive(v___x_7111_)) as u8;
                        if v_isSharedCheck_7124_ == 0 {
                            v___x_7119_ = v___x_7111_;
                            v_isShared_7120_ = v_isSharedCheck_7124_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7117_);
                            leanh::lean_dec(v___x_7111_);
                            v___x_7119_ = leanh::lean_box(0);
                            v_isShared_7120_ = v_isSharedCheck_7124_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_fst_7094_);
                    v___x_7125_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7125_, 0, v___y_7108_);
                    leanh::lean_ctor_set(v___x_7125_, 1, v___y_7107_);
                    v___x_7126_ = lean_array_push(v_fst_7090_, v___x_7125_);
                    v___y_7071_ = v___y_7109_;
                    v_varNames_7072_ = v___x_7126_;
                    v_hyps_7073_ = v_snd_7095_;
                    state = 4;
                    continue;
                }
            }
            13 => {
                if v_isShared_7120_ == 0 {
                    v___x_7122_ = v___x_7119_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7123_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7123_, 0, v_a_7117_);
                    v___x_7122_ = v_reuseFailAlloc_7123_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_7122_;
            }
            15 => {
                if v___y_7131_ == 0 {
                    v___x_7132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3___lam__0(v_fst_7090_, v_fst_7094_, v_snd_7095_, v___y_7050_, v___y_7051_, v___y_7052_, v___y_7053_);
                    if leanh::lean_obj_tag(v___x_7132_) == 0 {
                        v_a_7133_ = leanh::lean_ctor_get(v___x_7132_, 0);
                        leanh::lean_inc(v_a_7133_);
                        leanh::lean_dec_ref_known(v___x_7132_, 1);
                        v___x_7134_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_7134_, 0, v___y_7130_);
                        leanh::lean_ctor_set(v___x_7134_, 1, v___y_7128_);
                        v___x_7135_ = leanh::lean_unsigned_to_nat(1);
                        v___x_7136_ = lean_mk_empty_array_with_capacity(v___x_7135_);
                        v___x_7137_ = lean_array_push(v___x_7136_, v___x_7134_);
                        v___y_7078_ = v___y_7129_;
                        v_varNames_7079_ = v___x_7137_;
                        v_hyps_7080_ = v_a_7133_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___y_7130_);
                        leanh::lean_dec_ref(v___y_7129_);
                        leanh::lean_dec(v___y_7128_);
                        leanh::lean_del_object(v___x_7059_);
                        v_a_7138_ = leanh::lean_ctor_get(v___x_7132_, 0);
                        v_isSharedCheck_7145_ =
                            (!leanh::lean_is_exclusive(v___x_7132_)) as u8;
                        if v_isSharedCheck_7145_ == 0 {
                            v___x_7140_ = v___x_7132_;
                            v_isShared_7141_ = v_isSharedCheck_7145_;
                            state = 16;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7138_);
                            leanh::lean_dec(v___x_7132_);
                            v___x_7140_ = leanh::lean_box(0);
                            v_isShared_7141_ = v_isSharedCheck_7145_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_fst_7094_);
                    v___x_7146_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7146_, 0, v___y_7130_);
                    leanh::lean_ctor_set(v___x_7146_, 1, v___y_7128_);
                    v___x_7147_ = lean_array_push(v_fst_7090_, v___x_7146_);
                    v___y_7078_ = v___y_7129_;
                    v_varNames_7079_ = v___x_7147_;
                    v_hyps_7080_ = v_snd_7095_;
                    state = 5;
                    continue;
                }
            }
            16 => {
                if v_isShared_7141_ == 0 {
                    v___x_7143_ = v___x_7140_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_7144_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7144_, 0, v_a_7138_);
                    v___x_7143_ = v_reuseFailAlloc_7144_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_7143_;
            }
            18 => {
                if leanh::lean_obj_tag(v_val_7086_) == 0 {
                    v_fvarId_7150_ = leanh::lean_ctor_get(v_val_7086_, 1);
                    leanh::lean_inc(v_fvarId_7150_);
                    v_userName_7151_ = leanh::lean_ctor_get(v_val_7086_, 2);
                    leanh::lean_inc(v_userName_7151_);
                    v_type_7152_ = leanh::lean_ctor_get(v_val_7086_, 3);
                    leanh::lean_inc_ref(v_type_7152_);
                    leanh::lean_dec_ref_known(v_val_7086_, 4);
                    v___x_7153_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_7152_, v___y_7051_);
                    if leanh::lean_obj_tag(v___x_7153_) == 0 {
                        v_a_7154_ = leanh::lean_ctor_get(v___x_7153_, 0);
                        leanh::lean_inc(v_a_7154_);
                        leanh::lean_dec_ref_known(v___x_7153_, 1);
                        v___x_7155_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_userName_7151_,
                                v___x_7055_,
                            );
                        v___x_7156_ =
                            l_Option_instBEq_beq___at___00Lean_Widget_goalToInteractive_spec__1(
                                v_fst_7094_,
                                v___x_7061_,
                            );
                        if v___x_7156_ == 0 {
                            leanh::lean_inc(v_a_7154_);
                            if v_isShared_7089_ == 0 {
                                leanh::lean_ctor_set(v___x_7088_, 0, v_a_7154_);
                                v___x_7158_ = v___x_7088_;
                                state = 19;
                                continue;
                            } else {
                                v_reuseFailAlloc_7160_ =
                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_7160_, 0, v_a_7154_);
                                v___x_7158_ = v_reuseFailAlloc_7160_;
                                state = 19;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_7088_);
                            v___y_7107_ = v_fvarId_7150_;
                            v___y_7108_ = v___x_7155_;
                            v___y_7109_ = v_a_7154_;
                            v___y_7110_ = v___x_7156_;
                            state = 12;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_userName_7151_);
                        leanh::lean_dec(v_fvarId_7150_);
                        leanh::lean_dec(v_snd_7095_);
                        leanh::lean_dec(v_fst_7094_);
                        leanh::lean_dec(v_fst_7090_);
                        leanh::lean_del_object(v___x_7088_);
                        leanh::lean_del_object(v___x_7059_);
                        v_a_7161_ = leanh::lean_ctor_get(v___x_7153_, 0);
                        v_isSharedCheck_7168_ =
                            (!leanh::lean_is_exclusive(v___x_7153_)) as u8;
                        if v_isSharedCheck_7168_ == 0 {
                            v___x_7163_ = v___x_7153_;
                            v_isShared_7164_ = v_isSharedCheck_7168_;
                            state = 20;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7161_);
                            leanh::lean_dec(v___x_7153_);
                            v___x_7163_ = leanh::lean_box(0);
                            v_isShared_7164_ = v_isSharedCheck_7168_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    v_nondep_7169_ = leanh::lean_ctor_get_uint8(
                        v_val_7086_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    );
                    if v_nondep_7169_ == 0 {
                        v_fvarId_7170_ = leanh::lean_ctor_get(v_val_7086_, 1);
                        leanh::lean_inc(v_fvarId_7170_);
                        v_userName_7171_ = leanh::lean_ctor_get(v_val_7086_, 2);
                        leanh::lean_inc(v_userName_7171_);
                        v_type_7172_ = leanh::lean_ctor_get(v_val_7086_, 3);
                        leanh::lean_inc_ref(v_type_7172_);
                        v_value_7173_ = leanh::lean_ctor_get(v_val_7086_, 4);
                        leanh::lean_inc_ref(v_value_7173_);
                        leanh::lean_dec_ref_known(v_val_7086_, 5);
                        v___x_7174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3___lam__0(v_fst_7090_, v_fst_7094_, v_snd_7095_, v___y_7050_, v___y_7051_, v___y_7052_, v___y_7053_);
                        if leanh::lean_obj_tag(v___x_7174_) == 0 {
                            v_a_7175_ = leanh::lean_ctor_get(v___x_7174_, 0);
                            leanh::lean_inc(v_a_7175_);
                            leanh::lean_dec_ref_known(v___x_7174_, 1);
                            v___x_7176_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_7172_, v___y_7051_);
                            if leanh::lean_obj_tag(v___x_7176_) == 0 {
                                v_a_7177_ = leanh::lean_ctor_get(v___x_7176_, 0);
                                leanh::lean_inc(v_a_7177_);
                                leanh::lean_dec_ref_known(v___x_7176_, 1);
                                v___x_7178_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_value_7173_, v___y_7051_);
                                if leanh::lean_obj_tag(v___x_7178_) == 0 {
                                    v_a_7179_ = leanh::lean_ctor_get(v___x_7178_, 0);
                                    leanh::lean_inc(v_a_7179_);
                                    leanh::lean_dec_ref_known(v___x_7178_, 1);
                                    v___x_7180_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_7171_, v___x_7055_);
                                    v___x_7181_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_7181_, 0, v___x_7180_);
                                    leanh::lean_ctor_set(v___x_7181_, 1, v_fvarId_7170_);
                                    v___x_7182_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_7183_ = lean_mk_empty_array_with_capacity(v___x_7182_);
                                    v___x_7184_ = lean_array_push(v___x_7183_, v___x_7181_);
                                    if v_isShared_7089_ == 0 {
                                        leanh::lean_ctor_set(v___x_7088_, 0, v_a_7179_);
                                        v___x_7186_ = v___x_7088_;
                                        state = 22;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_7199_ =
                                            leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7199_,
                                            0,
                                            v_a_7179_,
                                        );
                                        v___x_7186_ = v_reuseFailAlloc_7199_;
                                        state = 22;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_7177_);
                                    leanh::lean_dec(v_a_7175_);
                                    leanh::lean_dec(v_userName_7171_);
                                    leanh::lean_dec(v_fvarId_7170_);
                                    leanh::lean_del_object(v___x_7088_);
                                    leanh::lean_del_object(v___x_7059_);
                                    v_a_7200_ = leanh::lean_ctor_get(v___x_7178_, 0);
                                    v_isSharedCheck_7207_ =
                                        (!leanh::lean_is_exclusive(v___x_7178_)) as u8;
                                    if v_isSharedCheck_7207_ == 0 {
                                        v___x_7202_ = v___x_7178_;
                                        v_isShared_7203_ = v_isSharedCheck_7207_;
                                        state = 25;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_7200_);
                                        leanh::lean_dec(v___x_7178_);
                                        v___x_7202_ = leanh::lean_box(0);
                                        v_isShared_7203_ = v_isSharedCheck_7207_;
                                        state = 25;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_7175_);
                                leanh::lean_dec_ref(v_value_7173_);
                                leanh::lean_dec(v_userName_7171_);
                                leanh::lean_dec(v_fvarId_7170_);
                                leanh::lean_del_object(v___x_7088_);
                                leanh::lean_del_object(v___x_7059_);
                                v_a_7208_ = leanh::lean_ctor_get(v___x_7176_, 0);
                                v_isSharedCheck_7215_ =
                                    (!leanh::lean_is_exclusive(v___x_7176_)) as u8;
                                if v_isSharedCheck_7215_ == 0 {
                                    v___x_7210_ = v___x_7176_;
                                    v_isShared_7211_ = v_isSharedCheck_7215_;
                                    state = 27;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_7208_);
                                    leanh::lean_dec(v___x_7176_);
                                    v___x_7210_ = leanh::lean_box(0);
                                    v_isShared_7211_ = v_isSharedCheck_7215_;
                                    state = 27;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_value_7173_);
                            leanh::lean_dec_ref(v_type_7172_);
                            leanh::lean_dec(v_userName_7171_);
                            leanh::lean_dec(v_fvarId_7170_);
                            leanh::lean_del_object(v___x_7088_);
                            leanh::lean_del_object(v___x_7059_);
                            v_a_7216_ = leanh::lean_ctor_get(v___x_7174_, 0);
                            v_isSharedCheck_7223_ =
                                (!leanh::lean_is_exclusive(v___x_7174_)) as u8;
                            if v_isSharedCheck_7223_ == 0 {
                                v___x_7218_ = v___x_7174_;
                                v_isShared_7219_ = v_isSharedCheck_7223_;
                                state = 29;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7216_);
                                leanh::lean_dec(v___x_7174_);
                                v___x_7218_ = leanh::lean_box(0);
                                v_isShared_7219_ = v_isSharedCheck_7223_;
                                state = 29;
                                continue;
                            }
                        }
                    } else {
                        v_fvarId_7224_ = leanh::lean_ctor_get(v_val_7086_, 1);
                        leanh::lean_inc(v_fvarId_7224_);
                        v_userName_7225_ = leanh::lean_ctor_get(v_val_7086_, 2);
                        leanh::lean_inc(v_userName_7225_);
                        v_type_7226_ = leanh::lean_ctor_get(v_val_7086_, 3);
                        leanh::lean_inc_ref(v_type_7226_);
                        leanh::lean_dec_ref_known(v_val_7086_, 5);
                        v___x_7227_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_7226_, v___y_7051_);
                        if leanh::lean_obj_tag(v___x_7227_) == 0 {
                            v_a_7228_ = leanh::lean_ctor_get(v___x_7227_, 0);
                            leanh::lean_inc(v_a_7228_);
                            leanh::lean_dec_ref_known(v___x_7227_, 1);
                            v___x_7229_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_userName_7225_,
                                    v_nondep_7169_,
                                );
                            v___x_7230_ =
                                l_Option_instBEq_beq___at___00Lean_Widget_goalToInteractive_spec__1(
                                    v_fst_7094_,
                                    v___x_7061_,
                                );
                            if v___x_7230_ == 0 {
                                leanh::lean_inc(v_a_7228_);
                                if v_isShared_7089_ == 0 {
                                    leanh::lean_ctor_set(v___x_7088_, 0, v_a_7228_);
                                    v___x_7232_ = v___x_7088_;
                                    state = 31;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_7234_ =
                                        leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7234_,
                                        0,
                                        v_a_7228_,
                                    );
                                    v___x_7232_ = v_reuseFailAlloc_7234_;
                                    state = 31;
                                    continue;
                                }
                            } else {
                                leanh::lean_del_object(v___x_7088_);
                                v___y_7128_ = v_fvarId_7224_;
                                v___y_7129_ = v_a_7228_;
                                v___y_7130_ = v___x_7229_;
                                v___y_7131_ = v___x_7230_;
                                state = 15;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_userName_7225_);
                            leanh::lean_dec(v_fvarId_7224_);
                            leanh::lean_dec(v_snd_7095_);
                            leanh::lean_dec(v_fst_7094_);
                            leanh::lean_dec(v_fst_7090_);
                            leanh::lean_del_object(v___x_7088_);
                            leanh::lean_del_object(v___x_7059_);
                            v_a_7235_ = leanh::lean_ctor_get(v___x_7227_, 0);
                            v_isSharedCheck_7242_ =
                                (!leanh::lean_is_exclusive(v___x_7227_)) as u8;
                            if v_isSharedCheck_7242_ == 0 {
                                v___x_7237_ = v___x_7227_;
                                v_isShared_7238_ = v_isSharedCheck_7242_;
                                state = 32;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7235_);
                                leanh::lean_dec(v___x_7227_);
                                v___x_7237_ = leanh::lean_box(0);
                                v_isShared_7238_ = v_isSharedCheck_7242_;
                                state = 32;
                                continue;
                            }
                        }
                    }
                }
            }
            19 => {
                v___x_7159_ = l_Option_instBEq_beq___at___00Lean_Widget_goalToInteractive_spec__1(
                    v_fst_7094_,
                    v___x_7158_,
                );
                leanh::lean_dec_ref(v___x_7158_);
                v___y_7107_ = v_fvarId_7150_;
                v___y_7108_ = v___x_7155_;
                v___y_7109_ = v_a_7154_;
                v___y_7110_ = v___x_7159_;
                state = 12;
                continue;
            }
            20 => {
                if v_isShared_7164_ == 0 {
                    v___x_7166_ = v___x_7163_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_7167_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7167_, 0, v_a_7161_);
                    v___x_7166_ = v_reuseFailAlloc_7167_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_7166_;
            }
            22 => {
                v___x_7187_ = l_Lean_Widget_addInteractiveHypothesisBundle(
                    v_a_7175_,
                    v___x_7184_,
                    v_a_7177_,
                    v___x_7186_,
                    v___x_7043_,
                    v___y_7050_,
                    v___y_7051_,
                    v___y_7052_,
                    v___y_7053_,
                );
                if leanh::lean_obj_tag(v___x_7187_) == 0 {
                    v_a_7188_ = leanh::lean_ctor_get(v___x_7187_, 0);
                    leanh::lean_inc(v_a_7188_);
                    leanh::lean_dec_ref_known(v___x_7187_, 1);
                    v___x_7189_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7189_, 0, v___x_7061_);
                    leanh::lean_ctor_set(v___x_7189_, 1, v_a_7188_);
                    v___x_7190_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7190_, 0, v___x_7148_);
                    leanh::lean_ctor_set(v___x_7190_, 1, v___x_7189_);
                    v_a_7063_ = v___x_7190_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_7059_);
                    v_a_7191_ = leanh::lean_ctor_get(v___x_7187_, 0);
                    v_isSharedCheck_7198_ = (!leanh::lean_is_exclusive(v___x_7187_)) as u8;
                    if v_isSharedCheck_7198_ == 0 {
                        v___x_7193_ = v___x_7187_;
                        v_isShared_7194_ = v_isSharedCheck_7198_;
                        state = 23;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7191_);
                        leanh::lean_dec(v___x_7187_);
                        v___x_7193_ = leanh::lean_box(0);
                        v_isShared_7194_ = v_isSharedCheck_7198_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_7194_ == 0 {
                    v___x_7196_ = v___x_7193_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_7197_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7197_, 0, v_a_7191_);
                    v___x_7196_ = v_reuseFailAlloc_7197_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_7196_;
            }
            25 => {
                if v_isShared_7203_ == 0 {
                    v___x_7205_ = v___x_7202_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_7206_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7206_, 0, v_a_7200_);
                    v___x_7205_ = v_reuseFailAlloc_7206_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_7205_;
            }
            27 => {
                if v_isShared_7211_ == 0 {
                    v___x_7213_ = v___x_7210_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_7214_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7214_, 0, v_a_7208_);
                    v___x_7213_ = v_reuseFailAlloc_7214_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_7213_;
            }
            29 => {
                if v_isShared_7219_ == 0 {
                    v___x_7221_ = v___x_7218_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_7222_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7222_, 0, v_a_7216_);
                    v___x_7221_ = v_reuseFailAlloc_7222_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_7221_;
            }
            31 => {
                v___x_7233_ = l_Option_instBEq_beq___at___00Lean_Widget_goalToInteractive_spec__1(
                    v_fst_7094_,
                    v___x_7232_,
                );
                leanh::lean_dec_ref(v___x_7232_);
                v___y_7128_ = v_fvarId_7224_;
                v___y_7129_ = v_a_7228_;
                v___y_7130_ = v___x_7229_;
                v___y_7131_ = v___x_7233_;
                state = 15;
                continue;
            }
            32 => {
                if v_isShared_7238_ == 0 {
                    v___x_7240_ = v___x_7237_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_7241_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7241_, 0, v_a_7235_);
                    v___x_7240_ = v_reuseFailAlloc_7241_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_7240_;
            }
            34 => {
                if v___x_7044_ == 0 {
                    v___x_7244_ = l_Lean_LocalDecl_isImplementationDetail(v_val_7086_);
                    if v___x_7244_ == 0 {
                        leanh::lean_del_object(v___x_7097_);
                        leanh::lean_del_object(v___x_7092_);
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_7088_);
                        leanh::lean_dec(v_val_7086_);
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_7097_);
                    leanh::lean_del_object(v___x_7092_);
                    state = 18;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3_spec__6___boxed(
    mut v___x_7252_: *mut leanh::LeanObject,
    mut v___x_7253_: *mut leanh::LeanObject,
    mut v___x_7254_: *mut leanh::LeanObject,
    mut v_as_7255_: *mut leanh::LeanObject,
    mut v_sz_7256_: *mut leanh::LeanObject,
    mut v_i_7257_: *mut leanh::LeanObject,
    mut v_b_7258_: *mut leanh::LeanObject,
    mut v___y_7259_: *mut leanh::LeanObject,
    mut v___y_7260_: *mut leanh::LeanObject,
    mut v___y_7261_: *mut leanh::LeanObject,
    mut v___y_7262_: *mut leanh::LeanObject,
    mut v___y_7263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_12716__boxed_7264_: u8 = 0;
    let mut v___x_12717__boxed_7265_: u8 = 0;
    let mut v___x_12718__boxed_7266_: u8 = 0;
    let mut v_sz_boxed_7267_: usize = 0;
    let mut v_i_boxed_7268_: usize = 0;
    let mut v_res_7269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_12716__boxed_7264_ = (leanh::lean_unbox(v___x_7252_) as u8);
    v___x_12717__boxed_7265_ = (leanh::lean_unbox(v___x_7253_) as u8);
    v___x_12718__boxed_7266_ = (leanh::lean_unbox(v___x_7254_) as u8);
    v_sz_boxed_7267_ = leanh::lean_unbox_usize(v_sz_7256_);
    leanh::lean_dec(v_sz_7256_);
    v_i_boxed_7268_ = leanh::lean_unbox_usize(v_i_7257_);
    leanh::lean_dec(v_i_7257_);
    v_res_7269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3_spec__6(v___x_12716__boxed_7264_, v___x_12717__boxed_7265_, v___x_12718__boxed_7266_, v_as_7255_, v_sz_boxed_7267_, v_i_boxed_7268_, v_b_7258_, v___y_7259_, v___y_7260_, v___y_7261_, v___y_7262_);
    leanh::lean_dec(v___y_7262_);
    leanh::lean_dec_ref(v___y_7261_);
    leanh::lean_dec(v___y_7260_);
    leanh::lean_dec_ref(v___y_7259_);
    leanh::lean_dec_ref(v_as_7255_);
    return v_res_7269_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3(
    mut v___x_7270_: u8,
    mut v___x_7271_: u8,
    mut v___x_7272_: u8,
    mut v_as_7273_: *mut leanh::LeanObject,
    mut v_sz_7274_: usize,
    mut v_i_7275_: usize,
    mut v_b_7276_: *mut leanh::LeanObject,
    mut v___y_7277_: *mut leanh::LeanObject,
    mut v___y_7278_: *mut leanh::LeanObject,
    mut v___y_7279_: *mut leanh::LeanObject,
    mut v___y_7280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7282_: u8 = 0;
    let mut v___x_7283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7287_: u8 = 0;
    let mut v___x_7288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7293_: usize = 0;
    let mut v___x_7294_: usize = 0;
    let mut v___x_7295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varNames_7299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_7300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varNames_7306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_7307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7316_: u8 = 0;
    let mut v_fst_7317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7320_: u8 = 0;
    let mut v_fst_7321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7325_: u8 = 0;
    let mut v___x_7328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7337_: u8 = 0;
    let mut v___x_7338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7347_: u8 = 0;
    let mut v___x_7349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7351_: u8 = 0;
    let mut v___x_7352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7358_: u8 = 0;
    let mut v___x_7359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7368_: u8 = 0;
    let mut v___x_7370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7372_: u8 = 0;
    let mut v___x_7373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_7378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7383_: u8 = 0;
    let mut v___x_7385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7386_: u8 = 0;
    let mut v_reuseFailAlloc_7387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7391_: u8 = 0;
    let mut v___x_7393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7395_: u8 = 0;
    let mut v_nondep_7396_: u8 = 0;
    let mut v_fvarId_7397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_7398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7421_: u8 = 0;
    let mut v___x_7423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7425_: u8 = 0;
    let mut v_reuseFailAlloc_7426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7430_: u8 = 0;
    let mut v___x_7432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7434_: u8 = 0;
    let mut v_a_7435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7438_: u8 = 0;
    let mut v___x_7440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7442_: u8 = 0;
    let mut v_a_7443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7446_: u8 = 0;
    let mut v___x_7448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7450_: u8 = 0;
    let mut v_fvarId_7451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_7452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7457_: u8 = 0;
    let mut v___x_7459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7460_: u8 = 0;
    let mut v_reuseFailAlloc_7461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7465_: u8 = 0;
    let mut v___x_7467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7469_: u8 = 0;
    let mut v___x_7471_: u8 = 0;
    let mut v___x_7472_: u8 = 0;
    let mut v_isSharedCheck_7473_: u8 = 0;
    let mut v_isSharedCheck_7474_: u8 = 0;
    let mut v_unused_7475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7476_: u8 = 0;
    let mut v_isSharedCheck_7477_: u8 = 0;
    let mut v_unused_7478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7282_ = lean_usize_dec_lt(v_i_7275_, v_sz_7274_);
                if v___x_7282_ == 0 {
                    v___x_7283_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7283_, 0, v_b_7276_);
                    return v___x_7283_;
                } else {
                    v_snd_7284_ = leanh::lean_ctor_get(v_b_7276_, 1);
                    v_isSharedCheck_7477_ = (!leanh::lean_is_exclusive(v_b_7276_)) as u8;
                    if v_isSharedCheck_7477_ == 0 {
                        v_unused_7478_ = leanh::lean_ctor_get(v_b_7276_, 0);
                        leanh::lean_dec(v_unused_7478_);
                        v___x_7286_ = v_b_7276_;
                        v_isShared_7287_ = v_isSharedCheck_7477_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_7284_);
                        leanh::lean_dec(v_b_7276_);
                        v___x_7286_ = leanh::lean_box(0);
                        v_isShared_7287_ = v_isSharedCheck_7477_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7288_ = leanh::lean_box(0);
                v_a_7311_ = lean_array_uget(v_as_7273_, v_i_7275_);
                if leanh::lean_obj_tag(v_a_7311_) == 0 {
                    v_a_7290_ = v_snd_7284_;
                    state = 2;
                    continue;
                } else {
                    v_snd_7312_ = leanh::lean_ctor_get(v_snd_7284_, 1);
                    leanh::lean_inc(v_snd_7312_);
                    v_val_7313_ = leanh::lean_ctor_get(v_a_7311_, 0);
                    v_isSharedCheck_7476_ = (!leanh::lean_is_exclusive(v_a_7311_)) as u8;
                    if v_isSharedCheck_7476_ == 0 {
                        v___x_7315_ = v_a_7311_;
                        v_isShared_7316_ = v_isSharedCheck_7476_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_7313_);
                        leanh::lean_dec(v_a_7311_);
                        v___x_7315_ = leanh::lean_box(0);
                        v_isShared_7316_ = v_isSharedCheck_7476_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7287_ == 0 {
                    leanh::lean_ctor_set(v___x_7286_, 1, v_a_7290_);
                    leanh::lean_ctor_set(v___x_7286_, 0, v___x_7288_);
                    v___x_7292_ = v___x_7286_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7296_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7296_, 0, v___x_7288_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7296_, 1, v_a_7290_);
                    v___x_7292_ = v_reuseFailAlloc_7296_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7293_ = 1usize;
                v___x_7294_ = lean_usize_add(v_i_7275_, v___x_7293_);
                v___x_7295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3_spec__6(v___x_7270_, v___x_7271_, v___x_7272_, v_as_7273_, v_sz_7274_, v___x_7294_, v___x_7292_, v___y_7277_, v___y_7278_, v___y_7279_, v___y_7280_);
                return v___x_7295_;
            }
            4 => {
                v___x_7301_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7301_, 0, v___y_7298_);
                v___x_7302_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7302_, 0, v___x_7301_);
                leanh::lean_ctor_set(v___x_7302_, 1, v_hyps_7300_);
                v___x_7303_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7303_, 0, v_varNames_7299_);
                leanh::lean_ctor_set(v___x_7303_, 1, v___x_7302_);
                v_a_7290_ = v___x_7303_;
                state = 2;
                continue;
            }
            5 => {
                v___x_7308_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7308_, 0, v___y_7305_);
                v___x_7309_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7309_, 0, v___x_7308_);
                leanh::lean_ctor_set(v___x_7309_, 1, v_hyps_7307_);
                v___x_7310_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7310_, 0, v_varNames_7306_);
                leanh::lean_ctor_set(v___x_7310_, 1, v___x_7309_);
                v_a_7290_ = v___x_7310_;
                state = 2;
                continue;
            }
            6 => {
                v_fst_7317_ = leanh::lean_ctor_get(v_snd_7284_, 0);
                v_isSharedCheck_7474_ = (!leanh::lean_is_exclusive(v_snd_7284_)) as u8;
                if v_isSharedCheck_7474_ == 0 {
                    v_unused_7475_ = leanh::lean_ctor_get(v_snd_7284_, 1);
                    leanh::lean_dec(v_unused_7475_);
                    v___x_7319_ = v_snd_7284_;
                    v_isShared_7320_ = v_isSharedCheck_7474_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_7317_);
                    leanh::lean_dec(v_snd_7284_);
                    v___x_7319_ = leanh::lean_box(0);
                    v_isShared_7320_ = v_isSharedCheck_7474_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_fst_7321_ = leanh::lean_ctor_get(v_snd_7312_, 0);
                v_snd_7322_ = leanh::lean_ctor_get(v_snd_7312_, 1);
                v_isSharedCheck_7473_ = (!leanh::lean_is_exclusive(v_snd_7312_)) as u8;
                if v_isSharedCheck_7473_ == 0 {
                    v___x_7324_ = v_snd_7312_;
                    v_isShared_7325_ = v_isSharedCheck_7473_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_7322_);
                    leanh::lean_inc(v_fst_7321_);
                    leanh::lean_dec(v_snd_7312_);
                    v___x_7324_ = leanh::lean_box(0);
                    v_isShared_7325_ = v_isSharedCheck_7473_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_7375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4_spec__9___closed__0;
                if v___x_7272_ == 0 {
                    v___x_7472_ = l_Lean_LocalDecl_isAuxDecl(v_val_7313_);
                    if v___x_7472_ == 0 {
                        state = 34;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_7315_);
                        leanh::lean_dec(v_val_7313_);
                        state = 9;
                        continue;
                    }
                } else {
                    state = 34;
                    continue;
                }
            }
            9 => {
                if v_isShared_7325_ == 0 {
                    v___x_7328_ = v___x_7324_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7332_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7332_, 0, v_fst_7321_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7332_, 1, v_snd_7322_);
                    v___x_7328_ = v_reuseFailAlloc_7332_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_7320_ == 0 {
                    leanh::lean_ctor_set(v___x_7319_, 1, v___x_7328_);
                    v___x_7330_ = v___x_7319_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7331_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7331_, 0, v_fst_7317_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7331_, 1, v___x_7328_);
                    v___x_7330_ = v_reuseFailAlloc_7331_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_a_7290_ = v___x_7330_;
                state = 2;
                continue;
            }
            12 => {
                if v___y_7337_ == 0 {
                    v___x_7338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3___lam__0(v_fst_7317_, v_fst_7321_, v_snd_7322_, v___y_7277_, v___y_7278_, v___y_7279_, v___y_7280_);
                    if leanh::lean_obj_tag(v___x_7338_) == 0 {
                        v_a_7339_ = leanh::lean_ctor_get(v___x_7338_, 0);
                        leanh::lean_inc(v_a_7339_);
                        leanh::lean_dec_ref_known(v___x_7338_, 1);
                        v___x_7340_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_7340_, 0, v___y_7335_);
                        leanh::lean_ctor_set(v___x_7340_, 1, v___y_7334_);
                        v___x_7341_ = leanh::lean_unsigned_to_nat(1);
                        v___x_7342_ = lean_mk_empty_array_with_capacity(v___x_7341_);
                        v___x_7343_ = lean_array_push(v___x_7342_, v___x_7340_);
                        v___y_7298_ = v___y_7336_;
                        v_varNames_7299_ = v___x_7343_;
                        v_hyps_7300_ = v_a_7339_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___y_7336_);
                        leanh::lean_dec_ref(v___y_7335_);
                        leanh::lean_dec(v___y_7334_);
                        leanh::lean_del_object(v___x_7286_);
                        v_a_7344_ = leanh::lean_ctor_get(v___x_7338_, 0);
                        v_isSharedCheck_7351_ =
                            (!leanh::lean_is_exclusive(v___x_7338_)) as u8;
                        if v_isSharedCheck_7351_ == 0 {
                            v___x_7346_ = v___x_7338_;
                            v_isShared_7347_ = v_isSharedCheck_7351_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7344_);
                            leanh::lean_dec(v___x_7338_);
                            v___x_7346_ = leanh::lean_box(0);
                            v_isShared_7347_ = v_isSharedCheck_7351_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_fst_7321_);
                    v___x_7352_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7352_, 0, v___y_7335_);
                    leanh::lean_ctor_set(v___x_7352_, 1, v___y_7334_);
                    v___x_7353_ = lean_array_push(v_fst_7317_, v___x_7352_);
                    v___y_7298_ = v___y_7336_;
                    v_varNames_7299_ = v___x_7353_;
                    v_hyps_7300_ = v_snd_7322_;
                    state = 4;
                    continue;
                }
            }
            13 => {
                if v_isShared_7347_ == 0 {
                    v___x_7349_ = v___x_7346_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7350_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7350_, 0, v_a_7344_);
                    v___x_7349_ = v_reuseFailAlloc_7350_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_7349_;
            }
            15 => {
                if v___y_7358_ == 0 {
                    v___x_7359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3___lam__0(v_fst_7317_, v_fst_7321_, v_snd_7322_, v___y_7277_, v___y_7278_, v___y_7279_, v___y_7280_);
                    if leanh::lean_obj_tag(v___x_7359_) == 0 {
                        v_a_7360_ = leanh::lean_ctor_get(v___x_7359_, 0);
                        leanh::lean_inc(v_a_7360_);
                        leanh::lean_dec_ref_known(v___x_7359_, 1);
                        v___x_7361_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_7361_, 0, v___y_7357_);
                        leanh::lean_ctor_set(v___x_7361_, 1, v___y_7355_);
                        v___x_7362_ = leanh::lean_unsigned_to_nat(1);
                        v___x_7363_ = lean_mk_empty_array_with_capacity(v___x_7362_);
                        v___x_7364_ = lean_array_push(v___x_7363_, v___x_7361_);
                        v___y_7305_ = v___y_7356_;
                        v_varNames_7306_ = v___x_7364_;
                        v_hyps_7307_ = v_a_7360_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___y_7357_);
                        leanh::lean_dec_ref(v___y_7356_);
                        leanh::lean_dec(v___y_7355_);
                        leanh::lean_del_object(v___x_7286_);
                        v_a_7365_ = leanh::lean_ctor_get(v___x_7359_, 0);
                        v_isSharedCheck_7372_ =
                            (!leanh::lean_is_exclusive(v___x_7359_)) as u8;
                        if v_isSharedCheck_7372_ == 0 {
                            v___x_7367_ = v___x_7359_;
                            v_isShared_7368_ = v_isSharedCheck_7372_;
                            state = 16;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7365_);
                            leanh::lean_dec(v___x_7359_);
                            v___x_7367_ = leanh::lean_box(0);
                            v_isShared_7368_ = v_isSharedCheck_7372_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_fst_7321_);
                    v___x_7373_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7373_, 0, v___y_7357_);
                    leanh::lean_ctor_set(v___x_7373_, 1, v___y_7355_);
                    v___x_7374_ = lean_array_push(v_fst_7317_, v___x_7373_);
                    v___y_7305_ = v___y_7356_;
                    v_varNames_7306_ = v___x_7374_;
                    v_hyps_7307_ = v_snd_7322_;
                    state = 5;
                    continue;
                }
            }
            16 => {
                if v_isShared_7368_ == 0 {
                    v___x_7370_ = v___x_7367_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_7371_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7371_, 0, v_a_7365_);
                    v___x_7370_ = v_reuseFailAlloc_7371_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_7370_;
            }
            18 => {
                if leanh::lean_obj_tag(v_val_7313_) == 0 {
                    v_fvarId_7377_ = leanh::lean_ctor_get(v_val_7313_, 1);
                    leanh::lean_inc(v_fvarId_7377_);
                    v_userName_7378_ = leanh::lean_ctor_get(v_val_7313_, 2);
                    leanh::lean_inc(v_userName_7378_);
                    v_type_7379_ = leanh::lean_ctor_get(v_val_7313_, 3);
                    leanh::lean_inc_ref(v_type_7379_);
                    leanh::lean_dec_ref_known(v_val_7313_, 4);
                    v___x_7380_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_7379_, v___y_7278_);
                    if leanh::lean_obj_tag(v___x_7380_) == 0 {
                        v_a_7381_ = leanh::lean_ctor_get(v___x_7380_, 0);
                        leanh::lean_inc(v_a_7381_);
                        leanh::lean_dec_ref_known(v___x_7380_, 1);
                        v___x_7382_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_userName_7378_,
                                v___x_7282_,
                            );
                        v___x_7383_ =
                            l_Option_instBEq_beq___at___00Lean_Widget_goalToInteractive_spec__1(
                                v_fst_7321_,
                                v___x_7288_,
                            );
                        if v___x_7383_ == 0 {
                            leanh::lean_inc(v_a_7381_);
                            if v_isShared_7316_ == 0 {
                                leanh::lean_ctor_set(v___x_7315_, 0, v_a_7381_);
                                v___x_7385_ = v___x_7315_;
                                state = 19;
                                continue;
                            } else {
                                v_reuseFailAlloc_7387_ =
                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_7387_, 0, v_a_7381_);
                                v___x_7385_ = v_reuseFailAlloc_7387_;
                                state = 19;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_7315_);
                            v___y_7334_ = v_fvarId_7377_;
                            v___y_7335_ = v___x_7382_;
                            v___y_7336_ = v_a_7381_;
                            v___y_7337_ = v___x_7383_;
                            state = 12;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_userName_7378_);
                        leanh::lean_dec(v_fvarId_7377_);
                        leanh::lean_dec(v_snd_7322_);
                        leanh::lean_dec(v_fst_7321_);
                        leanh::lean_dec(v_fst_7317_);
                        leanh::lean_del_object(v___x_7315_);
                        leanh::lean_del_object(v___x_7286_);
                        v_a_7388_ = leanh::lean_ctor_get(v___x_7380_, 0);
                        v_isSharedCheck_7395_ =
                            (!leanh::lean_is_exclusive(v___x_7380_)) as u8;
                        if v_isSharedCheck_7395_ == 0 {
                            v___x_7390_ = v___x_7380_;
                            v_isShared_7391_ = v_isSharedCheck_7395_;
                            state = 20;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7388_);
                            leanh::lean_dec(v___x_7380_);
                            v___x_7390_ = leanh::lean_box(0);
                            v_isShared_7391_ = v_isSharedCheck_7395_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    v_nondep_7396_ = leanh::lean_ctor_get_uint8(
                        v_val_7313_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    );
                    if v_nondep_7396_ == 0 {
                        v_fvarId_7397_ = leanh::lean_ctor_get(v_val_7313_, 1);
                        leanh::lean_inc(v_fvarId_7397_);
                        v_userName_7398_ = leanh::lean_ctor_get(v_val_7313_, 2);
                        leanh::lean_inc(v_userName_7398_);
                        v_type_7399_ = leanh::lean_ctor_get(v_val_7313_, 3);
                        leanh::lean_inc_ref(v_type_7399_);
                        v_value_7400_ = leanh::lean_ctor_get(v_val_7313_, 4);
                        leanh::lean_inc_ref(v_value_7400_);
                        leanh::lean_dec_ref_known(v_val_7313_, 5);
                        v___x_7401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3___lam__0(v_fst_7317_, v_fst_7321_, v_snd_7322_, v___y_7277_, v___y_7278_, v___y_7279_, v___y_7280_);
                        if leanh::lean_obj_tag(v___x_7401_) == 0 {
                            v_a_7402_ = leanh::lean_ctor_get(v___x_7401_, 0);
                            leanh::lean_inc(v_a_7402_);
                            leanh::lean_dec_ref_known(v___x_7401_, 1);
                            v___x_7403_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_7399_, v___y_7278_);
                            if leanh::lean_obj_tag(v___x_7403_) == 0 {
                                v_a_7404_ = leanh::lean_ctor_get(v___x_7403_, 0);
                                leanh::lean_inc(v_a_7404_);
                                leanh::lean_dec_ref_known(v___x_7403_, 1);
                                v___x_7405_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_value_7400_, v___y_7278_);
                                if leanh::lean_obj_tag(v___x_7405_) == 0 {
                                    v_a_7406_ = leanh::lean_ctor_get(v___x_7405_, 0);
                                    leanh::lean_inc(v_a_7406_);
                                    leanh::lean_dec_ref_known(v___x_7405_, 1);
                                    v___x_7407_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_7398_, v___x_7282_);
                                    v___x_7408_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_7408_, 0, v___x_7407_);
                                    leanh::lean_ctor_set(v___x_7408_, 1, v_fvarId_7397_);
                                    v___x_7409_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_7410_ = lean_mk_empty_array_with_capacity(v___x_7409_);
                                    v___x_7411_ = lean_array_push(v___x_7410_, v___x_7408_);
                                    if v_isShared_7316_ == 0 {
                                        leanh::lean_ctor_set(v___x_7315_, 0, v_a_7406_);
                                        v___x_7413_ = v___x_7315_;
                                        state = 22;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_7426_ =
                                            leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7426_,
                                            0,
                                            v_a_7406_,
                                        );
                                        v___x_7413_ = v_reuseFailAlloc_7426_;
                                        state = 22;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_7404_);
                                    leanh::lean_dec(v_a_7402_);
                                    leanh::lean_dec(v_userName_7398_);
                                    leanh::lean_dec(v_fvarId_7397_);
                                    leanh::lean_del_object(v___x_7315_);
                                    leanh::lean_del_object(v___x_7286_);
                                    v_a_7427_ = leanh::lean_ctor_get(v___x_7405_, 0);
                                    v_isSharedCheck_7434_ =
                                        (!leanh::lean_is_exclusive(v___x_7405_)) as u8;
                                    if v_isSharedCheck_7434_ == 0 {
                                        v___x_7429_ = v___x_7405_;
                                        v_isShared_7430_ = v_isSharedCheck_7434_;
                                        state = 25;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_7427_);
                                        leanh::lean_dec(v___x_7405_);
                                        v___x_7429_ = leanh::lean_box(0);
                                        v_isShared_7430_ = v_isSharedCheck_7434_;
                                        state = 25;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_7402_);
                                leanh::lean_dec_ref(v_value_7400_);
                                leanh::lean_dec(v_userName_7398_);
                                leanh::lean_dec(v_fvarId_7397_);
                                leanh::lean_del_object(v___x_7315_);
                                leanh::lean_del_object(v___x_7286_);
                                v_a_7435_ = leanh::lean_ctor_get(v___x_7403_, 0);
                                v_isSharedCheck_7442_ =
                                    (!leanh::lean_is_exclusive(v___x_7403_)) as u8;
                                if v_isSharedCheck_7442_ == 0 {
                                    v___x_7437_ = v___x_7403_;
                                    v_isShared_7438_ = v_isSharedCheck_7442_;
                                    state = 27;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_7435_);
                                    leanh::lean_dec(v___x_7403_);
                                    v___x_7437_ = leanh::lean_box(0);
                                    v_isShared_7438_ = v_isSharedCheck_7442_;
                                    state = 27;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_value_7400_);
                            leanh::lean_dec_ref(v_type_7399_);
                            leanh::lean_dec(v_userName_7398_);
                            leanh::lean_dec(v_fvarId_7397_);
                            leanh::lean_del_object(v___x_7315_);
                            leanh::lean_del_object(v___x_7286_);
                            v_a_7443_ = leanh::lean_ctor_get(v___x_7401_, 0);
                            v_isSharedCheck_7450_ =
                                (!leanh::lean_is_exclusive(v___x_7401_)) as u8;
                            if v_isSharedCheck_7450_ == 0 {
                                v___x_7445_ = v___x_7401_;
                                v_isShared_7446_ = v_isSharedCheck_7450_;
                                state = 29;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7443_);
                                leanh::lean_dec(v___x_7401_);
                                v___x_7445_ = leanh::lean_box(0);
                                v_isShared_7446_ = v_isSharedCheck_7450_;
                                state = 29;
                                continue;
                            }
                        }
                    } else {
                        v_fvarId_7451_ = leanh::lean_ctor_get(v_val_7313_, 1);
                        leanh::lean_inc(v_fvarId_7451_);
                        v_userName_7452_ = leanh::lean_ctor_get(v_val_7313_, 2);
                        leanh::lean_inc(v_userName_7452_);
                        v_type_7453_ = leanh::lean_ctor_get(v_val_7313_, 3);
                        leanh::lean_inc_ref(v_type_7453_);
                        leanh::lean_dec_ref_known(v_val_7313_, 5);
                        v___x_7454_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_7453_, v___y_7278_);
                        if leanh::lean_obj_tag(v___x_7454_) == 0 {
                            v_a_7455_ = leanh::lean_ctor_get(v___x_7454_, 0);
                            leanh::lean_inc(v_a_7455_);
                            leanh::lean_dec_ref_known(v___x_7454_, 1);
                            v___x_7456_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_userName_7452_,
                                    v_nondep_7396_,
                                );
                            v___x_7457_ =
                                l_Option_instBEq_beq___at___00Lean_Widget_goalToInteractive_spec__1(
                                    v_fst_7321_,
                                    v___x_7288_,
                                );
                            if v___x_7457_ == 0 {
                                leanh::lean_inc(v_a_7455_);
                                if v_isShared_7316_ == 0 {
                                    leanh::lean_ctor_set(v___x_7315_, 0, v_a_7455_);
                                    v___x_7459_ = v___x_7315_;
                                    state = 31;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_7461_ =
                                        leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7461_,
                                        0,
                                        v_a_7455_,
                                    );
                                    v___x_7459_ = v_reuseFailAlloc_7461_;
                                    state = 31;
                                    continue;
                                }
                            } else {
                                leanh::lean_del_object(v___x_7315_);
                                v___y_7355_ = v_fvarId_7451_;
                                v___y_7356_ = v_a_7455_;
                                v___y_7357_ = v___x_7456_;
                                v___y_7358_ = v___x_7457_;
                                state = 15;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_userName_7452_);
                            leanh::lean_dec(v_fvarId_7451_);
                            leanh::lean_dec(v_snd_7322_);
                            leanh::lean_dec(v_fst_7321_);
                            leanh::lean_dec(v_fst_7317_);
                            leanh::lean_del_object(v___x_7315_);
                            leanh::lean_del_object(v___x_7286_);
                            v_a_7462_ = leanh::lean_ctor_get(v___x_7454_, 0);
                            v_isSharedCheck_7469_ =
                                (!leanh::lean_is_exclusive(v___x_7454_)) as u8;
                            if v_isSharedCheck_7469_ == 0 {
                                v___x_7464_ = v___x_7454_;
                                v_isShared_7465_ = v_isSharedCheck_7469_;
                                state = 32;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7462_);
                                leanh::lean_dec(v___x_7454_);
                                v___x_7464_ = leanh::lean_box(0);
                                v_isShared_7465_ = v_isSharedCheck_7469_;
                                state = 32;
                                continue;
                            }
                        }
                    }
                }
            }
            19 => {
                v___x_7386_ = l_Option_instBEq_beq___at___00Lean_Widget_goalToInteractive_spec__1(
                    v_fst_7321_,
                    v___x_7385_,
                );
                leanh::lean_dec_ref(v___x_7385_);
                v___y_7334_ = v_fvarId_7377_;
                v___y_7335_ = v___x_7382_;
                v___y_7336_ = v_a_7381_;
                v___y_7337_ = v___x_7386_;
                state = 12;
                continue;
            }
            20 => {
                if v_isShared_7391_ == 0 {
                    v___x_7393_ = v___x_7390_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_7394_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7394_, 0, v_a_7388_);
                    v___x_7393_ = v_reuseFailAlloc_7394_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_7393_;
            }
            22 => {
                v___x_7414_ = l_Lean_Widget_addInteractiveHypothesisBundle(
                    v_a_7402_,
                    v___x_7411_,
                    v_a_7404_,
                    v___x_7413_,
                    v___x_7270_,
                    v___y_7277_,
                    v___y_7278_,
                    v___y_7279_,
                    v___y_7280_,
                );
                if leanh::lean_obj_tag(v___x_7414_) == 0 {
                    v_a_7415_ = leanh::lean_ctor_get(v___x_7414_, 0);
                    leanh::lean_inc(v_a_7415_);
                    leanh::lean_dec_ref_known(v___x_7414_, 1);
                    v___x_7416_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7416_, 0, v___x_7288_);
                    leanh::lean_ctor_set(v___x_7416_, 1, v_a_7415_);
                    v___x_7417_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7417_, 0, v___x_7375_);
                    leanh::lean_ctor_set(v___x_7417_, 1, v___x_7416_);
                    v_a_7290_ = v___x_7417_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_7286_);
                    v_a_7418_ = leanh::lean_ctor_get(v___x_7414_, 0);
                    v_isSharedCheck_7425_ = (!leanh::lean_is_exclusive(v___x_7414_)) as u8;
                    if v_isSharedCheck_7425_ == 0 {
                        v___x_7420_ = v___x_7414_;
                        v_isShared_7421_ = v_isSharedCheck_7425_;
                        state = 23;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7418_);
                        leanh::lean_dec(v___x_7414_);
                        v___x_7420_ = leanh::lean_box(0);
                        v_isShared_7421_ = v_isSharedCheck_7425_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_7421_ == 0 {
                    v___x_7423_ = v___x_7420_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_7424_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7424_, 0, v_a_7418_);
                    v___x_7423_ = v_reuseFailAlloc_7424_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_7423_;
            }
            25 => {
                if v_isShared_7430_ == 0 {
                    v___x_7432_ = v___x_7429_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_7433_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7433_, 0, v_a_7427_);
                    v___x_7432_ = v_reuseFailAlloc_7433_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_7432_;
            }
            27 => {
                if v_isShared_7438_ == 0 {
                    v___x_7440_ = v___x_7437_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_7441_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7441_, 0, v_a_7435_);
                    v___x_7440_ = v_reuseFailAlloc_7441_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_7440_;
            }
            29 => {
                if v_isShared_7446_ == 0 {
                    v___x_7448_ = v___x_7445_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_7449_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7449_, 0, v_a_7443_);
                    v___x_7448_ = v_reuseFailAlloc_7449_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_7448_;
            }
            31 => {
                v___x_7460_ = l_Option_instBEq_beq___at___00Lean_Widget_goalToInteractive_spec__1(
                    v_fst_7321_,
                    v___x_7459_,
                );
                leanh::lean_dec_ref(v___x_7459_);
                v___y_7355_ = v_fvarId_7451_;
                v___y_7356_ = v_a_7455_;
                v___y_7357_ = v___x_7456_;
                v___y_7358_ = v___x_7460_;
                state = 15;
                continue;
            }
            32 => {
                if v_isShared_7465_ == 0 {
                    v___x_7467_ = v___x_7464_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_7468_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7468_, 0, v_a_7462_);
                    v___x_7467_ = v_reuseFailAlloc_7468_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_7467_;
            }
            34 => {
                if v___x_7271_ == 0 {
                    v___x_7471_ = l_Lean_LocalDecl_isImplementationDetail(v_val_7313_);
                    if v___x_7471_ == 0 {
                        leanh::lean_del_object(v___x_7324_);
                        leanh::lean_del_object(v___x_7319_);
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_7315_);
                        leanh::lean_dec(v_val_7313_);
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_7324_);
                    leanh::lean_del_object(v___x_7319_);
                    state = 18;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3___boxed(
    mut v___x_7479_: *mut leanh::LeanObject,
    mut v___x_7480_: *mut leanh::LeanObject,
    mut v___x_7481_: *mut leanh::LeanObject,
    mut v_as_7482_: *mut leanh::LeanObject,
    mut v_sz_7483_: *mut leanh::LeanObject,
    mut v_i_7484_: *mut leanh::LeanObject,
    mut v_b_7485_: *mut leanh::LeanObject,
    mut v___y_7486_: *mut leanh::LeanObject,
    mut v___y_7487_: *mut leanh::LeanObject,
    mut v___y_7488_: *mut leanh::LeanObject,
    mut v___y_7489_: *mut leanh::LeanObject,
    mut v___y_7490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_13120__boxed_7491_: u8 = 0;
    let mut v___x_13121__boxed_7492_: u8 = 0;
    let mut v___x_13122__boxed_7493_: u8 = 0;
    let mut v_sz_boxed_7494_: usize = 0;
    let mut v_i_boxed_7495_: usize = 0;
    let mut v_res_7496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_13120__boxed_7491_ = (leanh::lean_unbox(v___x_7479_) as u8);
    v___x_13121__boxed_7492_ = (leanh::lean_unbox(v___x_7480_) as u8);
    v___x_13122__boxed_7493_ = (leanh::lean_unbox(v___x_7481_) as u8);
    v_sz_boxed_7494_ = leanh::lean_unbox_usize(v_sz_7483_);
    leanh::lean_dec(v_sz_7483_);
    v_i_boxed_7495_ = leanh::lean_unbox_usize(v_i_7484_);
    leanh::lean_dec(v_i_7484_);
    v_res_7496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3(v___x_13120__boxed_7491_, v___x_13121__boxed_7492_, v___x_13122__boxed_7493_, v_as_7482_, v_sz_boxed_7494_, v_i_boxed_7495_, v_b_7485_, v___y_7486_, v___y_7487_, v___y_7488_, v___y_7489_);
    leanh::lean_dec(v___y_7489_);
    leanh::lean_dec_ref(v___y_7488_);
    leanh::lean_dec(v___y_7487_);
    leanh::lean_dec_ref(v___y_7486_);
    leanh::lean_dec_ref(v_as_7482_);
    return v_res_7496_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2(
    mut v___x_7497_: u8,
    mut v___x_7498_: u8,
    mut v___x_7499_: u8,
    mut v_t_7500_: *mut leanh::LeanObject,
    mut v_init_7501_: *mut leanh::LeanObject,
    mut v___y_7502_: *mut leanh::LeanObject,
    mut v___y_7503_: *mut leanh::LeanObject,
    mut v___y_7504_: *mut leanh::LeanObject,
    mut v___y_7505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_7507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7513_: u8 = 0;
    let mut v_a_7514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7521_: usize = 0;
    let mut v___x_7522_: usize = 0;
    let mut v___x_7523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7527_: u8 = 0;
    let mut v_fst_7528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7537_: u8 = 0;
    let mut v_a_7538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7541_: u8 = 0;
    let mut v___x_7543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7545_: u8 = 0;
    let mut v_isSharedCheck_7546_: u8 = 0;
    let mut v_a_7547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7550_: u8 = 0;
    let mut v___x_7552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7554_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_7507_ = leanh::lean_ctor_get(v_t_7500_, 0);
                v_tail_7508_ = leanh::lean_ctor_get(v_t_7500_, 1);
                leanh::lean_inc_ref(v_init_7501_);
                v___x_7509_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2(v_init_7501_, v___x_7497_, v___x_7498_, v___x_7499_, v_root_7507_, v_init_7501_, v___y_7502_, v___y_7503_, v___y_7504_, v___y_7505_);
                leanh::lean_dec_ref(v_init_7501_);
                if leanh::lean_obj_tag(v___x_7509_) == 0 {
                    v_a_7510_ = leanh::lean_ctor_get(v___x_7509_, 0);
                    v_isSharedCheck_7546_ = (!leanh::lean_is_exclusive(v___x_7509_)) as u8;
                    if v_isSharedCheck_7546_ == 0 {
                        v___x_7512_ = v___x_7509_;
                        v_isShared_7513_ = v_isSharedCheck_7546_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7510_);
                        leanh::lean_dec(v___x_7509_);
                        v___x_7512_ = leanh::lean_box(0);
                        v_isShared_7513_ = v_isSharedCheck_7546_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7547_ = leanh::lean_ctor_get(v___x_7509_, 0);
                    v_isSharedCheck_7554_ = (!leanh::lean_is_exclusive(v___x_7509_)) as u8;
                    if v_isSharedCheck_7554_ == 0 {
                        v___x_7549_ = v___x_7509_;
                        v_isShared_7550_ = v_isSharedCheck_7554_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7547_);
                        leanh::lean_dec(v___x_7509_);
                        v___x_7549_ = leanh::lean_box(0);
                        v_isShared_7550_ = v_isSharedCheck_7554_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_7510_) == 0 {
                    v_a_7514_ = leanh::lean_ctor_get(v_a_7510_, 0);
                    leanh::lean_inc(v_a_7514_);
                    leanh::lean_dec_ref_known(v_a_7510_, 1);
                    if v_isShared_7513_ == 0 {
                        leanh::lean_ctor_set(v___x_7512_, 0, v_a_7514_);
                        v___x_7516_ = v___x_7512_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7517_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7517_, 0, v_a_7514_);
                        v___x_7516_ = v_reuseFailAlloc_7517_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_7512_);
                    v_a_7518_ = leanh::lean_ctor_get(v_a_7510_, 0);
                    leanh::lean_inc(v_a_7518_);
                    leanh::lean_dec_ref_known(v_a_7510_, 1);
                    v___x_7519_ = leanh::lean_box(0);
                    v___x_7520_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7520_, 0, v___x_7519_);
                    leanh::lean_ctor_set(v___x_7520_, 1, v_a_7518_);
                    v_sz_7521_ = lean_array_size(v_tail_7508_);
                    v___x_7522_ = 0usize;
                    v___x_7523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3(v___x_7497_, v___x_7498_, v___x_7499_, v_tail_7508_, v_sz_7521_, v___x_7522_, v___x_7520_, v___y_7502_, v___y_7503_, v___y_7504_, v___y_7505_);
                    if leanh::lean_obj_tag(v___x_7523_) == 0 {
                        v_a_7524_ = leanh::lean_ctor_get(v___x_7523_, 0);
                        v_isSharedCheck_7537_ =
                            (!leanh::lean_is_exclusive(v___x_7523_)) as u8;
                        if v_isSharedCheck_7537_ == 0 {
                            v___x_7526_ = v___x_7523_;
                            v_isShared_7527_ = v_isSharedCheck_7537_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7524_);
                            leanh::lean_dec(v___x_7523_);
                            v___x_7526_ = leanh::lean_box(0);
                            v_isShared_7527_ = v_isSharedCheck_7537_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_7538_ = leanh::lean_ctor_get(v___x_7523_, 0);
                        v_isSharedCheck_7545_ =
                            (!leanh::lean_is_exclusive(v___x_7523_)) as u8;
                        if v_isSharedCheck_7545_ == 0 {
                            v___x_7540_ = v___x_7523_;
                            v_isShared_7541_ = v_isSharedCheck_7545_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7538_);
                            leanh::lean_dec(v___x_7523_);
                            v___x_7540_ = leanh::lean_box(0);
                            v_isShared_7541_ = v_isSharedCheck_7545_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_7516_;
            }
            3 => {
                v_fst_7528_ = leanh::lean_ctor_get(v_a_7524_, 0);
                if leanh::lean_obj_tag(v_fst_7528_) == 0 {
                    v_snd_7529_ = leanh::lean_ctor_get(v_a_7524_, 1);
                    leanh::lean_inc(v_snd_7529_);
                    leanh::lean_dec(v_a_7524_);
                    if v_isShared_7527_ == 0 {
                        leanh::lean_ctor_set(v___x_7526_, 0, v_snd_7529_);
                        v___x_7531_ = v___x_7526_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_7532_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7532_, 0, v_snd_7529_);
                        v___x_7531_ = v_reuseFailAlloc_7532_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_7528_);
                    leanh::lean_dec(v_a_7524_);
                    v_val_7533_ = leanh::lean_ctor_get(v_fst_7528_, 0);
                    leanh::lean_inc(v_val_7533_);
                    leanh::lean_dec_ref_known(v_fst_7528_, 1);
                    if v_isShared_7527_ == 0 {
                        leanh::lean_ctor_set(v___x_7526_, 0, v_val_7533_);
                        v___x_7535_ = v___x_7526_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_7536_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7536_, 0, v_val_7533_);
                        v___x_7535_ = v_reuseFailAlloc_7536_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_7531_;
            }
            5 => {
                return v___x_7535_;
            }
            6 => {
                if v_isShared_7541_ == 0 {
                    v___x_7543_ = v___x_7540_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7544_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7544_, 0, v_a_7538_);
                    v___x_7543_ = v_reuseFailAlloc_7544_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7543_;
            }
            8 => {
                if v_isShared_7550_ == 0 {
                    v___x_7552_ = v___x_7549_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7553_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7553_, 0, v_a_7547_);
                    v___x_7552_ = v_reuseFailAlloc_7553_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7552_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2___boxed(
    mut v___x_7555_: *mut leanh::LeanObject,
    mut v___x_7556_: *mut leanh::LeanObject,
    mut v___x_7557_: *mut leanh::LeanObject,
    mut v_t_7558_: *mut leanh::LeanObject,
    mut v_init_7559_: *mut leanh::LeanObject,
    mut v___y_7560_: *mut leanh::LeanObject,
    mut v___y_7561_: *mut leanh::LeanObject,
    mut v___y_7562_: *mut leanh::LeanObject,
    mut v___y_7563_: *mut leanh::LeanObject,
    mut v___y_7564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_13522__boxed_7565_: u8 = 0;
    let mut v___x_13523__boxed_7566_: u8 = 0;
    let mut v___x_13524__boxed_7567_: u8 = 0;
    let mut v_res_7568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_13522__boxed_7565_ = (leanh::lean_unbox(v___x_7555_) as u8);
    v___x_13523__boxed_7566_ = (leanh::lean_unbox(v___x_7556_) as u8);
    v___x_13524__boxed_7567_ = (leanh::lean_unbox(v___x_7557_) as u8);
    v_res_7568_ = l_Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2(
        v___x_13522__boxed_7565_,
        v___x_13523__boxed_7566_,
        v___x_13524__boxed_7567_,
        v_t_7558_,
        v_init_7559_,
        v___y_7560_,
        v___y_7561_,
        v___y_7562_,
        v___y_7563_,
    );
    leanh::lean_dec(v___y_7563_);
    leanh::lean_dec_ref(v___y_7562_);
    leanh::lean_dec(v___y_7561_);
    leanh::lean_dec_ref(v___y_7560_);
    leanh::lean_dec_ref(v_t_7558_);
    return v_res_7568_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Widget_goalToInteractive_spec__3_spec__5___redArg(
    mut v___y_7569_: *mut leanh::LeanObject,
    mut v___y_7570_: *mut leanh::LeanObject,
    mut v___y_7571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_7576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_7577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_7581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7573_ = lean_st_ref_get(v___y_7571_);
    v_env_7574_ = leanh::lean_ctor_get(v___x_7573_, 0);
    leanh::lean_inc_ref(v_env_7574_);
    leanh::lean_dec(v___x_7573_);
    v___x_7575_ = lean_st_ref_get(v___y_7569_);
    v_mctx_7576_ = leanh::lean_ctor_get(v___x_7575_, 0);
    leanh::lean_inc_ref(v_mctx_7576_);
    leanh::lean_dec(v___x_7575_);
    v_options_7577_ = leanh::lean_ctor_get(v___y_7570_, 2);
    v_currNamespace_7578_ = leanh::lean_ctor_get(v___y_7570_, 6);
    v_openDecls_7579_ = leanh::lean_ctor_get(v___y_7570_, 7);
    v___x_7580_ = lean_st_ref_get(v___y_7571_);
    v_ngen_7581_ = leanh::lean_ctor_get(v___x_7580_, 2);
    leanh::lean_inc_ref(v_ngen_7581_);
    leanh::lean_dec(v___x_7580_);
    v___x_7582_ = leanh::lean_box(0);
    v___x_7583_ = l_Lean_instInhabitedFileMap_default;
    leanh::lean_inc(v_openDecls_7579_);
    leanh::lean_inc(v_currNamespace_7578_);
    leanh::lean_inc_ref(v_options_7577_);
    v___x_7584_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
    leanh::lean_ctor_set(v___x_7584_, 0, v_env_7574_);
    leanh::lean_ctor_set(v___x_7584_, 1, v___x_7582_);
    leanh::lean_ctor_set(v___x_7584_, 2, v___x_7583_);
    leanh::lean_ctor_set(v___x_7584_, 3, v_mctx_7576_);
    leanh::lean_ctor_set(v___x_7584_, 4, v_options_7577_);
    leanh::lean_ctor_set(v___x_7584_, 5, v_currNamespace_7578_);
    leanh::lean_ctor_set(v___x_7584_, 6, v_openDecls_7579_);
    leanh::lean_ctor_set(v___x_7584_, 7, v_ngen_7581_);
    v___x_7585_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_7585_, 0, v___x_7584_);
    return v___x_7585_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Widget_goalToInteractive_spec__3_spec__5___redArg___boxed(
    mut v___y_7586_: *mut leanh::LeanObject,
    mut v___y_7587_: *mut leanh::LeanObject,
    mut v___y_7588_: *mut leanh::LeanObject,
    mut v___y_7589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7590_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Widget_goalToInteractive_spec__3_spec__5___redArg(v___y_7586_, v___y_7587_, v___y_7588_);
    leanh::lean_dec(v___y_7588_);
    leanh::lean_dec_ref(v___y_7587_);
    leanh::lean_dec(v___y_7586_);
    return v_res_7590_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_save___at___00Lean_Widget_goalToInteractive_spec__3(
    mut v___y_7591_: *mut leanh::LeanObject,
    mut v___y_7592_: *mut leanh::LeanObject,
    mut v___y_7593_: *mut leanh::LeanObject,
    mut v___y_7594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7600_: u8 = 0;
    let mut v_fileMap_7601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_7603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_7604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_7607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7610_: u8 = 0;
    let mut v___x_7611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7618_: u8 = 0;
    let mut v_unused_7619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7621_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7596_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Widget_goalToInteractive_spec__3_spec__5___redArg(v___y_7592_, v___y_7593_, v___y_7594_);
                v_a_7597_ = leanh::lean_ctor_get(v___x_7596_, 0);
                v_isSharedCheck_7621_ = (!leanh::lean_is_exclusive(v___x_7596_)) as u8;
                if v_isSharedCheck_7621_ == 0 {
                    v___x_7599_ = v___x_7596_;
                    v_isShared_7600_ = v_isSharedCheck_7621_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_7597_);
                    leanh::lean_dec(v___x_7596_);
                    v___x_7599_ = leanh::lean_box(0);
                    v_isShared_7600_ = v_isSharedCheck_7621_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fileMap_7601_ = leanh::lean_ctor_get(v___y_7593_, 1);
                v_env_7602_ = leanh::lean_ctor_get(v_a_7597_, 0);
                v_mctx_7603_ = leanh::lean_ctor_get(v_a_7597_, 3);
                v_options_7604_ = leanh::lean_ctor_get(v_a_7597_, 4);
                v_currNamespace_7605_ = leanh::lean_ctor_get(v_a_7597_, 5);
                v_openDecls_7606_ = leanh::lean_ctor_get(v_a_7597_, 6);
                v_ngen_7607_ = leanh::lean_ctor_get(v_a_7597_, 7);
                v_isSharedCheck_7618_ = (!leanh::lean_is_exclusive(v_a_7597_)) as u8;
                if v_isSharedCheck_7618_ == 0 {
                    v_unused_7619_ = leanh::lean_ctor_get(v_a_7597_, 2);
                    leanh::lean_dec(v_unused_7619_);
                    v_unused_7620_ = leanh::lean_ctor_get(v_a_7597_, 1);
                    leanh::lean_dec(v_unused_7620_);
                    v___x_7609_ = v_a_7597_;
                    v_isShared_7610_ = v_isSharedCheck_7618_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_ngen_7607_);
                    leanh::lean_inc(v_openDecls_7606_);
                    leanh::lean_inc(v_currNamespace_7605_);
                    leanh::lean_inc(v_options_7604_);
                    leanh::lean_inc(v_mctx_7603_);
                    leanh::lean_inc(v_env_7602_);
                    leanh::lean_dec(v_a_7597_);
                    v___x_7609_ = leanh::lean_box(0);
                    v_isShared_7610_ = v_isSharedCheck_7618_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7611_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_fileMap_7601_);
                if v_isShared_7610_ == 0 {
                    leanh::lean_ctor_set(v___x_7609_, 2, v_fileMap_7601_);
                    leanh::lean_ctor_set(v___x_7609_, 1, v___x_7611_);
                    v___x_7613_ = v___x_7609_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7617_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7617_, 0, v_env_7602_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7617_, 1, v___x_7611_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7617_, 2, v_fileMap_7601_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7617_, 3, v_mctx_7603_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7617_, 4, v_options_7604_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7617_, 5, v_currNamespace_7605_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7617_, 6, v_openDecls_7606_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7617_, 7, v_ngen_7607_);
                    v___x_7613_ = v_reuseFailAlloc_7617_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_7600_ == 0 {
                    leanh::lean_ctor_set(v___x_7599_, 0, v___x_7613_);
                    v___x_7615_ = v___x_7599_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7616_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7616_, 0, v___x_7613_);
                    v___x_7615_ = v_reuseFailAlloc_7616_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7615_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_save___at___00Lean_Widget_goalToInteractive_spec__3___boxed(
    mut v___y_7622_: *mut leanh::LeanObject,
    mut v___y_7623_: *mut leanh::LeanObject,
    mut v___y_7624_: *mut leanh::LeanObject,
    mut v___y_7625_: *mut leanh::LeanObject,
    mut v___y_7626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7627_ =
        l_Lean_Elab_CommandContextInfo_save___at___00Lean_Widget_goalToInteractive_spec__3(
            v___y_7622_,
            v___y_7623_,
            v___y_7624_,
            v___y_7625_,
        );
    leanh::lean_dec(v___y_7625_);
    leanh::lean_dec_ref(v___y_7624_);
    leanh::lean_dec(v___y_7623_);
    leanh::lean_dec_ref(v___y_7622_);
    return v_res_7627_;
}
pub unsafe fn l_Lean_Widget_goalToInteractive___lam__0(
    mut v___x_7636_: u8,
    mut v___x_7637_: u8,
    mut v_mvarId_7638_: *mut leanh::LeanObject,
    mut v_lctx_7639_: *mut leanh::LeanObject,
    mut v_mvarDecl_7640_: *mut leanh::LeanObject,
    mut v___y_7641_: *mut leanh::LeanObject,
    mut v___y_7642_: *mut leanh::LeanObject,
    mut v___y_7643_: *mut leanh::LeanObject,
    mut v___y_7644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_userName_7646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_7648_: u8 = 0;
    let mut v_decls_7649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7652_: u8 = 0;
    let mut v___x_7653_: u8 = 0;
    let mut v___x_7654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7663_: u8 = 0;
    let mut v___x_7664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7676_: u8 = 0;
    let mut v_a_7678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7683_: u8 = 0;
    let mut v___x_7684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7690_: u8 = 0;
    let mut v___x_7691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7698_: u8 = 0;
    let mut v___x_7700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7702_: u8 = 0;
    let mut v_isSharedCheck_7703_: u8 = 0;
    let mut v___x_7704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7713_: u8 = 0;
    let mut v_val_7714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7720_: u8 = 0;
    let mut v___x_7722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7724_: u8 = 0;
    let mut v_a_7725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7728_: u8 = 0;
    let mut v___x_7730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7732_: u8 = 0;
    let mut v_isSharedCheck_7733_: u8 = 0;
    let mut v_unused_7734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_userName_7646_ = leanh::lean_ctor_get(v_mvarDecl_7640_, 0);
                v_type_7647_ = leanh::lean_ctor_get(v_mvarDecl_7640_, 2);
                v_kind_7648_ = leanh::lean_ctor_get_uint8(
                    v_mvarDecl_7640_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_decls_7649_ = leanh::lean_ctor_get(v_lctx_7639_, 1);
                v_isSharedCheck_7733_ = (!leanh::lean_is_exclusive(v_lctx_7639_)) as u8;
                if v_isSharedCheck_7733_ == 0 {
                    v_unused_7734_ = leanh::lean_ctor_get(v_lctx_7639_, 2);
                    leanh::lean_dec(v_unused_7734_);
                    v_unused_7735_ = leanh::lean_ctor_get(v_lctx_7639_, 0);
                    leanh::lean_dec(v_unused_7735_);
                    v___x_7651_ = v_lctx_7639_;
                    v_isShared_7652_ = v_isSharedCheck_7733_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_decls_7649_);
                    leanh::lean_dec(v_lctx_7639_);
                    v___x_7651_ = leanh::lean_box(0);
                    v_isShared_7652_ = v_isSharedCheck_7733_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7653_ = l_Lean_MetavarKind_isSyntheticOpaque(v_kind_7648_);
                v___x_7654_ = leanh::lean_unsigned_to_nat(0);
                v___x_7704_ = leanh::lean_box(0);
                v___x_7705_ = l_Lean_Widget_goalToInteractive___lam__0___closed__2;
                v___x_7706_ =
                    l_Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2(
                        v___x_7653_,
                        v___x_7636_,
                        v___x_7637_,
                        v_decls_7649_,
                        v___x_7705_,
                        v___y_7641_,
                        v___y_7642_,
                        v___y_7643_,
                        v___y_7644_,
                    );
                leanh::lean_dec_ref(v_decls_7649_);
                if leanh::lean_obj_tag(v___x_7706_) == 0 {
                    v_a_7707_ = leanh::lean_ctor_get(v___x_7706_, 0);
                    leanh::lean_inc(v_a_7707_);
                    leanh::lean_dec_ref_known(v___x_7706_, 1);
                    v_snd_7708_ = leanh::lean_ctor_get(v_a_7707_, 1);
                    leanh::lean_inc(v_snd_7708_);
                    v_fst_7709_ = leanh::lean_ctor_get(v_a_7707_, 0);
                    leanh::lean_inc(v_fst_7709_);
                    leanh::lean_dec(v_a_7707_);
                    v_fst_7710_ = leanh::lean_ctor_get(v_snd_7708_, 0);
                    leanh::lean_inc(v_fst_7710_);
                    v_snd_7711_ = leanh::lean_ctor_get(v_snd_7708_, 1);
                    leanh::lean_inc(v_snd_7711_);
                    leanh::lean_dec(v_snd_7708_);
                    v___x_7712_ = lean_array_get_size(v_fst_7709_);
                    v___x_7713_ = lean_nat_dec_eq(v___x_7712_, v___x_7654_);
                    if v___x_7713_ == 0 {
                        if leanh::lean_obj_tag(v_fst_7710_) == 0 {
                            leanh::lean_dec(v_fst_7709_);
                            v_a_7678_ = v_snd_7711_;
                            state = 6;
                            continue;
                        } else {
                            v_val_7714_ = leanh::lean_ctor_get(v_fst_7710_, 0);
                            leanh::lean_inc(v_val_7714_);
                            leanh::lean_dec_ref_known(v_fst_7710_, 1);
                            v___x_7715_ = l_Lean_Widget_addInteractiveHypothesisBundle(
                                v_snd_7711_,
                                v_fst_7709_,
                                v_val_7714_,
                                v___x_7704_,
                                v___x_7713_,
                                v___y_7641_,
                                v___y_7642_,
                                v___y_7643_,
                                v___y_7644_,
                            );
                            if leanh::lean_obj_tag(v___x_7715_) == 0 {
                                v_a_7716_ = leanh::lean_ctor_get(v___x_7715_, 0);
                                leanh::lean_inc(v_a_7716_);
                                leanh::lean_dec_ref_known(v___x_7715_, 1);
                                v_a_7678_ = v_a_7716_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_del_object(v___x_7651_);
                                leanh::lean_dec_ref(v_mvarDecl_7640_);
                                leanh::lean_dec(v_mvarId_7638_);
                                v_a_7717_ = leanh::lean_ctor_get(v___x_7715_, 0);
                                v_isSharedCheck_7724_ =
                                    (!leanh::lean_is_exclusive(v___x_7715_)) as u8;
                                if v_isSharedCheck_7724_ == 0 {
                                    v___x_7719_ = v___x_7715_;
                                    v_isShared_7720_ = v_isSharedCheck_7724_;
                                    state = 11;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_7717_);
                                    leanh::lean_dec(v___x_7715_);
                                    v___x_7719_ = leanh::lean_box(0);
                                    v_isShared_7720_ = v_isSharedCheck_7724_;
                                    state = 11;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_fst_7710_);
                        leanh::lean_dec(v_fst_7709_);
                        v_a_7678_ = v_snd_7711_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_7651_);
                    leanh::lean_dec_ref(v_mvarDecl_7640_);
                    leanh::lean_dec(v_mvarId_7638_);
                    v_a_7725_ = leanh::lean_ctor_get(v___x_7706_, 0);
                    v_isSharedCheck_7732_ = (!leanh::lean_is_exclusive(v___x_7706_)) as u8;
                    if v_isSharedCheck_7732_ == 0 {
                        v___x_7727_ = v___x_7706_;
                        v_isShared_7728_ = v_isSharedCheck_7732_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7725_);
                        leanh::lean_dec(v___x_7706_);
                        v___x_7727_ = leanh::lean_box(0);
                        v_isShared_7728_ = v_isSharedCheck_7732_;
                        state = 13;
                        continue;
                    }
                }
            }
            2 => {
                v___x_7659_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Widget_goalToInteractive_spec__3(v___y_7641_, v___y_7642_, v___y_7643_, v___y_7644_);
                v_a_7660_ = leanh::lean_ctor_get(v___x_7659_, 0);
                v_isSharedCheck_7676_ = (!leanh::lean_is_exclusive(v___x_7659_)) as u8;
                if v_isSharedCheck_7676_ == 0 {
                    v___x_7662_ = v___x_7659_;
                    v_isShared_7663_ = v_isSharedCheck_7676_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_a_7660_);
                    leanh::lean_dec(v___x_7659_);
                    v___x_7662_ = leanh::lean_box(0);
                    v_isShared_7663_ = v_isSharedCheck_7676_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7664_ = leanh::lean_box(0);
                v___x_7665_ = l_Lean_Widget_goalToInteractive___lam__0___closed__0;
                if v_isShared_7652_ == 0 {
                    leanh::lean_ctor_set(v___x_7651_, 2, v___x_7665_);
                    leanh::lean_ctor_set(v___x_7651_, 1, v___x_7664_);
                    leanh::lean_ctor_set(v___x_7651_, 0, v_a_7660_);
                    v___x_7667_ = v___x_7651_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7675_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7675_, 0, v_a_7660_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7675_, 1, v___x_7664_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7675_, 2, v___x_7665_);
                    v___x_7667_ = v_reuseFailAlloc_7675_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7668_ = l_Lean_Server_WithRpcRef_mk___redArg(v___x_7667_);
                v___x_7669_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_7669_, 0, v___y_7656_);
                leanh::lean_ctor_set(v___x_7669_, 1, v___y_7657_);
                leanh::lean_ctor_set(v___x_7669_, 2, v___x_7668_);
                v___x_7670_ = l_Lean_Meta_getGoalPrefix(v_mvarDecl_7640_);
                leanh::lean_dec_ref(v_mvarDecl_7640_);
                v___x_7671_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                leanh::lean_ctor_set(v___x_7671_, 0, v___x_7669_);
                leanh::lean_ctor_set(v___x_7671_, 1, v___y_7658_);
                leanh::lean_ctor_set(v___x_7671_, 2, v___x_7670_);
                leanh::lean_ctor_set(v___x_7671_, 3, v_mvarId_7638_);
                leanh::lean_ctor_set(v___x_7671_, 4, v___x_7664_);
                leanh::lean_ctor_set(v___x_7671_, 5, v___x_7664_);
                if v_isShared_7663_ == 0 {
                    leanh::lean_ctor_set(v___x_7662_, 0, v___x_7671_);
                    v___x_7673_ = v___x_7662_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7674_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7674_, 0, v___x_7671_);
                    v___x_7673_ = v_reuseFailAlloc_7674_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7673_;
            }
            6 => {
                leanh::lean_inc_ref(v_type_7647_);
                v___x_7679_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_7647_, v___y_7642_);
                v_a_7680_ = leanh::lean_ctor_get(v___x_7679_, 0);
                v_isSharedCheck_7703_ = (!leanh::lean_is_exclusive(v___x_7679_)) as u8;
                if v_isSharedCheck_7703_ == 0 {
                    v___x_7682_ = v___x_7679_;
                    v_isShared_7683_ = v_isSharedCheck_7703_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_a_7680_);
                    leanh::lean_dec(v___x_7679_);
                    v___x_7682_ = leanh::lean_box(0);
                    v_isShared_7683_ = v_isSharedCheck_7703_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_7684_ = l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged___closed__2;
                v___x_7685_ = l_Lean_Widget_ppExprTagged(
                    v_a_7680_,
                    v___x_7684_,
                    v___y_7641_,
                    v___y_7642_,
                    v___y_7643_,
                    v___y_7644_,
                );
                if leanh::lean_obj_tag(v___x_7685_) == 0 {
                    if leanh::lean_obj_tag(v_userName_7646_) == 0 {
                        leanh::lean_del_object(v___x_7682_);
                        v_a_7686_ = leanh::lean_ctor_get(v___x_7685_, 0);
                        leanh::lean_inc(v_a_7686_);
                        leanh::lean_dec_ref_known(v___x_7685_, 1);
                        v___x_7687_ = leanh::lean_box(0);
                        v___y_7656_ = v_a_7678_;
                        v___y_7657_ = v_a_7686_;
                        v___y_7658_ = v___x_7687_;
                        state = 2;
                        continue;
                    } else {
                        v_a_7688_ = leanh::lean_ctor_get(v___x_7685_, 0);
                        leanh::lean_inc(v_a_7688_);
                        leanh::lean_dec_ref_known(v___x_7685_, 1);
                        leanh::lean_inc(v_userName_7646_);
                        v___x_7689_ = lean_erase_macro_scopes(v_userName_7646_);
                        v___x_7690_ = 1;
                        v___x_7691_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v___x_7689_,
                                v___x_7690_,
                            );
                        if v_isShared_7683_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_7682_, 1);
                            leanh::lean_ctor_set(v___x_7682_, 0, v___x_7691_);
                            v___x_7693_ = v___x_7682_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_7694_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7694_, 0, v___x_7691_);
                            v___x_7693_ = v_reuseFailAlloc_7694_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_7682_);
                    leanh::lean_dec_ref(v_a_7678_);
                    leanh::lean_del_object(v___x_7651_);
                    leanh::lean_dec_ref(v_mvarDecl_7640_);
                    leanh::lean_dec(v_mvarId_7638_);
                    v_a_7695_ = leanh::lean_ctor_get(v___x_7685_, 0);
                    v_isSharedCheck_7702_ = (!leanh::lean_is_exclusive(v___x_7685_)) as u8;
                    if v_isSharedCheck_7702_ == 0 {
                        v___x_7697_ = v___x_7685_;
                        v_isShared_7698_ = v_isSharedCheck_7702_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7695_);
                        leanh::lean_dec(v___x_7685_);
                        v___x_7697_ = leanh::lean_box(0);
                        v_isShared_7698_ = v_isSharedCheck_7702_;
                        state = 9;
                        continue;
                    }
                }
            }
            8 => {
                v___y_7656_ = v_a_7678_;
                v___y_7657_ = v_a_7688_;
                v___y_7658_ = v___x_7693_;
                state = 2;
                continue;
            }
            9 => {
                if v_isShared_7698_ == 0 {
                    v___x_7700_ = v___x_7697_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7701_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7701_, 0, v_a_7695_);
                    v___x_7700_ = v_reuseFailAlloc_7701_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7700_;
            }
            11 => {
                if v_isShared_7720_ == 0 {
                    v___x_7722_ = v___x_7719_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7723_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7723_, 0, v_a_7717_);
                    v___x_7722_ = v_reuseFailAlloc_7723_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_7722_;
            }
            13 => {
                if v_isShared_7728_ == 0 {
                    v___x_7730_ = v___x_7727_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7731_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7731_, 0, v_a_7725_);
                    v___x_7730_ = v_reuseFailAlloc_7731_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_7730_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_goalToInteractive___lam__0___boxed(
    mut v___x_7736_: *mut leanh::LeanObject,
    mut v___x_7737_: *mut leanh::LeanObject,
    mut v_mvarId_7738_: *mut leanh::LeanObject,
    mut v_lctx_7739_: *mut leanh::LeanObject,
    mut v_mvarDecl_7740_: *mut leanh::LeanObject,
    mut v___y_7741_: *mut leanh::LeanObject,
    mut v___y_7742_: *mut leanh::LeanObject,
    mut v___y_7743_: *mut leanh::LeanObject,
    mut v___y_7744_: *mut leanh::LeanObject,
    mut v___y_7745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_13732__boxed_7746_: u8 = 0;
    let mut v___x_13733__boxed_7747_: u8 = 0;
    let mut v_res_7748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_13732__boxed_7746_ = (leanh::lean_unbox(v___x_7736_) as u8);
    v___x_13733__boxed_7747_ = (leanh::lean_unbox(v___x_7737_) as u8);
    v_res_7748_ = l_Lean_Widget_goalToInteractive___lam__0(
        v___x_13732__boxed_7746_,
        v___x_13733__boxed_7747_,
        v_mvarId_7738_,
        v_lctx_7739_,
        v_mvarDecl_7740_,
        v___y_7741_,
        v___y_7742_,
        v___y_7743_,
        v___y_7744_,
    );
    leanh::lean_dec(v___y_7744_);
    leanh::lean_dec_ref(v___y_7743_);
    leanh::lean_dec(v___y_7742_);
    leanh::lean_dec_ref(v___y_7741_);
    return v_res_7748_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4_spec__7___redArg(
    mut v_lctx_7749_: *mut leanh::LeanObject,
    mut v_localInsts_7750_: *mut leanh::LeanObject,
    mut v_x_7751_: *mut leanh::LeanObject,
    mut v___y_7752_: *mut leanh::LeanObject,
    mut v___y_7753_: *mut leanh::LeanObject,
    mut v___y_7754_: *mut leanh::LeanObject,
    mut v___y_7755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7761_: u8 = 0;
    let mut v___x_7763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7765_: u8 = 0;
    let mut v_a_7766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7769_: u8 = 0;
    let mut v___x_7771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7773_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7757_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(
                    leanh::lean_box(0),
                    v_lctx_7749_,
                    v_localInsts_7750_,
                    v_x_7751_,
                    v___y_7752_,
                    v___y_7753_,
                    v___y_7754_,
                    v___y_7755_,
                );
                if leanh::lean_obj_tag(v___x_7757_) == 0 {
                    v_a_7758_ = leanh::lean_ctor_get(v___x_7757_, 0);
                    v_isSharedCheck_7765_ = (!leanh::lean_is_exclusive(v___x_7757_)) as u8;
                    if v_isSharedCheck_7765_ == 0 {
                        v___x_7760_ = v___x_7757_;
                        v_isShared_7761_ = v_isSharedCheck_7765_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7758_);
                        leanh::lean_dec(v___x_7757_);
                        v___x_7760_ = leanh::lean_box(0);
                        v_isShared_7761_ = v_isSharedCheck_7765_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7766_ = leanh::lean_ctor_get(v___x_7757_, 0);
                    v_isSharedCheck_7773_ = (!leanh::lean_is_exclusive(v___x_7757_)) as u8;
                    if v_isSharedCheck_7773_ == 0 {
                        v___x_7768_ = v___x_7757_;
                        v_isShared_7769_ = v_isSharedCheck_7773_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7766_);
                        leanh::lean_dec(v___x_7757_);
                        v___x_7768_ = leanh::lean_box(0);
                        v_isShared_7769_ = v_isSharedCheck_7773_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7761_ == 0 {
                    v___x_7763_ = v___x_7760_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7764_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7764_, 0, v_a_7758_);
                    v___x_7763_ = v_reuseFailAlloc_7764_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7763_;
            }
            3 => {
                if v_isShared_7769_ == 0 {
                    v___x_7771_ = v___x_7768_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7772_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7772_, 0, v_a_7766_);
                    v___x_7771_ = v_reuseFailAlloc_7772_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7771_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4_spec__7___redArg___boxed(
    mut v_lctx_7774_: *mut leanh::LeanObject,
    mut v_localInsts_7775_: *mut leanh::LeanObject,
    mut v_x_7776_: *mut leanh::LeanObject,
    mut v___y_7777_: *mut leanh::LeanObject,
    mut v___y_7778_: *mut leanh::LeanObject,
    mut v___y_7779_: *mut leanh::LeanObject,
    mut v___y_7780_: *mut leanh::LeanObject,
    mut v___y_7781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7782_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4_spec__7___redArg(v_lctx_7774_, v_localInsts_7775_, v_x_7776_, v___y_7777_, v___y_7778_, v___y_7779_, v___y_7780_);
    leanh::lean_dec(v___y_7780_);
    leanh::lean_dec_ref(v___y_7779_);
    leanh::lean_dec(v___y_7778_);
    leanh::lean_dec_ref(v___y_7777_);
    return v_res_7782_;
}
pub unsafe fn l_Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4___redArg(
    mut v_goal_7783_: *mut leanh::LeanObject,
    mut v_action_7784_: *mut leanh::LeanObject,
    mut v___y_7785_: *mut leanh::LeanObject,
    mut v___y_7786_: *mut leanh::LeanObject,
    mut v___y_7787_: *mut leanh::LeanObject,
    mut v___y_7788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_7791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7790_ = lean_st_ref_get(v___y_7786_);
    v_mctx_7791_ = leanh::lean_ctor_get(v___x_7790_, 0);
    leanh::lean_inc_ref(v_mctx_7791_);
    leanh::lean_dec(v___x_7790_);
    v___x_7792_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_7791_, v_goal_7783_);
    leanh::lean_dec_ref(v_mctx_7791_);
    if leanh::lean_obj_tag(v___x_7792_) == 1 {
        let mut v_val_7793_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_options_7794_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_lctx_7795_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_localInstances_7796_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7797_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7798_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7799_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_7800_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7801_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7802_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_goal_7783_);
        v_val_7793_ = leanh::lean_ctor_get(v___x_7792_, 0);
        leanh::lean_inc(v_val_7793_);
        leanh::lean_dec_ref_known(v___x_7792_, 1);
        v_options_7794_ = leanh::lean_ctor_get(v___y_7787_, 2);
        v_lctx_7795_ = leanh::lean_ctor_get(v_val_7793_, 1);
        v_localInstances_7796_ = leanh::lean_ctor_get(v_val_7793_, 4);
        leanh::lean_inc_ref(v_localInstances_7796_);
        v___x_7797_ = leanh::lean_box(1);
        leanh::lean_inc_ref(v_options_7794_);
        v___x_7798_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_7798_, 0, v_options_7794_);
        leanh::lean_ctor_set(v___x_7798_, 1, v___x_7797_);
        leanh::lean_ctor_set(v___x_7798_, 2, v___x_7797_);
        leanh::lean_inc_ref(v_lctx_7795_);
        v___x_7799_ = l_Lean_LocalContext_sanitizeNames(v_lctx_7795_, v___x_7798_);
        v_fst_7800_ = leanh::lean_ctor_get(v___x_7799_, 0);
        leanh::lean_inc_n(v_fst_7800_, 2);
        leanh::lean_dec_ref(v___x_7799_);
        v___x_7801_ = leanh::lean_apply_2(v_action_7784_, v_fst_7800_, v_val_7793_);
        v___x_7802_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4_spec__7___redArg(v_fst_7800_, v_localInstances_7796_, v___x_7801_, v___y_7785_, v___y_7786_, v___y_7787_, v___y_7788_);
        return v___x_7802_;
    } else {
        let mut v___x_7803_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7804_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7805_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7806_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_7792_);
        leanh::lean_dec_ref(v_action_7784_);
        v___x_7803_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Widget_withGoalCtx___redArg___lam__1___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Widget_withGoalCtx___redArg___lam__1___closed__1_once),
            _init_l_Lean_Widget_withGoalCtx___redArg___lam__1___closed__1,
        );
        v___x_7804_ = l_Lean_MessageData_ofName(v_goal_7783_);
        v___x_7805_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_7805_, 0, v___x_7803_);
        leanh::lean_ctor_set(v___x_7805_, 1, v___x_7804_);
        v___x_7806_ =
            l_Lean_throwError___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__3___redArg(
                v___x_7805_,
                v___y_7785_,
                v___y_7786_,
                v___y_7787_,
                v___y_7788_,
            );
        return v___x_7806_;
    }
}
pub unsafe fn l_Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4___redArg___boxed(
    mut v_goal_7807_: *mut leanh::LeanObject,
    mut v_action_7808_: *mut leanh::LeanObject,
    mut v___y_7809_: *mut leanh::LeanObject,
    mut v___y_7810_: *mut leanh::LeanObject,
    mut v___y_7811_: *mut leanh::LeanObject,
    mut v___y_7812_: *mut leanh::LeanObject,
    mut v___y_7813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7814_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4___redArg(
        v_goal_7807_,
        v_action_7808_,
        v___y_7809_,
        v___y_7810_,
        v___y_7811_,
        v___y_7812_,
    );
    leanh::lean_dec(v___y_7812_);
    leanh::lean_dec_ref(v___y_7811_);
    leanh::lean_dec(v___y_7810_);
    leanh::lean_dec_ref(v___y_7809_);
    return v_res_7814_;
}
pub unsafe fn l_Lean_Widget_goalToInteractive(
    mut v_mvarId_7815_: *mut leanh::LeanObject,
    mut v_a_7816_: *mut leanh::LeanObject,
    mut v_a_7817_: *mut leanh::LeanObject,
    mut v_a_7818_: *mut leanh::LeanObject,
    mut v_a_7819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_7821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7823_: u8 = 0;
    let mut v___x_7824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7825_: u8 = 0;
    let mut v___x_7826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_options_7821_ = leanh::lean_ctor_get(v_a_7818_, 2);
    v___x_7822_ = l_Lean_Meta_pp_auxDecls;
    v___x_7823_ = l_Lean_Option_get___at___00Lean_Widget_goalToInteractive_spec__0(
        v_options_7821_,
        v___x_7822_,
    );
    v___x_7824_ = l_Lean_Meta_pp_implementationDetailHyps;
    v___x_7825_ = l_Lean_Option_get___at___00Lean_Widget_goalToInteractive_spec__0(
        v_options_7821_,
        v___x_7824_,
    );
    v___x_7826_ = leanh::lean_box((v___x_7825_) as usize);
    v___x_7827_ = leanh::lean_box((v___x_7823_) as usize);
    leanh::lean_inc(v_mvarId_7815_);
    v___f_7828_ = leanh::lean_alloc_closure(
        l_Lean_Widget_goalToInteractive___lam__0___boxed as *mut core::ffi::c_void,
        10,
        3,
    );
    leanh::lean_closure_set(v___f_7828_, 0, v___x_7826_);
    leanh::lean_closure_set(v___f_7828_, 1, v___x_7827_);
    leanh::lean_closure_set(v___f_7828_, 2, v_mvarId_7815_);
    v___x_7829_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4___redArg(
        v_mvarId_7815_,
        v___f_7828_,
        v_a_7816_,
        v_a_7817_,
        v_a_7818_,
        v_a_7819_,
    );
    return v___x_7829_;
}
pub unsafe fn l_Lean_Widget_goalToInteractive___boxed(
    mut v_mvarId_7830_: *mut leanh::LeanObject,
    mut v_a_7831_: *mut leanh::LeanObject,
    mut v_a_7832_: *mut leanh::LeanObject,
    mut v_a_7833_: *mut leanh::LeanObject,
    mut v_a_7834_: *mut leanh::LeanObject,
    mut v_a_7835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7836_ =
        l_Lean_Widget_goalToInteractive(v_mvarId_7830_, v_a_7831_, v_a_7832_, v_a_7833_, v_a_7834_);
    leanh::lean_dec(v_a_7834_);
    leanh::lean_dec_ref(v_a_7833_);
    leanh::lean_dec(v_a_7832_);
    leanh::lean_dec_ref(v_a_7831_);
    return v_res_7836_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Widget_goalToInteractive_spec__3_spec__5(
    mut v___y_7837_: *mut leanh::LeanObject,
    mut v___y_7838_: *mut leanh::LeanObject,
    mut v___y_7839_: *mut leanh::LeanObject,
    mut v___y_7840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7842_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Widget_goalToInteractive_spec__3_spec__5___redArg(v___y_7838_, v___y_7839_, v___y_7840_);
    return v___x_7842_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Widget_goalToInteractive_spec__3_spec__5___boxed(
    mut v___y_7843_: *mut leanh::LeanObject,
    mut v___y_7844_: *mut leanh::LeanObject,
    mut v___y_7845_: *mut leanh::LeanObject,
    mut v___y_7846_: *mut leanh::LeanObject,
    mut v___y_7847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7848_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Widget_goalToInteractive_spec__3_spec__5(v___y_7843_, v___y_7844_, v___y_7845_, v___y_7846_);
    leanh::lean_dec(v___y_7846_);
    leanh::lean_dec_ref(v___y_7845_);
    leanh::lean_dec(v___y_7844_);
    leanh::lean_dec_ref(v___y_7843_);
    return v_res_7848_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4_spec__7(
    mut v_00_u03b1_7849_: *mut leanh::LeanObject,
    mut v_lctx_7850_: *mut leanh::LeanObject,
    mut v_localInsts_7851_: *mut leanh::LeanObject,
    mut v_x_7852_: *mut leanh::LeanObject,
    mut v___y_7853_: *mut leanh::LeanObject,
    mut v___y_7854_: *mut leanh::LeanObject,
    mut v___y_7855_: *mut leanh::LeanObject,
    mut v___y_7856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7858_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4_spec__7___redArg(v_lctx_7850_, v_localInsts_7851_, v_x_7852_, v___y_7853_, v___y_7854_, v___y_7855_, v___y_7856_);
    return v___x_7858_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4_spec__7___boxed(
    mut v_00_u03b1_7859_: *mut leanh::LeanObject,
    mut v_lctx_7860_: *mut leanh::LeanObject,
    mut v_localInsts_7861_: *mut leanh::LeanObject,
    mut v_x_7862_: *mut leanh::LeanObject,
    mut v___y_7863_: *mut leanh::LeanObject,
    mut v___y_7864_: *mut leanh::LeanObject,
    mut v___y_7865_: *mut leanh::LeanObject,
    mut v___y_7866_: *mut leanh::LeanObject,
    mut v___y_7867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7868_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4_spec__7(v_00_u03b1_7859_, v_lctx_7860_, v_localInsts_7861_, v_x_7862_, v___y_7863_, v___y_7864_, v___y_7865_, v___y_7866_);
    leanh::lean_dec(v___y_7866_);
    leanh::lean_dec_ref(v___y_7865_);
    leanh::lean_dec(v___y_7864_);
    leanh::lean_dec_ref(v___y_7863_);
    return v_res_7868_;
}
pub unsafe fn l_Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4(
    mut v_00_u03b1_7869_: *mut leanh::LeanObject,
    mut v_goal_7870_: *mut leanh::LeanObject,
    mut v_action_7871_: *mut leanh::LeanObject,
    mut v___y_7872_: *mut leanh::LeanObject,
    mut v___y_7873_: *mut leanh::LeanObject,
    mut v___y_7874_: *mut leanh::LeanObject,
    mut v___y_7875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7877_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4___redArg(
        v_goal_7870_,
        v_action_7871_,
        v___y_7872_,
        v___y_7873_,
        v___y_7874_,
        v___y_7875_,
    );
    return v___x_7877_;
}
pub unsafe fn l_Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4___boxed(
    mut v_00_u03b1_7878_: *mut leanh::LeanObject,
    mut v_goal_7879_: *mut leanh::LeanObject,
    mut v_action_7880_: *mut leanh::LeanObject,
    mut v___y_7881_: *mut leanh::LeanObject,
    mut v___y_7882_: *mut leanh::LeanObject,
    mut v___y_7883_: *mut leanh::LeanObject,
    mut v___y_7884_: *mut leanh::LeanObject,
    mut v___y_7885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7886_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4(
        v_00_u03b1_7878_,
        v_goal_7879_,
        v_action_7880_,
        v___y_7881_,
        v___y_7882_,
        v___y_7883_,
        v___y_7884_,
    );
    leanh::lean_dec(v___y_7884_);
    leanh::lean_dec_ref(v___y_7883_);
    leanh::lean_dec(v___y_7882_);
    leanh::lean_dec_ref(v___y_7881_);
    return v_res_7886_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Widget_InteractiveGoal(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Widget_InteractiveCode(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default =
        _init_l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default();
    leanh::lean_mark_persistent(
        l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default,
    );
    l_Lean_Widget_instInhabitedInteractiveHypothesisBundle =
        _init_l_Lean_Widget_instInhabitedInteractiveHypothesisBundle();
    leanh::lean_mark_persistent(l_Lean_Widget_instInhabitedInteractiveHypothesisBundle);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Widget_InteractiveGoal(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Widget_InteractiveGoal(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Widget_InteractiveCode(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Lsp_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Widget_InteractiveGoal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Widget_InteractiveGoal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Widget_InteractiveGoal(builtin);
}
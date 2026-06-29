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
static mut l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Widget_instInhabitedInteractiveHypothesisBundle:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1_spec__1___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [110, 97, 109, 101, 115, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [102, 118, 97, 114, 73, 100, 115, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 121, 112, 101, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [118, 97, 108, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 115, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 115, 84, 121, 112, 101, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 115, 73, 110, 115, 101, 114, 116, 101, 100, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 115, 82, 101, 109, 111, 118, 101, 100, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_instToJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 101, 120, 116, 0]};
static mut l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 112, 112, 101, 110, 100, 0]};
static mut l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [116, 97, 103, 0]};
static mut l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc___closed__0_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableSubexprInfo_enc_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc___closed__0_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc___closed__0_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__value) as *mut crate::leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0___closed__0_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 32, 97, 114, 114, 97, 121, 44, 32, 103, 111, 116, 32, 39, 0]};
static mut l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__0_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 97, 103, 32, 102, 111, 117, 110, 100, 0]};
static mut l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__2_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 109, 97, 116, 99, 104, 101, 100, 0]};
static mut l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__3_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec___closed__0_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableSubexprInfo_dec_00___x40_Lean_Widget_InteractiveCode_3233133395____hygCtx___hyg_1____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec___closed__0_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec___closed__0_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle___closed__1_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 121, 112, 115, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [99, 116, 120, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [117, 115, 101, 114, 78, 97, 109, 101, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [103, 111, 97, 108, 80, 114, 101, 102, 105, 120, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 118, 97, 114, 73, 100, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_45__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_45____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_45_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_45__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_instToJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_45_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_45__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveGoal___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableInteractiveGoal_enc_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableInteractiveGoal___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveGoal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveGoal___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableInteractiveGoal_dec_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableInteractiveGoal___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveGoal___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveGoal___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveGoal___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveGoal___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instRpcEncodableInteractiveGoal___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveGoal___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_instRpcEncodableInteractiveGoal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveGoal___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [114, 97, 110, 103, 101, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 101, 114, 109, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_36__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_36____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_36_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_36__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_instToJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_36_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_36__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveTermGoal___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableInteractiveTermGoal_enc_00___x40_Lean_Widget_InteractiveGoal_2553565095____hygCtx___hyg_1_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableInteractiveTermGoal___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveTermGoal___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveTermGoal___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableInteractiveTermGoal_dec_00___x40_Lean_Widget_InteractiveGoal_2553565095____hygCtx___hyg_1____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableInteractiveTermGoal___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveTermGoal___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveTermGoal___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveTermGoal___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveTermGoal___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instRpcEncodableInteractiveTermGoal___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveTermGoal___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_instRpcEncodableInteractiveTermGoal: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveTermGoal___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_List_filterTR_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_filterTR_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__1_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__2_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__3_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 58, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__4_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__3_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__5_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 58, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__6_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__7_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 58, 61, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__8_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__7_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__9_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__10_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_InteractiveGoalCore_pretty___closed__0_value:
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
    m_data: [99, 97, 115, 101, 32, 0],
};
static mut l_Lean_Widget_InteractiveGoalCore_pretty___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_InteractiveGoalCore_pretty___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_InteractiveGoalCore_pretty___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_InteractiveGoalCore_pretty___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_InteractiveGoalCore_pretty___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_InteractiveGoalCore_pretty___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_InteractiveTermGoal_pretty___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Widget_InteractiveTermGoal_pretty___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_InteractiveTermGoal_pretty___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 111, 97, 108, 115, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_28__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_28_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_28_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_28__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_instToJsonRpcEncodablePacket_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_28_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_28__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveGoals___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableInteractiveGoals_enc_00___x40_Lean_Widget_InteractiveGoal_1490754142____hygCtx___hyg_1_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableInteractiveGoals___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveGoals___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveGoals___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableInteractiveGoals_dec_00___x40_Lean_Widget_InteractiveGoal_1490754142____hygCtx___hyg_1____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableInteractiveGoals___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveGoals___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableInteractiveGoals___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveGoals___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveGoals___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instRpcEncodableInteractiveGoals___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveGoals___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_instRpcEncodableInteractiveGoals: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableInteractiveGoals___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instAppendInteractiveGoals___closed__0_value:
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
    m_fun: l_Lean_Widget_InteractiveGoals_append___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Widget_instAppendInteractiveGoals___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instAppendInteractiveGoals___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_instAppendInteractiveGoals: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instAppendInteractiveGoals___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_instEmptyCollectionInteractiveGoals___closed__0_value:
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
static mut l_Lean_Widget_instEmptyCollectionInteractiveGoals___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instEmptyCollectionInteractiveGoals___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Widget_instEmptyCollectionInteractiveGoals: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instEmptyCollectionInteractiveGoals___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged___closed__0_value: crate::leanh::LeanStringObject<113> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 113, m_capacity: 113, m_length: 112, m_data: [86, 97, 108, 117, 101, 32, 111, 109, 105, 116, 116, 101, 100, 32, 115, 105, 110, 99, 101, 32, 96, 112, 112, 46, 115, 104, 111, 119, 76, 101, 116, 86, 97, 108, 117, 101, 115, 96, 32, 105, 115, 32, 102, 97, 108, 115, 101, 32, 97, 110, 100, 32, 116, 104, 101, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 39, 115, 32, 100, 101, 112, 116, 104, 32, 101, 120, 99, 101, 101, 100, 115, 32, 96, 112, 112, 46, 115, 104, 111, 119, 76, 101, 116, 86, 97, 108, 117, 101, 115, 46, 116, 104, 114, 101, 115, 104, 111, 108, 100, 96, 46, 0]};
static mut l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged___closed__1_value: crate::leanh::LeanStringObject<158> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 158, m_capacity: 158, m_length: 157, m_data: [86, 97, 108, 117, 101, 32, 111, 109, 105, 116, 116, 101, 100, 32, 115, 105, 110, 99, 101, 32, 96, 112, 112, 46, 115, 104, 111, 119, 76, 101, 116, 86, 97, 108, 117, 101, 115, 96, 32, 105, 115, 32, 102, 97, 108, 115, 101, 32, 97, 110, 100, 32, 116, 104, 101, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 39, 115, 32, 100, 101, 112, 116, 104, 32, 101, 120, 99, 101, 101, 100, 115, 32, 98, 111, 116, 104, 32, 96, 112, 112, 46, 115, 104, 111, 119, 76, 101, 116, 86, 97, 108, 117, 101, 115, 46, 116, 97, 99, 116, 105, 99, 46, 116, 104, 114, 101, 115, 104, 111, 108, 100, 96, 32, 97, 110, 100, 32, 96, 112, 112, 46, 115, 104, 111, 119, 76, 101, 116, 86, 97, 108, 117, 101, 115, 46, 116, 104, 114, 101, 115, 104, 111, 108, 100, 96, 46, 0]};
static mut l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Delaborator_delab___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_addInteractiveHypothesisBundle___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Widget_addInteractiveHypothesisBundle___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_addInteractiveHypothesisBundle___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_addInteractiveHypothesisBundle___closed__1_value:
    crate::leanh::LeanStringObject<72> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Widget_addInteractiveHypothesisBundle___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_addInteractiveHypothesisBundle___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Widget_addInteractiveHypothesisBundle___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_addInteractiveHypothesisBundle___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Widget_withGoalCtx___redArg___lam__1___closed__0_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Widget_withGoalCtx___redArg___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_withGoalCtx___redArg___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Widget_withGoalCtx___redArg___lam__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Widget_withGoalCtx___redArg___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4_spec__9___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4_spec__9___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4_spec__9___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_goalToInteractive___lam__0___closed__0_value:
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
static mut l_Lean_Widget_goalToInteractive___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_goalToInteractive___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_goalToInteractive___lam__0___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4_spec__9___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Widget_goalToInteractive___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_goalToInteractive___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Widget_goalToInteractive___lam__0___closed__2_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4_spec__9___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Widget_goalToInteractive___lam__0___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Widget_goalToInteractive___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_goalToInteractive___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3946_ = l_Lean_Widget_instInhabitedTaggedText_default(crate::leanh::lean_box(0));
    return v___x_3946_;
}
pub unsafe fn _init_l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3947_ = crate::leanh::lean_box(0);
    v___x_3948_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__1_once
        ),
        _init_l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__1,
    );
    v___x_3949_ = l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default___closed__0;
    v___x_3950_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3950_, 0, v___x_3949_);
    crate::leanh::lean_ctor_set(v___x_3950_, 1, v___x_3949_);
    crate::leanh::lean_ctor_set(v___x_3950_, 2, v___x_3948_);
    crate::leanh::lean_ctor_set(v___x_3950_, 3, v___x_3947_);
    crate::leanh::lean_ctor_set(v___x_3950_, 4, v___x_3947_);
    crate::leanh::lean_ctor_set(v___x_3950_, 5, v___x_3947_);
    crate::leanh::lean_ctor_set(v___x_3950_, 6, v___x_3947_);
    crate::leanh::lean_ctor_set(v___x_3950_, 7, v___x_3947_);
    return v___x_3950_;
}
pub unsafe fn _init_l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3951_ = crate::leanh::lean_obj_once(
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3952_ = l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default;
    return v___x_3952_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(
    mut v_j_3953_: *mut crate::leanh::LeanObject,
    mut v_k_3954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3955_ = l_Lean_Json_getObjValD(v_j_3953_, v_k_3954_);
    v___x_3956_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3956_, 0, v___x_3955_);
    return v___x_3956_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0___boxed(
    mut v_j_3957_: *mut crate::leanh::LeanObject,
    mut v_k_3958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3959_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_j_3957_, v_k_3958_);
    crate::leanh::lean_dec_ref(v_k_3958_);
    return v_res_3959_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1_spec__1(
    mut v_x_3962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3962_) == 0 {
        let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3963_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1_spec__1___closed__0;
        return v___x_3963_;
    } else {
        let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3964_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3964_, 0, v_x_3962_);
        v___x_3965_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3965_, 0, v___x_3964_);
        return v___x_3965_;
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1(
    mut v_j_3966_: *mut crate::leanh::LeanObject,
    mut v_k_3967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3968_ = l_Lean_Json_getObjValD(v_j_3966_, v_k_3967_);
    v___x_3969_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1_spec__1(v___x_3968_);
    return v___x_3969_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1___boxed(
    mut v_j_3970_: *mut crate::leanh::LeanObject,
    mut v_k_3971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3972_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1(v_j_3970_, v_k_3971_);
    crate::leanh::lean_dec_ref(v_k_3971_);
    return v_res_3972_;
}
pub unsafe fn l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_(
    mut v_json_3981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4008_: u8 = 0;
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4013_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3982_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
                crate::leanh::lean_inc_n(v_json_3981_, 7);
                v___x_3983_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_3981_, v___x_3982_);
                v_a_3984_ = crate::leanh::lean_ctor_get(v___x_3983_, 0);
                crate::leanh::lean_inc(v_a_3984_);
                crate::leanh::lean_dec_ref(v___x_3983_);
                v___x_3985_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
                v___x_3986_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_3981_, v___x_3985_);
                v_a_3987_ = crate::leanh::lean_ctor_get(v___x_3986_, 0);
                crate::leanh::lean_inc(v_a_3987_);
                crate::leanh::lean_dec_ref(v___x_3986_);
                v___x_3988_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
                v___x_3989_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_3981_, v___x_3988_);
                v_a_3990_ = crate::leanh::lean_ctor_get(v___x_3989_, 0);
                crate::leanh::lean_inc(v_a_3990_);
                crate::leanh::lean_dec_ref(v___x_3989_);
                v___x_3991_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
                v___x_3992_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1(v_json_3981_, v___x_3991_);
                v_a_3993_ = crate::leanh::lean_ctor_get(v___x_3992_, 0);
                crate::leanh::lean_inc(v_a_3993_);
                crate::leanh::lean_dec_ref(v___x_3992_);
                v___x_3994_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
                v___x_3995_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1(v_json_3981_, v___x_3994_);
                v_a_3996_ = crate::leanh::lean_ctor_get(v___x_3995_, 0);
                crate::leanh::lean_inc(v_a_3996_);
                crate::leanh::lean_dec_ref(v___x_3995_);
                v___x_3997_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__5_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
                v___x_3998_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1(v_json_3981_, v___x_3997_);
                v_a_3999_ = crate::leanh::lean_ctor_get(v___x_3998_, 0);
                crate::leanh::lean_inc(v_a_3999_);
                crate::leanh::lean_dec_ref(v___x_3998_);
                v___x_4000_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
                v___x_4001_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1(v_json_3981_, v___x_4000_);
                v_a_4002_ = crate::leanh::lean_ctor_get(v___x_4001_, 0);
                crate::leanh::lean_inc(v_a_4002_);
                crate::leanh::lean_dec_ref(v___x_4001_);
                v___x_4003_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
                v___x_4004_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1(v_json_3981_, v___x_4003_);
                v_a_4005_ = crate::leanh::lean_ctor_get(v___x_4004_, 0);
                v_isSharedCheck_4013_ = (!crate::leanh::lean_is_exclusive(v___x_4004_)) as u8;
                if v_isSharedCheck_4013_ == 0 {
                    v___x_4007_ = v___x_4004_;
                    v_isShared_4008_ = v_isSharedCheck_4013_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4005_);
                    crate::leanh::lean_dec(v___x_4004_);
                    v___x_4007_ = crate::leanh::lean_box(0);
                    v_isShared_4008_ = v_isSharedCheck_4013_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4009_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4009_, 0, v_a_3984_);
                crate::leanh::lean_ctor_set(v___x_4009_, 1, v_a_3987_);
                crate::leanh::lean_ctor_set(v___x_4009_, 2, v_a_3990_);
                crate::leanh::lean_ctor_set(v___x_4009_, 3, v_a_3993_);
                crate::leanh::lean_ctor_set(v___x_4009_, 4, v_a_3996_);
                crate::leanh::lean_ctor_set(v___x_4009_, 5, v_a_3999_);
                crate::leanh::lean_ctor_set(v___x_4009_, 6, v_a_4002_);
                crate::leanh::lean_ctor_set(v___x_4009_, 7, v_a_4005_);
                if v_isShared_4008_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4007_, 0, v___x_4009_);
                    v___x_4011_ = v___x_4007_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4012_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4012_, 0, v___x_4009_);
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
    mut v_k_4016_: *mut crate::leanh::LeanObject,
    mut v_x_4017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4017_) == 0 {
        let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_k_4016_);
        v___x_4018_ = crate::leanh::lean_box(0);
        return v___x_4018_;
    } else {
        let mut v_val_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4019_ = crate::leanh::lean_ctor_get(v_x_4017_, 0);
        crate::leanh::lean_inc(v_val_4019_);
        v___x_4020_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4020_, 0, v_k_4016_);
        crate::leanh::lean_ctor_set(v___x_4020_, 1, v_val_4019_);
        v___x_4021_ = crate::leanh::lean_box(0);
        v___x_4022_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4022_, 0, v___x_4020_);
        crate::leanh::lean_ctor_set(v___x_4022_, 1, v___x_4021_);
        return v___x_4022_;
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__0___boxed(
    mut v_k_4023_: *mut crate::leanh::LeanObject,
    mut v_x_4024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4025_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__0(v_k_4023_, v_x_4024_);
    crate::leanh::lean_dec(v_x_4024_);
    return v_res_4025_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__1(
    mut v_a_4026_: *mut crate::leanh::LeanObject,
    mut v_a_4027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4026_) == 0 {
                    v___x_4028_ = lean_array_to_list(v_a_4027_);
                    return v___x_4028_;
                } else {
                    v_head_4029_ = crate::leanh::lean_ctor_get(v_a_4026_, 0);
                    crate::leanh::lean_inc(v_head_4029_);
                    v_tail_4030_ = crate::leanh::lean_ctor_get(v_a_4026_, 1);
                    crate::leanh::lean_inc(v_tail_4030_);
                    crate::leanh::lean_dec_ref_known(v_a_4026_, 2);
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
    mut v_x_4035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_names_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarIds_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_x3f_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInstance_x3f_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isType_x3f_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInserted_x3f_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRemoved_x3f_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_names_4036_ = crate::leanh::lean_ctor_get(v_x_4035_, 0);
    v_fvarIds_4037_ = crate::leanh::lean_ctor_get(v_x_4035_, 1);
    v_type_4038_ = crate::leanh::lean_ctor_get(v_x_4035_, 2);
    v_val_x3f_4039_ = crate::leanh::lean_ctor_get(v_x_4035_, 3);
    v_isInstance_x3f_4040_ = crate::leanh::lean_ctor_get(v_x_4035_, 4);
    v_isType_x3f_4041_ = crate::leanh::lean_ctor_get(v_x_4035_, 5);
    v_isInserted_x3f_4042_ = crate::leanh::lean_ctor_get(v_x_4035_, 6);
    v_isRemoved_x3f_4043_ = crate::leanh::lean_ctor_get(v_x_4035_, 7);
    v___x_4044_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
    crate::leanh::lean_inc(v_names_4036_);
    v___x_4045_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4045_, 0, v___x_4044_);
    crate::leanh::lean_ctor_set(v___x_4045_, 1, v_names_4036_);
    v___x_4046_ = crate::leanh::lean_box(0);
    v___x_4047_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4047_, 0, v___x_4045_);
    crate::leanh::lean_ctor_set(v___x_4047_, 1, v___x_4046_);
    v___x_4048_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
    crate::leanh::lean_inc(v_fvarIds_4037_);
    v___x_4049_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4049_, 0, v___x_4048_);
    crate::leanh::lean_ctor_set(v___x_4049_, 1, v_fvarIds_4037_);
    v___x_4050_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4050_, 0, v___x_4049_);
    crate::leanh::lean_ctor_set(v___x_4050_, 1, v___x_4046_);
    v___x_4051_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
    crate::leanh::lean_inc(v_type_4038_);
    v___x_4052_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4052_, 0, v___x_4051_);
    crate::leanh::lean_ctor_set(v___x_4052_, 1, v_type_4038_);
    v___x_4053_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4053_, 0, v___x_4052_);
    crate::leanh::lean_ctor_set(v___x_4053_, 1, v___x_4046_);
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
    v___x_4064_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4064_, 0, v___x_4063_);
    crate::leanh::lean_ctor_set(v___x_4064_, 1, v___x_4046_);
    v___x_4065_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4065_, 0, v___x_4061_);
    crate::leanh::lean_ctor_set(v___x_4065_, 1, v___x_4064_);
    v___x_4066_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4066_, 0, v___x_4059_);
    crate::leanh::lean_ctor_set(v___x_4066_, 1, v___x_4065_);
    v___x_4067_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4067_, 0, v___x_4057_);
    crate::leanh::lean_ctor_set(v___x_4067_, 1, v___x_4066_);
    v___x_4068_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4068_, 0, v___x_4055_);
    crate::leanh::lean_ctor_set(v___x_4068_, 1, v___x_4067_);
    v___x_4069_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4069_, 0, v___x_4053_);
    crate::leanh::lean_ctor_set(v___x_4069_, 1, v___x_4068_);
    v___x_4070_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4070_, 0, v___x_4050_);
    crate::leanh::lean_ctor_set(v___x_4070_, 1, v___x_4069_);
    v___x_4071_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4071_, 0, v___x_4047_);
    crate::leanh::lean_ctor_set(v___x_4071_, 1, v___x_4070_);
    v___x_4072_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47_;
    v___x_4073_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__1(v___x_4071_, v___x_4072_);
    v___x_4074_ = l_Lean_Json_mkObj(v___x_4073_);
    crate::leanh::lean_dec(v___x_4073_);
    return v___x_4074_;
}
pub unsafe fn l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47____boxed(
    mut v_x_4075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4076_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47_(v_x_4075_);
    crate::leanh::lean_dec_ref(v_x_4075_);
    return v_res_4076_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3_spec__4(
    mut v_sz_4079_: usize,
    mut v_i_4080_: usize,
    mut v_bs_4081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4082_: u8 = 0;
    let mut v_v_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: usize = 0;
    let mut v___x_4087_: usize = 0;
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4082_ = lean_usize_dec_lt(v_i_4080_, v_sz_4079_);
                if v___x_4082_ == 0 {
                    return v_bs_4081_;
                } else {
                    v_v_4083_ = lean_array_uget(v_bs_4081_, v_i_4080_);
                    v___x_4084_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_4090_: *mut crate::leanh::LeanObject,
    mut v_i_4091_: *mut crate::leanh::LeanObject,
    mut v_bs_4092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4093_: usize = 0;
    let mut v_i_boxed_4094_: usize = 0;
    let mut v_res_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4093_ = crate::leanh::lean_unbox_usize(v_sz_4090_);
    crate::leanh::lean_dec(v_sz_4090_);
    v_i_boxed_4094_ = crate::leanh::lean_unbox_usize(v_i_4091_);
    crate::leanh::lean_dec(v_i_4091_);
    v_res_4095_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3_spec__4(v_sz_boxed_4093_, v_i_boxed_4094_, v_bs_4092_);
    return v_res_4095_;
}
pub unsafe fn l_Array_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3(
    mut v_a_4096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_4097_: usize = 0;
    let mut v___x_4098_: usize = 0;
    let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_4097_ = lean_array_size(v_a_4096_);
    v___x_4098_ = 0usize;
    v___x_4099_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3_spec__4(v_sz_4097_, v___x_4098_, v_a_4096_);
    v___x_4100_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4100_, 0, v___x_4099_);
    return v___x_4100_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0(
    mut v_sz_4101_: usize,
    mut v_i_4102_: usize,
    mut v_bs_4103_: *mut crate::leanh::LeanObject,
    mut v___y_4104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4105_: u8 = 0;
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: usize = 0;
    let mut v___x_4112_: usize = 0;
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4105_ = lean_usize_dec_lt(v_i_4102_, v_sz_4101_);
                if v___x_4105_ == 0 {
                    v___x_4106_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4106_, 0, v_bs_4103_);
                    crate::leanh::lean_ctor_set(v___x_4106_, 1, v___y_4104_);
                    return v___x_4106_;
                } else {
                    v_v_4107_ = lean_array_uget(v_bs_4103_, v_i_4102_);
                    v___x_4108_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4109_ = lean_array_uset(v_bs_4103_, v_i_4102_, v___x_4108_);
                    v___x_4110_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4110_, 0, v_v_4107_);
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
    mut v_sz_4115_: *mut crate::leanh::LeanObject,
    mut v_i_4116_: *mut crate::leanh::LeanObject,
    mut v_bs_4117_: *mut crate::leanh::LeanObject,
    mut v___y_4118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4119_: usize = 0;
    let mut v_i_boxed_4120_: usize = 0;
    let mut v_res_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4119_ = crate::leanh::lean_unbox_usize(v_sz_4115_);
    crate::leanh::lean_dec(v_sz_4115_);
    v_i_boxed_4120_ = crate::leanh::lean_unbox_usize(v_i_4116_);
    crate::leanh::lean_dec(v_i_4116_);
    v_res_4121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0(v_sz_boxed_4119_, v_i_boxed_4120_, v_bs_4117_, v___y_4118_);
    return v_res_4121_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__1(
    mut v_sz_4122_: usize,
    mut v_i_4123_: usize,
    mut v_bs_4124_: *mut crate::leanh::LeanObject,
    mut v___y_4125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4126_: u8 = 0;
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: usize = 0;
    let mut v___x_4134_: usize = 0;
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4126_ = lean_usize_dec_lt(v_i_4123_, v_sz_4122_);
                if v___x_4126_ == 0 {
                    v___x_4127_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4127_, 0, v_bs_4124_);
                    crate::leanh::lean_ctor_set(v___x_4127_, 1, v___y_4125_);
                    return v___x_4127_;
                } else {
                    v_v_4128_ = lean_array_uget(v_bs_4124_, v_i_4123_);
                    v___x_4129_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4130_ = lean_array_uset(v_bs_4124_, v_i_4123_, v___x_4129_);
                    v___x_4131_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_v_4128_,
                        v___x_4126_,
                    );
                    v___x_4132_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4132_, 0, v___x_4131_);
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
    mut v_sz_4137_: *mut crate::leanh::LeanObject,
    mut v_i_4138_: *mut crate::leanh::LeanObject,
    mut v_bs_4139_: *mut crate::leanh::LeanObject,
    mut v___y_4140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4141_: usize = 0;
    let mut v_i_boxed_4142_: usize = 0;
    let mut v_res_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4141_ = crate::leanh::lean_unbox_usize(v_sz_4137_);
    crate::leanh::lean_dec(v_sz_4137_);
    v_i_boxed_4142_ = crate::leanh::lean_unbox_usize(v_i_4138_);
    crate::leanh::lean_dec(v_i_4138_);
    v_res_4143_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__1(v_sz_boxed_4141_, v_i_boxed_4142_, v_bs_4139_, v___y_4140_);
    return v_res_4143_;
}
pub unsafe fn l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(
    mut v_x_4147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4151_: u8 = 0;
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4160_: u8 = 0;
    let mut v_a_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4172_: u8 = 0;
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4186_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_4147_) {
                0 => {
                    v_a_4148_ = crate::leanh::lean_ctor_get(v_x_4147_, 0);
                    v_isSharedCheck_4160_ = (!crate::leanh::lean_is_exclusive(v_x_4147_)) as u8;
                    if v_isSharedCheck_4160_ == 0 {
                        v___x_4150_ = v_x_4147_;
                        v_isShared_4151_ = v_isSharedCheck_4160_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4148_);
                        crate::leanh::lean_dec(v_x_4147_);
                        v___x_4150_ = crate::leanh::lean_box(0);
                        v_isShared_4151_ = v_isSharedCheck_4160_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_4161_ = crate::leanh::lean_ctor_get(v_x_4147_, 0);
                    crate::leanh::lean_inc_ref(v_a_4161_);
                    crate::leanh::lean_dec_ref_known(v_x_4147_, 1);
                    v___x_4162_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__1;
                    v___x_4163_ = l_Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4_spec__6(v_a_4161_);
                    v___x_4164_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4164_, 0, v___x_4162_);
                    crate::leanh::lean_ctor_set(v___x_4164_, 1, v___x_4163_);
                    v___x_4165_ = crate::leanh::lean_box(0);
                    v___x_4166_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4166_, 0, v___x_4164_);
                    crate::leanh::lean_ctor_set(v___x_4166_, 1, v___x_4165_);
                    v___x_4167_ = l_Lean_Json_mkObj(v___x_4166_);
                    crate::leanh::lean_dec_ref_known(v___x_4166_, 2);
                    return v___x_4167_;
                }
                _ => {
                    v_a_4168_ = crate::leanh::lean_ctor_get(v_x_4147_, 0);
                    v_a_4169_ = crate::leanh::lean_ctor_get(v_x_4147_, 1);
                    v_isSharedCheck_4186_ = (!crate::leanh::lean_is_exclusive(v_x_4147_)) as u8;
                    if v_isSharedCheck_4186_ == 0 {
                        v___x_4171_ = v_x_4147_;
                        v_isShared_4172_ = v_isSharedCheck_4186_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4169_);
                        crate::leanh::lean_inc(v_a_4168_);
                        crate::leanh::lean_dec(v_x_4147_);
                        v___x_4171_ = crate::leanh::lean_box(0);
                        v_isShared_4172_ = v_isSharedCheck_4186_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_4152_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__0;
                if v_isShared_4151_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4150_, 3);
                    v___x_4154_ = v___x_4150_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4159_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_a_4148_);
                    v___x_4154_ = v_reuseFailAlloc_4159_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4155_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4155_, 0, v___x_4152_);
                crate::leanh::lean_ctor_set(v___x_4155_, 1, v___x_4154_);
                v___x_4156_ = crate::leanh::lean_box(0);
                v___x_4157_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4157_, 0, v___x_4155_);
                crate::leanh::lean_ctor_set(v___x_4157_, 1, v___x_4156_);
                v___x_4158_ = l_Lean_Json_mkObj(v___x_4157_);
                crate::leanh::lean_dec_ref_known(v___x_4157_, 2);
                return v___x_4158_;
            }
            3 => {
                v___x_4173_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__2;
                v___x_4174_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(v_a_4169_);
                v___x_4175_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_4176_ = lean_mk_empty_array_with_capacity(v___x_4175_);
                v___x_4177_ = lean_array_push(v___x_4176_, v_a_4168_);
                v___x_4178_ = lean_array_push(v___x_4177_, v___x_4174_);
                v___x_4179_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4179_, 0, v___x_4178_);
                if v_isShared_4172_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4171_, 0);
                    crate::leanh::lean_ctor_set(v___x_4171_, 1, v___x_4179_);
                    crate::leanh::lean_ctor_set(v___x_4171_, 0, v___x_4173_);
                    v___x_4181_ = v___x_4171_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4185_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4185_, 0, v___x_4173_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4185_, 1, v___x_4179_);
                    v___x_4181_ = v_reuseFailAlloc_4185_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4182_ = crate::leanh::lean_box(0);
                v___x_4183_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4183_, 0, v___x_4181_);
                crate::leanh::lean_ctor_set(v___x_4183_, 1, v___x_4182_);
                v___x_4184_ = l_Lean_Json_mkObj(v___x_4183_);
                crate::leanh::lean_dec_ref_known(v___x_4183_, 2);
                return v___x_4184_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4_spec__6_spec__7(
    mut v_sz_4187_: usize,
    mut v_i_4188_: usize,
    mut v_bs_4189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4190_: u8 = 0;
    let mut v_v_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: usize = 0;
    let mut v___x_4196_: usize = 0;
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4190_ = lean_usize_dec_lt(v_i_4188_, v_sz_4187_);
                if v___x_4190_ == 0 {
                    return v_bs_4189_;
                } else {
                    v_v_4191_ = lean_array_uget(v_bs_4189_, v_i_4188_);
                    v___x_4192_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_a_4199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_4200_: usize = 0;
    let mut v___x_4201_: usize = 0;
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_4200_ = lean_array_size(v_a_4199_);
    v___x_4201_ = 0usize;
    v___x_4202_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4_spec__6_spec__7(v_sz_4200_, v___x_4201_, v_a_4199_);
    v___x_4203_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4203_, 0, v___x_4202_);
    return v___x_4203_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4_spec__6_spec__7___boxed(
    mut v_sz_4204_: *mut crate::leanh::LeanObject,
    mut v_i_4205_: *mut crate::leanh::LeanObject,
    mut v_bs_4206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4207_: usize = 0;
    let mut v_i_boxed_4208_: usize = 0;
    let mut v_res_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4207_ = crate::leanh::lean_unbox_usize(v_sz_4204_);
    crate::leanh::lean_dec(v_sz_4204_);
    v_i_boxed_4208_ = crate::leanh::lean_unbox_usize(v_i_4205_);
    crate::leanh::lean_dec(v_i_4205_);
    v_res_4209_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4_spec__6_spec__7(v_sz_boxed_4207_, v_i_boxed_4208_, v_bs_4206_);
    return v_res_4209_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___redArg(
    mut v_f_4210_: *mut crate::leanh::LeanObject,
    mut v_x_4211_: *mut crate::leanh::LeanObject,
    mut v___y_4212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4216_: u8 = 0;
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4221_: u8 = 0;
    let mut v_a_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4225_: u8 = 0;
    let mut v_sz_4226_: usize = 0;
    let mut v___x_4227_: usize = 0;
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4233_: u8 = 0;
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4240_: u8 = 0;
    let mut v_isSharedCheck_4241_: u8 = 0;
    let mut v_a_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4246_: u8 = 0;
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4255_: u8 = 0;
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4262_: u8 = 0;
    let mut v_isSharedCheck_4263_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_4211_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_f_4210_);
                    v_a_4213_ = crate::leanh::lean_ctor_get(v_x_4211_, 0);
                    v_isSharedCheck_4221_ = (!crate::leanh::lean_is_exclusive(v_x_4211_)) as u8;
                    if v_isSharedCheck_4221_ == 0 {
                        v___x_4215_ = v_x_4211_;
                        v_isShared_4216_ = v_isSharedCheck_4221_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4213_);
                        crate::leanh::lean_dec(v_x_4211_);
                        v___x_4215_ = crate::leanh::lean_box(0);
                        v_isShared_4216_ = v_isSharedCheck_4221_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_4222_ = crate::leanh::lean_ctor_get(v_x_4211_, 0);
                    v_isSharedCheck_4241_ = (!crate::leanh::lean_is_exclusive(v_x_4211_)) as u8;
                    if v_isSharedCheck_4241_ == 0 {
                        v___x_4224_ = v_x_4211_;
                        v_isShared_4225_ = v_isSharedCheck_4241_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4222_);
                        crate::leanh::lean_dec(v_x_4211_);
                        v___x_4224_ = crate::leanh::lean_box(0);
                        v_isShared_4225_ = v_isSharedCheck_4241_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v_a_4242_ = crate::leanh::lean_ctor_get(v_x_4211_, 0);
                    v_a_4243_ = crate::leanh::lean_ctor_get(v_x_4211_, 1);
                    v_isSharedCheck_4263_ = (!crate::leanh::lean_is_exclusive(v_x_4211_)) as u8;
                    if v_isSharedCheck_4263_ == 0 {
                        v___x_4245_ = v_x_4211_;
                        v_isShared_4246_ = v_isSharedCheck_4263_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4243_);
                        crate::leanh::lean_inc(v_a_4242_);
                        crate::leanh::lean_dec(v_x_4211_);
                        v___x_4245_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4220_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_a_4213_);
                    v___x_4218_ = v_reuseFailAlloc_4220_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4219_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4219_, 0, v___x_4218_);
                crate::leanh::lean_ctor_set(v___x_4219_, 1, v___y_4212_);
                return v___x_4219_;
            }
            3 => {
                v_sz_4226_ = lean_array_size(v_a_4222_);
                v___x_4227_ = 0usize;
                v___x_4228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2_spec__2___redArg(v_f_4210_, v_sz_4226_, v___x_4227_, v_a_4222_, v___y_4212_);
                v_fst_4229_ = crate::leanh::lean_ctor_get(v___x_4228_, 0);
                v_snd_4230_ = crate::leanh::lean_ctor_get(v___x_4228_, 1);
                v_isSharedCheck_4240_ = (!crate::leanh::lean_is_exclusive(v___x_4228_)) as u8;
                if v_isSharedCheck_4240_ == 0 {
                    v___x_4232_ = v___x_4228_;
                    v_isShared_4233_ = v_isSharedCheck_4240_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4230_);
                    crate::leanh::lean_inc(v_fst_4229_);
                    crate::leanh::lean_dec(v___x_4228_);
                    v___x_4232_ = crate::leanh::lean_box(0);
                    v_isShared_4233_ = v_isSharedCheck_4240_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4225_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4224_, 0, v_fst_4229_);
                    v___x_4235_ = v___x_4224_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4239_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_fst_4229_);
                    v___x_4235_ = v_reuseFailAlloc_4239_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4233_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4232_, 0, v___x_4235_);
                    v___x_4237_ = v___x_4232_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4238_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4238_, 0, v___x_4235_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4238_, 1, v_snd_4230_);
                    v___x_4237_ = v_reuseFailAlloc_4238_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4237_;
            }
            7 => {
                crate::leanh::lean_inc_ref(v_f_4210_);
                v___x_4247_ = crate::leanh::lean_apply_2(v_f_4210_, v_a_4242_, v___y_4212_);
                v_fst_4248_ = crate::leanh::lean_ctor_get(v___x_4247_, 0);
                crate::leanh::lean_inc(v_fst_4248_);
                v_snd_4249_ = crate::leanh::lean_ctor_get(v___x_4247_, 1);
                crate::leanh::lean_inc(v_snd_4249_);
                crate::leanh::lean_dec_ref(v___x_4247_);
                v___x_4250_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___redArg(v_f_4210_, v_a_4243_, v_snd_4249_);
                v_fst_4251_ = crate::leanh::lean_ctor_get(v___x_4250_, 0);
                v_snd_4252_ = crate::leanh::lean_ctor_get(v___x_4250_, 1);
                v_isSharedCheck_4262_ = (!crate::leanh::lean_is_exclusive(v___x_4250_)) as u8;
                if v_isSharedCheck_4262_ == 0 {
                    v___x_4254_ = v___x_4250_;
                    v_isShared_4255_ = v_isSharedCheck_4262_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4252_);
                    crate::leanh::lean_inc(v_fst_4251_);
                    crate::leanh::lean_dec(v___x_4250_);
                    v___x_4254_ = crate::leanh::lean_box(0);
                    v_isShared_4255_ = v_isSharedCheck_4262_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_4246_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4245_, 1, v_fst_4251_);
                    crate::leanh::lean_ctor_set(v___x_4245_, 0, v_fst_4248_);
                    v___x_4257_ = v___x_4245_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4261_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4261_, 0, v_fst_4248_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4261_, 1, v_fst_4251_);
                    v___x_4257_ = v_reuseFailAlloc_4261_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4255_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4254_, 0, v___x_4257_);
                    v___x_4259_ = v___x_4254_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4260_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4260_, 0, v___x_4257_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4260_, 1, v_snd_4252_);
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
    mut v_f_4264_: *mut crate::leanh::LeanObject,
    mut v_sz_4265_: usize,
    mut v_i_4266_: usize,
    mut v_bs_4267_: *mut crate::leanh::LeanObject,
    mut v___y_4268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4269_: u8 = 0;
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: usize = 0;
    let mut v___x_4278_: usize = 0;
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4269_ = lean_usize_dec_lt(v_i_4266_, v_sz_4265_);
                if v___x_4269_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_4264_);
                    v___x_4270_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4270_, 0, v_bs_4267_);
                    crate::leanh::lean_ctor_set(v___x_4270_, 1, v___y_4268_);
                    return v___x_4270_;
                } else {
                    v_v_4271_ = lean_array_uget_borrowed(v_bs_4267_, v_i_4266_);
                    crate::leanh::lean_inc(v_v_4271_);
                    crate::leanh::lean_inc_ref(v_f_4264_);
                    v___x_4272_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___redArg(v_f_4264_, v_v_4271_, v___y_4268_);
                    v_fst_4273_ = crate::leanh::lean_ctor_get(v___x_4272_, 0);
                    crate::leanh::lean_inc(v_fst_4273_);
                    v_snd_4274_ = crate::leanh::lean_ctor_get(v___x_4272_, 1);
                    crate::leanh::lean_inc(v_snd_4274_);
                    crate::leanh::lean_dec_ref(v___x_4272_);
                    v___x_4275_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_f_4281_: *mut crate::leanh::LeanObject,
    mut v_sz_4282_: *mut crate::leanh::LeanObject,
    mut v_i_4283_: *mut crate::leanh::LeanObject,
    mut v_bs_4284_: *mut crate::leanh::LeanObject,
    mut v___y_4285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4286_: usize = 0;
    let mut v_i_boxed_4287_: usize = 0;
    let mut v_res_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4286_ = crate::leanh::lean_unbox_usize(v_sz_4282_);
    crate::leanh::lean_dec(v_sz_4282_);
    v_i_boxed_4287_ = crate::leanh::lean_unbox_usize(v_i_4283_);
    crate::leanh::lean_dec(v_i_4283_);
    v_res_4288_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2_spec__2___redArg(v_f_4281_, v_sz_boxed_4286_, v_i_boxed_4287_, v_bs_4284_, v___y_4285_);
    return v_res_4288_;
}
pub unsafe fn l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_(
    mut v_a_4290_: *mut crate::leanh::LeanObject,
    mut v_a_4291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_names_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarIds_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_x3f_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInstance_x3f_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isType_x3f_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInserted_x3f_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRemoved_x3f_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4302_: u8 = 0;
    let mut v_sz_4303_: usize = 0;
    let mut v___x_4304_: usize = 0;
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4308_: usize = 0;
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4318_: u8 = 0;
    let mut v___x_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4346_: u8 = 0;
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: u8 = 0;
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4352_: u8 = 0;
    let mut v___y_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4362_: u8 = 0;
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: u8 = 0;
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4368_: u8 = 0;
    let mut v___y_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4377_: u8 = 0;
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: u8 = 0;
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4383_: u8 = 0;
    let mut v_fst_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4391_: u8 = 0;
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: u8 = 0;
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4397_: u8 = 0;
    let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4402_: u8 = 0;
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4410_: u8 = 0;
    let mut v_isSharedCheck_4411_: u8 = 0;
    let mut v_isSharedCheck_4412_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_names_4292_ = crate::leanh::lean_ctor_get(v_a_4290_, 0);
                v_fvarIds_4293_ = crate::leanh::lean_ctor_get(v_a_4290_, 1);
                v_type_4294_ = crate::leanh::lean_ctor_get(v_a_4290_, 2);
                v_val_x3f_4295_ = crate::leanh::lean_ctor_get(v_a_4290_, 3);
                v_isInstance_x3f_4296_ = crate::leanh::lean_ctor_get(v_a_4290_, 4);
                v_isType_x3f_4297_ = crate::leanh::lean_ctor_get(v_a_4290_, 5);
                v_isInserted_x3f_4298_ = crate::leanh::lean_ctor_get(v_a_4290_, 6);
                v_isRemoved_x3f_4299_ = crate::leanh::lean_ctor_get(v_a_4290_, 7);
                v_isSharedCheck_4412_ = (!crate::leanh::lean_is_exclusive(v_a_4290_)) as u8;
                if v_isSharedCheck_4412_ == 0 {
                    v___x_4301_ = v_a_4290_;
                    v_isShared_4302_ = v_isSharedCheck_4412_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_isRemoved_x3f_4299_);
                    crate::leanh::lean_inc(v_isInserted_x3f_4298_);
                    crate::leanh::lean_inc(v_isType_x3f_4297_);
                    crate::leanh::lean_inc(v_isInstance_x3f_4296_);
                    crate::leanh::lean_inc(v_val_x3f_4295_);
                    crate::leanh::lean_inc(v_type_4294_);
                    crate::leanh::lean_inc(v_fvarIds_4293_);
                    crate::leanh::lean_inc(v_names_4292_);
                    crate::leanh::lean_dec(v_a_4290_);
                    v___x_4301_ = crate::leanh::lean_box(0);
                    v_isShared_4302_ = v_isSharedCheck_4412_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_sz_4303_ = lean_array_size(v_names_4292_);
                v___x_4304_ = 0usize;
                v___x_4305_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0(v_sz_4303_, v___x_4304_, v_names_4292_, v_a_4291_);
                v_fst_4306_ = crate::leanh::lean_ctor_get(v___x_4305_, 0);
                crate::leanh::lean_inc(v_fst_4306_);
                v_snd_4307_ = crate::leanh::lean_ctor_get(v___x_4305_, 1);
                crate::leanh::lean_inc(v_snd_4307_);
                crate::leanh::lean_dec_ref(v___x_4305_);
                v_sz_4308_ = lean_array_size(v_fvarIds_4293_);
                v___x_4309_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__1(v_sz_4308_, v___x_4304_, v_fvarIds_4293_, v_snd_4307_);
                v_fst_4310_ = crate::leanh::lean_ctor_get(v___x_4309_, 0);
                crate::leanh::lean_inc(v_fst_4310_);
                v_snd_4311_ = crate::leanh::lean_ctor_get(v___x_4309_, 1);
                crate::leanh::lean_inc(v_snd_4311_);
                crate::leanh::lean_dec_ref(v___x_4309_);
                v___x_4312_ = l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc___closed__0_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_;
                v___x_4313_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___redArg(v___x_4312_, v_type_4294_, v_snd_4311_);
                v_fst_4314_ = crate::leanh::lean_ctor_get(v___x_4313_, 0);
                v_snd_4315_ = crate::leanh::lean_ctor_get(v___x_4313_, 1);
                v_isSharedCheck_4411_ = (!crate::leanh::lean_is_exclusive(v___x_4313_)) as u8;
                if v_isSharedCheck_4411_ == 0 {
                    v___x_4317_ = v___x_4313_;
                    v_isShared_4318_ = v_isSharedCheck_4411_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4315_);
                    crate::leanh::lean_inc(v_fst_4314_);
                    crate::leanh::lean_dec(v___x_4313_);
                    v___x_4317_ = crate::leanh::lean_box(0);
                    v_isShared_4318_ = v_isSharedCheck_4411_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4319_ = l_Array_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3(v_fst_4306_);
                v___x_4320_ = l_Array_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3(v_fst_4310_);
                v___x_4321_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(v_fst_4314_);
                if crate::leanh::lean_obj_tag(v_val_x3f_4295_) == 0 {
                    v___x_4398_ = crate::leanh::lean_box(0);
                    v_fst_4385_ = v___x_4398_;
                    v_snd_4386_ = v_snd_4315_;
                    state = 15;
                    continue;
                } else {
                    v_val_4399_ = crate::leanh::lean_ctor_get(v_val_x3f_4295_, 0);
                    v_isSharedCheck_4410_ =
                        (!crate::leanh::lean_is_exclusive(v_val_x3f_4295_)) as u8;
                    if v_isSharedCheck_4410_ == 0 {
                        v___x_4401_ = v_val_x3f_4295_;
                        v_isShared_4402_ = v_isSharedCheck_4410_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4399_);
                        crate::leanh::lean_dec(v_val_x3f_4295_);
                        v___x_4401_ = crate::leanh::lean_box(0);
                        v_isShared_4402_ = v_isSharedCheck_4410_;
                        state = 18;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4302_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4301_, 7, v_fst_4327_);
                    crate::leanh::lean_ctor_set(v___x_4301_, 6, v___y_4326_);
                    crate::leanh::lean_ctor_set(v___x_4301_, 5, v___y_4325_);
                    crate::leanh::lean_ctor_set(v___x_4301_, 4, v___y_4324_);
                    crate::leanh::lean_ctor_set(v___x_4301_, 3, v___y_4323_);
                    crate::leanh::lean_ctor_set(v___x_4301_, 2, v___x_4321_);
                    crate::leanh::lean_ctor_set(v___x_4301_, 1, v___x_4320_);
                    crate::leanh::lean_ctor_set(v___x_4301_, 0, v___x_4319_);
                    v___x_4330_ = v___x_4301_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4335_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 0, v___x_4319_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 1, v___x_4320_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 2, v___x_4321_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 3, v___y_4323_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 4, v___y_4324_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 5, v___y_4325_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 6, v___y_4326_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 7, v_fst_4327_);
                    v___x_4330_ = v_reuseFailAlloc_4335_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4331_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47_(v___x_4330_);
                crate::leanh::lean_dec_ref(v___x_4330_);
                if v_isShared_4318_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4317_, 1, v_snd_4328_);
                    crate::leanh::lean_ctor_set(v___x_4317_, 0, v___x_4331_);
                    v___x_4333_ = v___x_4317_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4334_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4334_, 0, v___x_4331_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4334_, 1, v_snd_4328_);
                    v___x_4333_ = v_reuseFailAlloc_4334_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4333_;
            }
            6 => {
                if crate::leanh::lean_obj_tag(v_isRemoved_x3f_4299_) == 0 {
                    v___x_4342_ = crate::leanh::lean_box(0);
                    v___y_4323_ = v___y_4337_;
                    v___y_4324_ = v___y_4338_;
                    v___y_4325_ = v___y_4339_;
                    v___y_4326_ = v_fst_4340_;
                    v_fst_4327_ = v___x_4342_;
                    v_snd_4328_ = v_snd_4341_;
                    state = 3;
                    continue;
                } else {
                    v_val_4343_ = crate::leanh::lean_ctor_get(v_isRemoved_x3f_4299_, 0);
                    v_isSharedCheck_4352_ =
                        (!crate::leanh::lean_is_exclusive(v_isRemoved_x3f_4299_)) as u8;
                    if v_isSharedCheck_4352_ == 0 {
                        v___x_4345_ = v_isRemoved_x3f_4299_;
                        v_isShared_4346_ = v_isSharedCheck_4352_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4343_);
                        crate::leanh::lean_dec(v_isRemoved_x3f_4299_);
                        v___x_4345_ = crate::leanh::lean_box(0);
                        v_isShared_4346_ = v_isSharedCheck_4352_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                v___x_4347_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_4348_ = (crate::leanh::lean_unbox(v_val_4343_) as u8);
                crate::leanh::lean_dec(v_val_4343_);
                crate::leanh::lean_ctor_set_uint8(v___x_4347_, 0 as u32, v___x_4348_);
                if v_isShared_4346_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4345_, 0, v___x_4347_);
                    v___x_4350_ = v___x_4345_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4351_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4351_, 0, v___x_4347_);
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
                if crate::leanh::lean_obj_tag(v_isInserted_x3f_4298_) == 0 {
                    v___x_4358_ = crate::leanh::lean_box(0);
                    v___y_4337_ = v___y_4354_;
                    v___y_4338_ = v___y_4355_;
                    v___y_4339_ = v_fst_4356_;
                    v_fst_4340_ = v___x_4358_;
                    v_snd_4341_ = v_snd_4357_;
                    state = 6;
                    continue;
                } else {
                    v_val_4359_ = crate::leanh::lean_ctor_get(v_isInserted_x3f_4298_, 0);
                    v_isSharedCheck_4368_ =
                        (!crate::leanh::lean_is_exclusive(v_isInserted_x3f_4298_)) as u8;
                    if v_isSharedCheck_4368_ == 0 {
                        v___x_4361_ = v_isInserted_x3f_4298_;
                        v_isShared_4362_ = v_isSharedCheck_4368_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4359_);
                        crate::leanh::lean_dec(v_isInserted_x3f_4298_);
                        v___x_4361_ = crate::leanh::lean_box(0);
                        v_isShared_4362_ = v_isSharedCheck_4368_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                v___x_4363_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_4364_ = (crate::leanh::lean_unbox(v_val_4359_) as u8);
                crate::leanh::lean_dec(v_val_4359_);
                crate::leanh::lean_ctor_set_uint8(v___x_4363_, 0 as u32, v___x_4364_);
                if v_isShared_4362_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4361_, 0, v___x_4363_);
                    v___x_4366_ = v___x_4361_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4367_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4367_, 0, v___x_4363_);
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
                if crate::leanh::lean_obj_tag(v_isType_x3f_4297_) == 0 {
                    v___x_4373_ = crate::leanh::lean_box(0);
                    v___y_4354_ = v___y_4370_;
                    v___y_4355_ = v_fst_4371_;
                    v_fst_4356_ = v___x_4373_;
                    v_snd_4357_ = v_snd_4372_;
                    state = 9;
                    continue;
                } else {
                    v_val_4374_ = crate::leanh::lean_ctor_get(v_isType_x3f_4297_, 0);
                    v_isSharedCheck_4383_ =
                        (!crate::leanh::lean_is_exclusive(v_isType_x3f_4297_)) as u8;
                    if v_isSharedCheck_4383_ == 0 {
                        v___x_4376_ = v_isType_x3f_4297_;
                        v_isShared_4377_ = v_isSharedCheck_4383_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4374_);
                        crate::leanh::lean_dec(v_isType_x3f_4297_);
                        v___x_4376_ = crate::leanh::lean_box(0);
                        v_isShared_4377_ = v_isSharedCheck_4383_;
                        state = 13;
                        continue;
                    }
                }
            }
            13 => {
                v___x_4378_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_4379_ = (crate::leanh::lean_unbox(v_val_4374_) as u8);
                crate::leanh::lean_dec(v_val_4374_);
                crate::leanh::lean_ctor_set_uint8(v___x_4378_, 0 as u32, v___x_4379_);
                if v_isShared_4377_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4376_, 0, v___x_4378_);
                    v___x_4381_ = v___x_4376_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4382_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 0, v___x_4378_);
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
                if crate::leanh::lean_obj_tag(v_isInstance_x3f_4296_) == 0 {
                    v___x_4387_ = crate::leanh::lean_box(0);
                    v___y_4370_ = v_fst_4385_;
                    v_fst_4371_ = v___x_4387_;
                    v_snd_4372_ = v_snd_4386_;
                    state = 12;
                    continue;
                } else {
                    v_val_4388_ = crate::leanh::lean_ctor_get(v_isInstance_x3f_4296_, 0);
                    v_isSharedCheck_4397_ =
                        (!crate::leanh::lean_is_exclusive(v_isInstance_x3f_4296_)) as u8;
                    if v_isSharedCheck_4397_ == 0 {
                        v___x_4390_ = v_isInstance_x3f_4296_;
                        v_isShared_4391_ = v_isSharedCheck_4397_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4388_);
                        crate::leanh::lean_dec(v_isInstance_x3f_4296_);
                        v___x_4390_ = crate::leanh::lean_box(0);
                        v_isShared_4391_ = v_isSharedCheck_4397_;
                        state = 16;
                        continue;
                    }
                }
            }
            16 => {
                v___x_4392_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_4393_ = (crate::leanh::lean_unbox(v_val_4388_) as u8);
                crate::leanh::lean_dec(v_val_4388_);
                crate::leanh::lean_ctor_set_uint8(v___x_4392_, 0 as u32, v___x_4393_);
                if v_isShared_4391_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4390_, 0, v___x_4392_);
                    v___x_4395_ = v___x_4390_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4396_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___x_4392_);
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
                v_fst_4404_ = crate::leanh::lean_ctor_get(v___x_4403_, 0);
                crate::leanh::lean_inc(v_fst_4404_);
                v_snd_4405_ = crate::leanh::lean_ctor_get(v___x_4403_, 1);
                crate::leanh::lean_inc(v_snd_4405_);
                crate::leanh::lean_dec_ref(v___x_4403_);
                v___x_4406_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(v_fst_4404_);
                if v_isShared_4402_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4401_, 0, v___x_4406_);
                    v___x_4408_ = v___x_4401_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4409_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4409_, 0, v___x_4406_);
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
    mut v_00_u03b1_4413_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4414_: *mut crate::leanh::LeanObject,
    mut v_f_4415_: *mut crate::leanh::LeanObject,
    mut v_x_4416_: *mut crate::leanh::LeanObject,
    mut v___y_4417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4418_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___redArg(v_f_4415_, v_x_4416_, v___y_4417_);
    return v___x_4418_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2_spec__2(
    mut v_00_u03b1_4419_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4420_: *mut crate::leanh::LeanObject,
    mut v_f_4421_: *mut crate::leanh::LeanObject,
    mut v_sz_4422_: usize,
    mut v_i_4423_: usize,
    mut v_bs_4424_: *mut crate::leanh::LeanObject,
    mut v___y_4425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4426_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2_spec__2___redArg(v_f_4421_, v_sz_4422_, v_i_4423_, v_bs_4424_, v___y_4425_);
    return v___x_4426_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2_spec__2___boxed(
    mut v_00_u03b1_4427_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4428_: *mut crate::leanh::LeanObject,
    mut v_f_4429_: *mut crate::leanh::LeanObject,
    mut v_sz_4430_: *mut crate::leanh::LeanObject,
    mut v_i_4431_: *mut crate::leanh::LeanObject,
    mut v_bs_4432_: *mut crate::leanh::LeanObject,
    mut v___y_4433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4434_: usize = 0;
    let mut v_i_boxed_4435_: usize = 0;
    let mut v_res_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4434_ = crate::leanh::lean_unbox_usize(v_sz_4430_);
    crate::leanh::lean_dec(v_sz_4430_);
    v_i_boxed_4435_ = crate::leanh::lean_unbox_usize(v_i_4431_);
    crate::leanh::lean_dec(v_i_4431_);
    v_res_4436_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2_spec__2(v_00_u03b1_4427_, v_00_u03b2_4428_, v_f_4429_, v_sz_boxed_4434_, v_i_boxed_4435_, v_bs_4432_, v___y_4433_);
    return v_res_4436_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__1___redArg(
    mut v_x_4437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_x_4437_);
    return v_x_4437_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__1___redArg___boxed(
    mut v_x_4438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4439_ = l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__1___redArg(v_x_4438_);
    crate::leanh::lean_dec_ref(v_x_4438_);
    return v_res_4439_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__1(
    mut v_00_u03b1_4440_: *mut crate::leanh::LeanObject,
    mut v_x_4441_: *mut crate::leanh::LeanObject,
    mut v___y_4442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_x_4441_);
    return v_x_4441_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__1___boxed(
    mut v_00_u03b1_4443_: *mut crate::leanh::LeanObject,
    mut v_x_4444_: *mut crate::leanh::LeanObject,
    mut v___y_4445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4446_ = l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__1(v_00_u03b1_4443_, v_x_4444_, v___y_4445_);
    crate::leanh::lean_dec_ref(v___y_4445_);
    crate::leanh::lean_dec_ref(v_x_4444_);
    return v_res_4446_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5___redArg(
    mut v_f_4447_: *mut crate::leanh::LeanObject,
    mut v_x_4448_: *mut crate::leanh::LeanObject,
    mut v___y_4449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4453_: u8 = 0;
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4458_: u8 = 0;
    let mut v_a_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4462_: u8 = 0;
    let mut v_sz_4463_: usize = 0;
    let mut v___x_4464_: usize = 0;
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4469_: u8 = 0;
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4473_: u8 = 0;
    let mut v_a_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4477_: u8 = 0;
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4484_: u8 = 0;
    let mut v_isSharedCheck_4485_: u8 = 0;
    let mut v_a_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4490_: u8 = 0;
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4495_: u8 = 0;
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4499_: u8 = 0;
    let mut v_a_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4505_: u8 = 0;
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4512_: u8 = 0;
    let mut v_isSharedCheck_4513_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_4448_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_f_4447_);
                    v_a_4450_ = crate::leanh::lean_ctor_get(v_x_4448_, 0);
                    v_isSharedCheck_4458_ = (!crate::leanh::lean_is_exclusive(v_x_4448_)) as u8;
                    if v_isSharedCheck_4458_ == 0 {
                        v___x_4452_ = v_x_4448_;
                        v_isShared_4453_ = v_isSharedCheck_4458_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4450_);
                        crate::leanh::lean_dec(v_x_4448_);
                        v___x_4452_ = crate::leanh::lean_box(0);
                        v_isShared_4453_ = v_isSharedCheck_4458_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_4459_ = crate::leanh::lean_ctor_get(v_x_4448_, 0);
                    v_isSharedCheck_4485_ = (!crate::leanh::lean_is_exclusive(v_x_4448_)) as u8;
                    if v_isSharedCheck_4485_ == 0 {
                        v___x_4461_ = v_x_4448_;
                        v_isShared_4462_ = v_isSharedCheck_4485_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4459_);
                        crate::leanh::lean_dec(v_x_4448_);
                        v___x_4461_ = crate::leanh::lean_box(0);
                        v_isShared_4462_ = v_isSharedCheck_4485_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v_a_4486_ = crate::leanh::lean_ctor_get(v_x_4448_, 0);
                    v_a_4487_ = crate::leanh::lean_ctor_get(v_x_4448_, 1);
                    v_isSharedCheck_4513_ = (!crate::leanh::lean_is_exclusive(v_x_4448_)) as u8;
                    if v_isSharedCheck_4513_ == 0 {
                        v___x_4489_ = v_x_4448_;
                        v_isShared_4490_ = v_isSharedCheck_4513_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4487_);
                        crate::leanh::lean_inc(v_a_4486_);
                        crate::leanh::lean_dec(v_x_4448_);
                        v___x_4489_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4457_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4450_);
                    v___x_4455_ = v_reuseFailAlloc_4457_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4456_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4456_, 0, v___x_4455_);
                return v___x_4456_;
            }
            3 => {
                v_sz_4463_ = lean_array_size(v_a_4459_);
                v___x_4464_ = 0usize;
                v___x_4465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5_spec__7___redArg(v_f_4447_, v_sz_4463_, v___x_4464_, v_a_4459_, v___y_4449_);
                if crate::leanh::lean_obj_tag(v___x_4465_) == 0 {
                    crate::leanh::lean_del_object(v___x_4461_);
                    v_a_4466_ = crate::leanh::lean_ctor_get(v___x_4465_, 0);
                    v_isSharedCheck_4473_ = (!crate::leanh::lean_is_exclusive(v___x_4465_)) as u8;
                    if v_isSharedCheck_4473_ == 0 {
                        v___x_4468_ = v___x_4465_;
                        v_isShared_4469_ = v_isSharedCheck_4473_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4466_);
                        crate::leanh::lean_dec(v___x_4465_);
                        v___x_4468_ = crate::leanh::lean_box(0);
                        v_isShared_4469_ = v_isSharedCheck_4473_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_4474_ = crate::leanh::lean_ctor_get(v___x_4465_, 0);
                    v_isSharedCheck_4484_ = (!crate::leanh::lean_is_exclusive(v___x_4465_)) as u8;
                    if v_isSharedCheck_4484_ == 0 {
                        v___x_4476_ = v___x_4465_;
                        v_isShared_4477_ = v_isSharedCheck_4484_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4474_);
                        crate::leanh::lean_dec(v___x_4465_);
                        v___x_4476_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4472_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_a_4466_);
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
                    crate::leanh::lean_ctor_set(v___x_4461_, 0, v_a_4474_);
                    v___x_4479_ = v___x_4461_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4483_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_a_4474_);
                    v___x_4479_ = v_reuseFailAlloc_4483_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4477_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4476_, 0, v___x_4479_);
                    v___x_4481_ = v___x_4476_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4482_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4482_, 0, v___x_4479_);
                    v___x_4481_ = v_reuseFailAlloc_4482_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4481_;
            }
            9 => {
                crate::leanh::lean_inc_ref(v_f_4447_);
                crate::leanh::lean_inc_ref(v___y_4449_);
                v___x_4491_ = crate::leanh::lean_apply_2(v_f_4447_, v_a_4486_, v___y_4449_);
                if crate::leanh::lean_obj_tag(v___x_4491_) == 0 {
                    crate::leanh::lean_del_object(v___x_4489_);
                    crate::leanh::lean_dec_ref(v_a_4487_);
                    crate::leanh::lean_dec_ref(v_f_4447_);
                    v_a_4492_ = crate::leanh::lean_ctor_get(v___x_4491_, 0);
                    v_isSharedCheck_4499_ = (!crate::leanh::lean_is_exclusive(v___x_4491_)) as u8;
                    if v_isSharedCheck_4499_ == 0 {
                        v___x_4494_ = v___x_4491_;
                        v_isShared_4495_ = v_isSharedCheck_4499_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4492_);
                        crate::leanh::lean_dec(v___x_4491_);
                        v___x_4494_ = crate::leanh::lean_box(0);
                        v_isShared_4495_ = v_isSharedCheck_4499_;
                        state = 10;
                        continue;
                    }
                } else {
                    v_a_4500_ = crate::leanh::lean_ctor_get(v___x_4491_, 0);
                    crate::leanh::lean_inc(v_a_4500_);
                    crate::leanh::lean_dec_ref_known(v___x_4491_, 1);
                    v___x_4501_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5___redArg(v_f_4447_, v_a_4487_, v___y_4449_);
                    if crate::leanh::lean_obj_tag(v___x_4501_) == 0 {
                        crate::leanh::lean_dec(v_a_4500_);
                        crate::leanh::lean_del_object(v___x_4489_);
                        return v___x_4501_;
                    } else {
                        v_a_4502_ = crate::leanh::lean_ctor_get(v___x_4501_, 0);
                        v_isSharedCheck_4512_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4501_)) as u8;
                        if v_isSharedCheck_4512_ == 0 {
                            v___x_4504_ = v___x_4501_;
                            v_isShared_4505_ = v_isSharedCheck_4512_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4502_);
                            crate::leanh::lean_dec(v___x_4501_);
                            v___x_4504_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4498_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_a_4492_);
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
                    crate::leanh::lean_ctor_set(v___x_4489_, 1, v_a_4502_);
                    crate::leanh::lean_ctor_set(v___x_4489_, 0, v_a_4500_);
                    v___x_4507_ = v___x_4489_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4511_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_a_4500_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4511_, 1, v_a_4502_);
                    v___x_4507_ = v_reuseFailAlloc_4511_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_4505_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4504_, 0, v___x_4507_);
                    v___x_4509_ = v___x_4504_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4510_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4510_, 0, v___x_4507_);
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
    mut v_f_4514_: *mut crate::leanh::LeanObject,
    mut v_sz_4515_: usize,
    mut v_i_4516_: usize,
    mut v_bs_4517_: *mut crate::leanh::LeanObject,
    mut v___y_4518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4519_: u8 = 0;
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4526_: u8 = 0;
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4530_: u8 = 0;
    let mut v_a_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: usize = 0;
    let mut v___x_4535_: usize = 0;
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4519_ = lean_usize_dec_lt(v_i_4516_, v_sz_4515_);
                if v___x_4519_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_4514_);
                    v___x_4520_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4520_, 0, v_bs_4517_);
                    return v___x_4520_;
                } else {
                    v_v_4521_ = lean_array_uget_borrowed(v_bs_4517_, v_i_4516_);
                    crate::leanh::lean_inc(v_v_4521_);
                    crate::leanh::lean_inc_ref(v_f_4514_);
                    v___x_4522_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5___redArg(v_f_4514_, v_v_4521_, v___y_4518_);
                    if crate::leanh::lean_obj_tag(v___x_4522_) == 0 {
                        crate::leanh::lean_dec_ref(v_bs_4517_);
                        crate::leanh::lean_dec_ref(v_f_4514_);
                        v_a_4523_ = crate::leanh::lean_ctor_get(v___x_4522_, 0);
                        v_isSharedCheck_4530_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4522_)) as u8;
                        if v_isSharedCheck_4530_ == 0 {
                            v___x_4525_ = v___x_4522_;
                            v_isShared_4526_ = v_isSharedCheck_4530_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4523_);
                            crate::leanh::lean_dec(v___x_4522_);
                            v___x_4525_ = crate::leanh::lean_box(0);
                            v_isShared_4526_ = v_isSharedCheck_4530_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4531_ = crate::leanh::lean_ctor_get(v___x_4522_, 0);
                        crate::leanh::lean_inc(v_a_4531_);
                        crate::leanh::lean_dec_ref_known(v___x_4522_, 1);
                        v___x_4532_ = crate::leanh::lean_unsigned_to_nat(0);
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
                    v_reuseFailAlloc_4529_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_a_4523_);
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
    mut v_f_4538_: *mut crate::leanh::LeanObject,
    mut v_sz_4539_: *mut crate::leanh::LeanObject,
    mut v_i_4540_: *mut crate::leanh::LeanObject,
    mut v_bs_4541_: *mut crate::leanh::LeanObject,
    mut v___y_4542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4543_: usize = 0;
    let mut v_i_boxed_4544_: usize = 0;
    let mut v_res_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4543_ = crate::leanh::lean_unbox_usize(v_sz_4539_);
    crate::leanh::lean_dec(v_sz_4539_);
    v_i_boxed_4544_ = crate::leanh::lean_unbox_usize(v_i_4540_);
    crate::leanh::lean_dec(v_i_4540_);
    v_res_4545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5_spec__7___redArg(v_f_4538_, v_sz_boxed_4543_, v_i_boxed_4544_, v_bs_4541_, v___y_4542_);
    crate::leanh::lean_dec_ref(v___y_4542_);
    return v_res_4545_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5___redArg___boxed(
    mut v_f_4546_: *mut crate::leanh::LeanObject,
    mut v_x_4547_: *mut crate::leanh::LeanObject,
    mut v___y_4548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4549_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5___redArg(v_f_4546_, v_x_4547_, v___y_4548_);
    crate::leanh::lean_dec_ref(v___y_4548_);
    return v_res_4549_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3___redArg(
    mut v_sz_4550_: usize,
    mut v_i_4551_: usize,
    mut v_bs_4552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4553_: u8 = 0;
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4560_: u8 = 0;
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4564_: u8 = 0;
    let mut v_a_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: usize = 0;
    let mut v___x_4569_: usize = 0;
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4553_ = lean_usize_dec_lt(v_i_4551_, v_sz_4550_);
                if v___x_4553_ == 0 {
                    v___x_4554_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4554_, 0, v_bs_4552_);
                    return v___x_4554_;
                } else {
                    v_v_4555_ = lean_array_uget_borrowed(v_bs_4552_, v_i_4551_);
                    crate::leanh::lean_inc(v_v_4555_);
                    v___x_4556_ = l_Lean_Name_fromJson_x3f(v_v_4555_);
                    if crate::leanh::lean_obj_tag(v___x_4556_) == 0 {
                        crate::leanh::lean_dec_ref(v_bs_4552_);
                        v_a_4557_ = crate::leanh::lean_ctor_get(v___x_4556_, 0);
                        v_isSharedCheck_4564_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4556_)) as u8;
                        if v_isSharedCheck_4564_ == 0 {
                            v___x_4559_ = v___x_4556_;
                            v_isShared_4560_ = v_isSharedCheck_4564_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4557_);
                            crate::leanh::lean_dec(v___x_4556_);
                            v___x_4559_ = crate::leanh::lean_box(0);
                            v_isShared_4560_ = v_isSharedCheck_4564_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4565_ = crate::leanh::lean_ctor_get(v___x_4556_, 0);
                        crate::leanh::lean_inc(v_a_4565_);
                        crate::leanh::lean_dec_ref_known(v___x_4556_, 1);
                        v___x_4566_ = crate::leanh::lean_unsigned_to_nat(0);
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
                    v_reuseFailAlloc_4563_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4563_, 0, v_a_4557_);
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
    mut v_sz_4572_: *mut crate::leanh::LeanObject,
    mut v_i_4573_: *mut crate::leanh::LeanObject,
    mut v_bs_4574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4575_: usize = 0;
    let mut v_i_boxed_4576_: usize = 0;
    let mut v_res_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4575_ = crate::leanh::lean_unbox_usize(v_sz_4572_);
    crate::leanh::lean_dec(v_sz_4572_);
    v_i_boxed_4576_ = crate::leanh::lean_unbox_usize(v_i_4573_);
    crate::leanh::lean_dec(v_i_4573_);
    v_res_4577_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3___redArg(v_sz_boxed_4575_, v_i_boxed_4576_, v_bs_4574_);
    return v_res_4577_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0_spec__0(
    mut v_sz_4578_: usize,
    mut v_i_4579_: usize,
    mut v_bs_4580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4581_: u8 = 0;
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: usize = 0;
    let mut v___x_4587_: usize = 0;
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4581_ = lean_usize_dec_lt(v_i_4579_, v_sz_4578_);
                if v___x_4581_ == 0 {
                    v___x_4582_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4582_, 0, v_bs_4580_);
                    return v___x_4582_;
                } else {
                    v_v_4583_ = lean_array_uget(v_bs_4580_, v_i_4579_);
                    v___x_4584_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_4590_: *mut crate::leanh::LeanObject,
    mut v_i_4591_: *mut crate::leanh::LeanObject,
    mut v_bs_4592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4593_: usize = 0;
    let mut v_i_boxed_4594_: usize = 0;
    let mut v_res_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4593_ = crate::leanh::lean_unbox_usize(v_sz_4590_);
    crate::leanh::lean_dec(v_sz_4590_);
    v_i_boxed_4594_ = crate::leanh::lean_unbox_usize(v_i_4591_);
    crate::leanh::lean_dec(v_i_4591_);
    v_res_4595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0_spec__0(v_sz_boxed_4593_, v_i_boxed_4594_, v_bs_4592_);
    return v_res_4595_;
}
pub unsafe fn l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0(
    mut v_x_4598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4598_) == 4 {
        let mut v_elems_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4600_: usize = 0;
        let mut v___x_4601_: usize = 0;
        let mut v___x_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_elems_4599_ = crate::leanh::lean_ctor_get(v_x_4598_, 0);
        crate::leanh::lean_inc_ref(v_elems_4599_);
        crate::leanh::lean_dec_ref_known(v_x_4598_, 1);
        v_sz_4600_ = lean_array_size(v_elems_4599_);
        v___x_4601_ = 0usize;
        v___x_4602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0_spec__0(v_sz_4600_, v___x_4601_, v_elems_4599_);
        return v___x_4602_;
    } else {
        let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4603_ = l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0___closed__0;
        v___x_4604_ = crate::leanh::lean_unsigned_to_nat(80);
        v___x_4605_ = l_Lean_Json_pretty(v_x_4598_, v___x_4604_);
        v___x_4606_ = lean_string_append(v___x_4603_, v___x_4605_);
        crate::leanh::lean_dec_ref(v___x_4605_);
        v___x_4607_ = l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0___closed__1;
        v___x_4608_ = lean_string_append(v___x_4606_, v___x_4607_);
        v___x_4609_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4609_, 0, v___x_4608_);
        return v___x_4609_;
    }
}
pub unsafe fn l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(
    mut v_json_4616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4622_: u8 = 0;
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: u8 = 0;
    let mut v___x_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: u8 = 0;
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: u8 = 0;
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4637_: u8 = 0;
    let mut v___x_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4641_: u8 = 0;
    let mut v_a_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4649_: u8 = 0;
    let mut v___x_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4656_: u8 = 0;
    let mut v___x_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4663_: u8 = 0;
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4667_: u8 = 0;
    let mut v_a_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4675_: u8 = 0;
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4679_: u8 = 0;
    let mut v_a_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4683_: u8 = 0;
    let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4690_: u8 = 0;
    let mut v___x_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4697_: u8 = 0;
    let mut v___x_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4701_: u8 = 0;
    let mut v_a_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4709_: u8 = 0;
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4713_: u8 = 0;
    let mut v_a_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4717_: u8 = 0;
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4724_: u8 = 0;
    let mut v_isSharedCheck_4725_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_json_4616_);
                v___x_4617_ = l_Lean_Json_getTag_x3f(v_json_4616_);
                if crate::leanh::lean_obj_tag(v___x_4617_) == 0 {
                    crate::leanh::lean_dec(v_json_4616_);
                    v___x_4618_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__1;
                    return v___x_4618_;
                } else {
                    v_val_4619_ = crate::leanh::lean_ctor_get(v___x_4617_, 0);
                    v_isSharedCheck_4725_ = (!crate::leanh::lean_is_exclusive(v___x_4617_)) as u8;
                    if v_isSharedCheck_4725_ == 0 {
                        v___x_4621_ = v___x_4617_;
                        v_isShared_4622_ = v_isSharedCheck_4725_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4619_);
                        crate::leanh::lean_dec(v___x_4617_);
                        v___x_4621_ = crate::leanh::lean_box(0);
                        v_isShared_4622_ = v_isSharedCheck_4725_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4623_ = crate::leanh::lean_box(0);
                v___x_4624_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__1;
                v___x_4625_ = lean_string_dec_eq(v_val_4619_, v___x_4624_);
                if v___x_4625_ == 0 {
                    v___x_4626_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__0;
                    v___x_4627_ = lean_string_dec_eq(v_val_4619_, v___x_4626_);
                    if v___x_4627_ == 0 {
                        crate::leanh::lean_del_object(v___x_4621_);
                        v___x_4628_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__2;
                        v___x_4629_ = lean_string_dec_eq(v_val_4619_, v___x_4628_);
                        crate::leanh::lean_dec(v_val_4619_);
                        if v___x_4629_ == 0 {
                            crate::leanh::lean_dec(v_json_4616_);
                            v___x_4630_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4___closed__3;
                            return v___x_4630_;
                        } else {
                            v___x_4631_ = crate::leanh::lean_unsigned_to_nat(2);
                            v___x_4632_ = crate::leanh::lean_box(0);
                            v___x_4633_ = l_Lean_Json_parseCtorFields(
                                v_json_4616_,
                                v___x_4628_,
                                v___x_4631_,
                                v___x_4632_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4633_) == 0 {
                                v_a_4634_ = crate::leanh::lean_ctor_get(v___x_4633_, 0);
                                v_isSharedCheck_4641_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4633_)) as u8;
                                if v_isSharedCheck_4641_ == 0 {
                                    v___x_4636_ = v___x_4633_;
                                    v_isShared_4637_ = v_isSharedCheck_4641_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4634_);
                                    crate::leanh::lean_dec(v___x_4633_);
                                    v___x_4636_ = crate::leanh::lean_box(0);
                                    v_isShared_4637_ = v_isSharedCheck_4641_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_a_4642_ = crate::leanh::lean_ctor_get(v___x_4633_, 0);
                                crate::leanh::lean_inc(v_a_4642_);
                                crate::leanh::lean_dec_ref_known(v___x_4633_, 1);
                                v___x_4643_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_4644_ =
                                    lean_array_get_borrowed(v___x_4623_, v_a_4642_, v___x_4643_);
                                crate::leanh::lean_inc(v___x_4644_);
                                v___x_4645_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(v___x_4644_);
                                if crate::leanh::lean_obj_tag(v___x_4645_) == 0 {
                                    crate::leanh::lean_dec(v_a_4642_);
                                    return v___x_4645_;
                                } else {
                                    v_a_4646_ = crate::leanh::lean_ctor_get(v___x_4645_, 0);
                                    v_isSharedCheck_4656_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4645_)) as u8;
                                    if v_isSharedCheck_4656_ == 0 {
                                        v___x_4648_ = v___x_4645_;
                                        v_isShared_4649_ = v_isSharedCheck_4656_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4646_);
                                        crate::leanh::lean_dec(v___x_4645_);
                                        v___x_4648_ = crate::leanh::lean_box(0);
                                        v_isShared_4649_ = v_isSharedCheck_4656_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_4619_);
                        v___x_4657_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4658_ = crate::leanh::lean_box(0);
                        v___x_4659_ = l_Lean_Json_parseCtorFields(
                            v_json_4616_,
                            v___x_4626_,
                            v___x_4657_,
                            v___x_4658_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4659_) == 0 {
                            crate::leanh::lean_del_object(v___x_4621_);
                            v_a_4660_ = crate::leanh::lean_ctor_get(v___x_4659_, 0);
                            v_isSharedCheck_4667_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4659_)) as u8;
                            if v_isSharedCheck_4667_ == 0 {
                                v___x_4662_ = v___x_4659_;
                                v_isShared_4663_ = v_isSharedCheck_4667_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4660_);
                                crate::leanh::lean_dec(v___x_4659_);
                                v___x_4662_ = crate::leanh::lean_box(0);
                                v_isShared_4663_ = v_isSharedCheck_4667_;
                                state = 6;
                                continue;
                            }
                        } else {
                            v_a_4668_ = crate::leanh::lean_ctor_get(v___x_4659_, 0);
                            crate::leanh::lean_inc(v_a_4668_);
                            crate::leanh::lean_dec_ref_known(v___x_4659_, 1);
                            v___x_4669_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_4670_ = lean_array_get(v___x_4623_, v_a_4668_, v___x_4669_);
                            crate::leanh::lean_dec(v_a_4668_);
                            v___x_4671_ = l_Lean_Json_getStr_x3f(v___x_4670_);
                            if crate::leanh::lean_obj_tag(v___x_4671_) == 0 {
                                crate::leanh::lean_del_object(v___x_4621_);
                                v_a_4672_ = crate::leanh::lean_ctor_get(v___x_4671_, 0);
                                v_isSharedCheck_4679_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4671_)) as u8;
                                if v_isSharedCheck_4679_ == 0 {
                                    v___x_4674_ = v___x_4671_;
                                    v_isShared_4675_ = v_isSharedCheck_4679_;
                                    state = 8;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4672_);
                                    crate::leanh::lean_dec(v___x_4671_);
                                    v___x_4674_ = crate::leanh::lean_box(0);
                                    v_isShared_4675_ = v_isSharedCheck_4679_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                v_a_4680_ = crate::leanh::lean_ctor_get(v___x_4671_, 0);
                                v_isSharedCheck_4690_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4671_)) as u8;
                                if v_isSharedCheck_4690_ == 0 {
                                    v___x_4682_ = v___x_4671_;
                                    v_isShared_4683_ = v_isSharedCheck_4690_;
                                    state = 10;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4680_);
                                    crate::leanh::lean_dec(v___x_4671_);
                                    v___x_4682_ = crate::leanh::lean_box(0);
                                    v_isShared_4683_ = v_isSharedCheck_4690_;
                                    state = 10;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_val_4619_);
                    v___x_4691_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4692_ = crate::leanh::lean_box(0);
                    v___x_4693_ = l_Lean_Json_parseCtorFields(
                        v_json_4616_,
                        v___x_4624_,
                        v___x_4691_,
                        v___x_4692_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4693_) == 0 {
                        crate::leanh::lean_del_object(v___x_4621_);
                        v_a_4694_ = crate::leanh::lean_ctor_get(v___x_4693_, 0);
                        v_isSharedCheck_4701_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4693_)) as u8;
                        if v_isSharedCheck_4701_ == 0 {
                            v___x_4696_ = v___x_4693_;
                            v_isShared_4697_ = v_isSharedCheck_4701_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4694_);
                            crate::leanh::lean_dec(v___x_4693_);
                            v___x_4696_ = crate::leanh::lean_box(0);
                            v_isShared_4697_ = v_isSharedCheck_4701_;
                            state = 13;
                            continue;
                        }
                    } else {
                        v_a_4702_ = crate::leanh::lean_ctor_get(v___x_4693_, 0);
                        crate::leanh::lean_inc(v_a_4702_);
                        crate::leanh::lean_dec_ref_known(v___x_4693_, 1);
                        v___x_4703_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_4704_ = lean_array_get(v___x_4623_, v_a_4702_, v___x_4703_);
                        crate::leanh::lean_dec(v_a_4702_);
                        v___x_4705_ = l_Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4_spec__5(v___x_4704_);
                        if crate::leanh::lean_obj_tag(v___x_4705_) == 0 {
                            crate::leanh::lean_del_object(v___x_4621_);
                            v_a_4706_ = crate::leanh::lean_ctor_get(v___x_4705_, 0);
                            v_isSharedCheck_4713_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4705_)) as u8;
                            if v_isSharedCheck_4713_ == 0 {
                                v___x_4708_ = v___x_4705_;
                                v_isShared_4709_ = v_isSharedCheck_4713_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4706_);
                                crate::leanh::lean_dec(v___x_4705_);
                                v___x_4708_ = crate::leanh::lean_box(0);
                                v_isShared_4709_ = v_isSharedCheck_4713_;
                                state = 15;
                                continue;
                            }
                        } else {
                            v_a_4714_ = crate::leanh::lean_ctor_get(v___x_4705_, 0);
                            v_isSharedCheck_4724_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4705_)) as u8;
                            if v_isSharedCheck_4724_ == 0 {
                                v___x_4716_ = v___x_4705_;
                                v_isShared_4717_ = v_isSharedCheck_4724_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4714_);
                                crate::leanh::lean_dec(v___x_4705_);
                                v___x_4716_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4640_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4640_, 0, v_a_4634_);
                    v___x_4639_ = v_reuseFailAlloc_4640_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4639_;
            }
            4 => {
                v___x_4650_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4651_ = lean_array_get(v___x_4623_, v_a_4642_, v___x_4650_);
                crate::leanh::lean_dec(v_a_4642_);
                v___x_4652_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4652_, 0, v___x_4651_);
                crate::leanh::lean_ctor_set(v___x_4652_, 1, v_a_4646_);
                if v_isShared_4649_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4648_, 0, v___x_4652_);
                    v___x_4654_ = v___x_4648_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4655_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4655_, 0, v___x_4652_);
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
                    v_reuseFailAlloc_4666_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4666_, 0, v_a_4660_);
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
                    v_reuseFailAlloc_4678_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_a_4672_);
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
                    crate::leanh::lean_ctor_set_tag(v___x_4621_, 0);
                    crate::leanh::lean_ctor_set(v___x_4621_, 0, v_a_4680_);
                    v___x_4685_ = v___x_4621_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4689_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4689_, 0, v_a_4680_);
                    v___x_4685_ = v_reuseFailAlloc_4689_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4683_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4682_, 0, v___x_4685_);
                    v___x_4687_ = v___x_4682_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4688_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4688_, 0, v___x_4685_);
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
                    v_reuseFailAlloc_4700_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4700_, 0, v_a_4694_);
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
                    v_reuseFailAlloc_4712_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4712_, 0, v_a_4706_);
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
                    crate::leanh::lean_ctor_set(v___x_4621_, 0, v_a_4714_);
                    v___x_4719_ = v___x_4621_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4723_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4723_, 0, v_a_4714_);
                    v___x_4719_ = v_reuseFailAlloc_4723_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_4717_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4716_, 0, v___x_4719_);
                    v___x_4721_ = v___x_4716_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4722_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4722_, 0, v___x_4719_);
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
    mut v_bs_4728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4729_: u8 = 0;
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4736_: u8 = 0;
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4740_: u8 = 0;
    let mut v_a_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: usize = 0;
    let mut v___x_4745_: usize = 0;
    let mut v___x_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4729_ = lean_usize_dec_lt(v_i_4727_, v_sz_4726_);
                if v___x_4729_ == 0 {
                    v___x_4730_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4730_, 0, v_bs_4728_);
                    return v___x_4730_;
                } else {
                    v_v_4731_ = lean_array_uget_borrowed(v_bs_4728_, v_i_4727_);
                    crate::leanh::lean_inc(v_v_4731_);
                    v___x_4732_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(v_v_4731_);
                    if crate::leanh::lean_obj_tag(v___x_4732_) == 0 {
                        crate::leanh::lean_dec_ref(v_bs_4728_);
                        v_a_4733_ = crate::leanh::lean_ctor_get(v___x_4732_, 0);
                        v_isSharedCheck_4740_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4732_)) as u8;
                        if v_isSharedCheck_4740_ == 0 {
                            v___x_4735_ = v___x_4732_;
                            v_isShared_4736_ = v_isSharedCheck_4740_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4733_);
                            crate::leanh::lean_dec(v___x_4732_);
                            v___x_4735_ = crate::leanh::lean_box(0);
                            v_isShared_4736_ = v_isSharedCheck_4740_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4741_ = crate::leanh::lean_ctor_get(v___x_4732_, 0);
                        crate::leanh::lean_inc(v_a_4741_);
                        crate::leanh::lean_dec_ref_known(v___x_4732_, 1);
                        v___x_4742_ = crate::leanh::lean_unsigned_to_nat(0);
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
                    v_reuseFailAlloc_4739_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4739_, 0, v_a_4733_);
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
    mut v_x_4748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4748_) == 4 {
        let mut v_elems_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_sz_4750_: usize = 0;
        let mut v___x_4751_: usize = 0;
        let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_elems_4749_ = crate::leanh::lean_ctor_get(v_x_4748_, 0);
        crate::leanh::lean_inc_ref(v_elems_4749_);
        crate::leanh::lean_dec_ref_known(v_x_4748_, 1);
        v_sz_4750_ = lean_array_size(v_elems_4749_);
        v___x_4751_ = 0usize;
        v___x_4752_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4_spec__5_spec__6(v_sz_4750_, v___x_4751_, v_elems_4749_);
        return v___x_4752_;
    } else {
        let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4753_ = l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0___closed__0;
        v___x_4754_ = crate::leanh::lean_unsigned_to_nat(80);
        v___x_4755_ = l_Lean_Json_pretty(v_x_4748_, v___x_4754_);
        v___x_4756_ = lean_string_append(v___x_4753_, v___x_4755_);
        crate::leanh::lean_dec_ref(v___x_4755_);
        v___x_4757_ = l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0___closed__1;
        v___x_4758_ = lean_string_append(v___x_4756_, v___x_4757_);
        v___x_4759_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4759_, 0, v___x_4758_);
        return v___x_4759_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4_spec__5_spec__6___boxed(
    mut v_sz_4760_: *mut crate::leanh::LeanObject,
    mut v_i_4761_: *mut crate::leanh::LeanObject,
    mut v_bs_4762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4763_: usize = 0;
    let mut v_i_boxed_4764_: usize = 0;
    let mut v_res_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4763_ = crate::leanh::lean_unbox_usize(v_sz_4760_);
    crate::leanh::lean_dec(v_sz_4760_);
    v_i_boxed_4764_ = crate::leanh::lean_unbox_usize(v_i_4761_);
    crate::leanh::lean_dec(v_i_4761_);
    v_res_4765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_fromJson_x3f___at___00Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4_spec__5_spec__6(v_sz_boxed_4763_, v_i_boxed_4764_, v_bs_4762_);
    return v_res_4765_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___redArg(
    mut v_sz_4766_: usize,
    mut v_i_4767_: usize,
    mut v_bs_4768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4769_: u8 = 0;
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4776_: u8 = 0;
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4780_: u8 = 0;
    let mut v_a_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: usize = 0;
    let mut v___x_4785_: usize = 0;
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4769_ = lean_usize_dec_lt(v_i_4767_, v_sz_4766_);
                if v___x_4769_ == 0 {
                    v___x_4770_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4770_, 0, v_bs_4768_);
                    return v___x_4770_;
                } else {
                    v_v_4771_ = lean_array_uget_borrowed(v_bs_4768_, v_i_4767_);
                    crate::leanh::lean_inc(v_v_4771_);
                    v___x_4772_ = l_Lean_Json_getStr_x3f(v_v_4771_);
                    if crate::leanh::lean_obj_tag(v___x_4772_) == 0 {
                        crate::leanh::lean_dec_ref(v_bs_4768_);
                        v_a_4773_ = crate::leanh::lean_ctor_get(v___x_4772_, 0);
                        v_isSharedCheck_4780_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4772_)) as u8;
                        if v_isSharedCheck_4780_ == 0 {
                            v___x_4775_ = v___x_4772_;
                            v_isShared_4776_ = v_isSharedCheck_4780_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4773_);
                            crate::leanh::lean_dec(v___x_4772_);
                            v___x_4775_ = crate::leanh::lean_box(0);
                            v_isShared_4776_ = v_isSharedCheck_4780_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4781_ = crate::leanh::lean_ctor_get(v___x_4772_, 0);
                        crate::leanh::lean_inc(v_a_4781_);
                        crate::leanh::lean_dec_ref_known(v___x_4772_, 1);
                        v___x_4782_ = crate::leanh::lean_unsigned_to_nat(0);
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
                    v_reuseFailAlloc_4779_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4779_, 0, v_a_4773_);
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
    mut v_sz_4788_: *mut crate::leanh::LeanObject,
    mut v_i_4789_: *mut crate::leanh::LeanObject,
    mut v_bs_4790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4791_: usize = 0;
    let mut v_i_boxed_4792_: usize = 0;
    let mut v_res_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4791_ = crate::leanh::lean_unbox_usize(v_sz_4788_);
    crate::leanh::lean_dec(v_sz_4788_);
    v_i_boxed_4792_ = crate::leanh::lean_unbox_usize(v_i_4789_);
    crate::leanh::lean_dec(v_i_4789_);
    v_res_4793_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___redArg(v_sz_boxed_4791_, v_i_boxed_4792_, v_bs_4790_);
    return v_res_4793_;
}
pub unsafe fn l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_(
    mut v_j_4795_: *mut crate::leanh::LeanObject,
    mut v_a_4796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4801_: u8 = 0;
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4805_: u8 = 0;
    let mut v_a_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_names_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarIds_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_x3f_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInstance_x3f_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isType_x3f_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInserted_x3f_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRemoved_x3f_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4817_: u8 = 0;
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4822_: u8 = 0;
    let mut v___x_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4826_: u8 = 0;
    let mut v_a_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4828_: usize = 0;
    let mut v___x_4829_: usize = 0;
    let mut v___x_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4834_: u8 = 0;
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4838_: u8 = 0;
    let mut v_a_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4844_: u8 = 0;
    let mut v___x_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4848_: u8 = 0;
    let mut v_a_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4850_: usize = 0;
    let mut v___x_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4855_: u8 = 0;
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4859_: u8 = 0;
    let mut v_a_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4865_: u8 = 0;
    let mut v___x_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4869_: u8 = 0;
    let mut v_a_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4876_: u8 = 0;
    let mut v___x_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4880_: u8 = 0;
    let mut v_a_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4884_: u8 = 0;
    let mut v___y_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_____do__lift_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_____do__lift_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4906_: u8 = 0;
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4911_: u8 = 0;
    let mut v___x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4915_: u8 = 0;
    let mut v_a_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4920_: u8 = 0;
    let mut v___y_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_____do__lift_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4929_: u8 = 0;
    let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4934_: u8 = 0;
    let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4938_: u8 = 0;
    let mut v_a_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4943_: u8 = 0;
    let mut v___y_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_____do__lift_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4951_: u8 = 0;
    let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4956_: u8 = 0;
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4960_: u8 = 0;
    let mut v_a_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4965_: u8 = 0;
    let mut v_____do__lift_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4972_: u8 = 0;
    let mut v___x_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4977_: u8 = 0;
    let mut v___x_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4981_: u8 = 0;
    let mut v_a_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4986_: u8 = 0;
    let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4991_: u8 = 0;
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4996_: u8 = 0;
    let mut v___x_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5000_: u8 = 0;
    let mut v_a_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5006_: u8 = 0;
    let mut v___x_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5010_: u8 = 0;
    let mut v_a_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5015_: u8 = 0;
    let mut v_isSharedCheck_5016_: u8 = 0;
    let mut v_isSharedCheck_5017_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4797_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_(v_j_4795_);
                if crate::leanh::lean_obj_tag(v___x_4797_) == 0 {
                    v_a_4798_ = crate::leanh::lean_ctor_get(v___x_4797_, 0);
                    v_isSharedCheck_4805_ = (!crate::leanh::lean_is_exclusive(v___x_4797_)) as u8;
                    if v_isSharedCheck_4805_ == 0 {
                        v___x_4800_ = v___x_4797_;
                        v_isShared_4801_ = v_isSharedCheck_4805_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4798_);
                        crate::leanh::lean_dec(v___x_4797_);
                        v___x_4800_ = crate::leanh::lean_box(0);
                        v_isShared_4801_ = v_isSharedCheck_4805_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4806_ = crate::leanh::lean_ctor_get(v___x_4797_, 0);
                    crate::leanh::lean_inc(v_a_4806_);
                    crate::leanh::lean_dec_ref_known(v___x_4797_, 1);
                    v_names_4807_ = crate::leanh::lean_ctor_get(v_a_4806_, 0);
                    v_fvarIds_4808_ = crate::leanh::lean_ctor_get(v_a_4806_, 1);
                    v_type_4809_ = crate::leanh::lean_ctor_get(v_a_4806_, 2);
                    v_val_x3f_4810_ = crate::leanh::lean_ctor_get(v_a_4806_, 3);
                    v_isInstance_x3f_4811_ = crate::leanh::lean_ctor_get(v_a_4806_, 4);
                    v_isType_x3f_4812_ = crate::leanh::lean_ctor_get(v_a_4806_, 5);
                    v_isInserted_x3f_4813_ = crate::leanh::lean_ctor_get(v_a_4806_, 6);
                    v_isRemoved_x3f_4814_ = crate::leanh::lean_ctor_get(v_a_4806_, 7);
                    v_isSharedCheck_5017_ = (!crate::leanh::lean_is_exclusive(v_a_4806_)) as u8;
                    if v_isSharedCheck_5017_ == 0 {
                        v___x_4816_ = v_a_4806_;
                        v_isShared_4817_ = v_isSharedCheck_5017_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_isRemoved_x3f_4814_);
                        crate::leanh::lean_inc(v_isInserted_x3f_4813_);
                        crate::leanh::lean_inc(v_isType_x3f_4812_);
                        crate::leanh::lean_inc(v_isInstance_x3f_4811_);
                        crate::leanh::lean_inc(v_val_x3f_4810_);
                        crate::leanh::lean_inc(v_type_4809_);
                        crate::leanh::lean_inc(v_fvarIds_4808_);
                        crate::leanh::lean_inc(v_names_4807_);
                        crate::leanh::lean_dec(v_a_4806_);
                        v___x_4816_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4804_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_a_4798_);
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
                if crate::leanh::lean_obj_tag(v___x_4818_) == 0 {
                    crate::leanh::lean_del_object(v___x_4816_);
                    crate::leanh::lean_dec(v_isRemoved_x3f_4814_);
                    crate::leanh::lean_dec(v_isInserted_x3f_4813_);
                    crate::leanh::lean_dec(v_isType_x3f_4812_);
                    crate::leanh::lean_dec(v_isInstance_x3f_4811_);
                    crate::leanh::lean_dec(v_val_x3f_4810_);
                    crate::leanh::lean_dec(v_type_4809_);
                    crate::leanh::lean_dec(v_fvarIds_4808_);
                    v_a_4819_ = crate::leanh::lean_ctor_get(v___x_4818_, 0);
                    v_isSharedCheck_4826_ = (!crate::leanh::lean_is_exclusive(v___x_4818_)) as u8;
                    if v_isSharedCheck_4826_ == 0 {
                        v___x_4821_ = v___x_4818_;
                        v_isShared_4822_ = v_isSharedCheck_4826_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4819_);
                        crate::leanh::lean_dec(v___x_4818_);
                        v___x_4821_ = crate::leanh::lean_box(0);
                        v_isShared_4822_ = v_isSharedCheck_4826_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_4827_ = crate::leanh::lean_ctor_get(v___x_4818_, 0);
                    crate::leanh::lean_inc(v_a_4827_);
                    crate::leanh::lean_dec_ref_known(v___x_4818_, 1);
                    v_sz_4828_ = lean_array_size(v_a_4827_);
                    v___x_4829_ = 0usize;
                    v___x_4830_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___redArg(v_sz_4828_, v___x_4829_, v_a_4827_);
                    if crate::leanh::lean_obj_tag(v___x_4830_) == 0 {
                        crate::leanh::lean_del_object(v___x_4816_);
                        crate::leanh::lean_dec(v_isRemoved_x3f_4814_);
                        crate::leanh::lean_dec(v_isInserted_x3f_4813_);
                        crate::leanh::lean_dec(v_isType_x3f_4812_);
                        crate::leanh::lean_dec(v_isInstance_x3f_4811_);
                        crate::leanh::lean_dec(v_val_x3f_4810_);
                        crate::leanh::lean_dec(v_type_4809_);
                        crate::leanh::lean_dec(v_fvarIds_4808_);
                        v_a_4831_ = crate::leanh::lean_ctor_get(v___x_4830_, 0);
                        v_isSharedCheck_4838_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4830_)) as u8;
                        if v_isSharedCheck_4838_ == 0 {
                            v___x_4833_ = v___x_4830_;
                            v_isShared_4834_ = v_isSharedCheck_4838_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4831_);
                            crate::leanh::lean_dec(v___x_4830_);
                            v___x_4833_ = crate::leanh::lean_box(0);
                            v_isShared_4834_ = v_isSharedCheck_4838_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_4839_ = crate::leanh::lean_ctor_get(v___x_4830_, 0);
                        crate::leanh::lean_inc(v_a_4839_);
                        crate::leanh::lean_dec_ref_known(v___x_4830_, 1);
                        v___x_4840_ = l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0(v_fvarIds_4808_);
                        if crate::leanh::lean_obj_tag(v___x_4840_) == 0 {
                            crate::leanh::lean_dec(v_a_4839_);
                            crate::leanh::lean_del_object(v___x_4816_);
                            crate::leanh::lean_dec(v_isRemoved_x3f_4814_);
                            crate::leanh::lean_dec(v_isInserted_x3f_4813_);
                            crate::leanh::lean_dec(v_isType_x3f_4812_);
                            crate::leanh::lean_dec(v_isInstance_x3f_4811_);
                            crate::leanh::lean_dec(v_val_x3f_4810_);
                            crate::leanh::lean_dec(v_type_4809_);
                            v_a_4841_ = crate::leanh::lean_ctor_get(v___x_4840_, 0);
                            v_isSharedCheck_4848_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4840_)) as u8;
                            if v_isSharedCheck_4848_ == 0 {
                                v___x_4843_ = v___x_4840_;
                                v_isShared_4844_ = v_isSharedCheck_4848_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4841_);
                                crate::leanh::lean_dec(v___x_4840_);
                                v___x_4843_ = crate::leanh::lean_box(0);
                                v_isShared_4844_ = v_isSharedCheck_4848_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v_a_4849_ = crate::leanh::lean_ctor_get(v___x_4840_, 0);
                            crate::leanh::lean_inc(v_a_4849_);
                            crate::leanh::lean_dec_ref_known(v___x_4840_, 1);
                            v_sz_4850_ = lean_array_size(v_a_4849_);
                            v___x_4851_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3___redArg(v_sz_4850_, v___x_4829_, v_a_4849_);
                            if crate::leanh::lean_obj_tag(v___x_4851_) == 0 {
                                crate::leanh::lean_dec(v_a_4839_);
                                crate::leanh::lean_del_object(v___x_4816_);
                                crate::leanh::lean_dec(v_isRemoved_x3f_4814_);
                                crate::leanh::lean_dec(v_isInserted_x3f_4813_);
                                crate::leanh::lean_dec(v_isType_x3f_4812_);
                                crate::leanh::lean_dec(v_isInstance_x3f_4811_);
                                crate::leanh::lean_dec(v_val_x3f_4810_);
                                crate::leanh::lean_dec(v_type_4809_);
                                v_a_4852_ = crate::leanh::lean_ctor_get(v___x_4851_, 0);
                                v_isSharedCheck_4859_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4851_)) as u8;
                                if v_isSharedCheck_4859_ == 0 {
                                    v___x_4854_ = v___x_4851_;
                                    v_isShared_4855_ = v_isSharedCheck_4859_;
                                    state = 10;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4852_);
                                    crate::leanh::lean_dec(v___x_4851_);
                                    v___x_4854_ = crate::leanh::lean_box(0);
                                    v_isShared_4855_ = v_isSharedCheck_4859_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                v_a_4860_ = crate::leanh::lean_ctor_get(v___x_4851_, 0);
                                crate::leanh::lean_inc(v_a_4860_);
                                crate::leanh::lean_dec_ref_known(v___x_4851_, 1);
                                v___x_4861_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(v_type_4809_);
                                if crate::leanh::lean_obj_tag(v___x_4861_) == 0 {
                                    crate::leanh::lean_dec(v_a_4860_);
                                    crate::leanh::lean_dec(v_a_4839_);
                                    crate::leanh::lean_del_object(v___x_4816_);
                                    crate::leanh::lean_dec(v_isRemoved_x3f_4814_);
                                    crate::leanh::lean_dec(v_isInserted_x3f_4813_);
                                    crate::leanh::lean_dec(v_isType_x3f_4812_);
                                    crate::leanh::lean_dec(v_isInstance_x3f_4811_);
                                    crate::leanh::lean_dec(v_val_x3f_4810_);
                                    v_a_4862_ = crate::leanh::lean_ctor_get(v___x_4861_, 0);
                                    v_isSharedCheck_4869_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4861_)) as u8;
                                    if v_isSharedCheck_4869_ == 0 {
                                        v___x_4864_ = v___x_4861_;
                                        v_isShared_4865_ = v_isSharedCheck_4869_;
                                        state = 12;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4862_);
                                        crate::leanh::lean_dec(v___x_4861_);
                                        v___x_4864_ = crate::leanh::lean_box(0);
                                        v_isShared_4865_ = v_isSharedCheck_4869_;
                                        state = 12;
                                        continue;
                                    }
                                } else {
                                    v_a_4870_ = crate::leanh::lean_ctor_get(v___x_4861_, 0);
                                    crate::leanh::lean_inc(v_a_4870_);
                                    crate::leanh::lean_dec_ref_known(v___x_4861_, 1);
                                    v___x_4871_ = l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec___closed__0_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_;
                                    v___x_4872_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5___redArg(v___x_4871_, v_a_4870_, v_a_4796_);
                                    if crate::leanh::lean_obj_tag(v___x_4872_) == 0 {
                                        crate::leanh::lean_dec(v_a_4860_);
                                        crate::leanh::lean_dec(v_a_4839_);
                                        crate::leanh::lean_del_object(v___x_4816_);
                                        crate::leanh::lean_dec(v_isRemoved_x3f_4814_);
                                        crate::leanh::lean_dec(v_isInserted_x3f_4813_);
                                        crate::leanh::lean_dec(v_isType_x3f_4812_);
                                        crate::leanh::lean_dec(v_isInstance_x3f_4811_);
                                        crate::leanh::lean_dec(v_val_x3f_4810_);
                                        v_a_4873_ = crate::leanh::lean_ctor_get(v___x_4872_, 0);
                                        v_isSharedCheck_4880_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4872_)) as u8;
                                        if v_isSharedCheck_4880_ == 0 {
                                            v___x_4875_ = v___x_4872_;
                                            v_isShared_4876_ = v_isSharedCheck_4880_;
                                            state = 14;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4873_);
                                            crate::leanh::lean_dec(v___x_4872_);
                                            v___x_4875_ = crate::leanh::lean_box(0);
                                            v_isShared_4876_ = v_isSharedCheck_4880_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_a_4881_ = crate::leanh::lean_ctor_get(v___x_4872_, 0);
                                        v_isSharedCheck_5016_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4872_)) as u8;
                                        if v_isSharedCheck_5016_ == 0 {
                                            v___x_4883_ = v___x_4872_;
                                            v_isShared_4884_ = v_isSharedCheck_5016_;
                                            state = 16;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4881_);
                                            crate::leanh::lean_dec(v___x_4872_);
                                            v___x_4883_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4825_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4825_, 0, v_a_4819_);
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
                    v_reuseFailAlloc_4837_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4837_, 0, v_a_4831_);
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
                    v_reuseFailAlloc_4847_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4847_, 0, v_a_4841_);
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
                    v_reuseFailAlloc_4858_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_a_4852_);
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
                    v_reuseFailAlloc_4868_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4868_, 0, v_a_4862_);
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
                    v_reuseFailAlloc_4879_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4879_, 0, v_a_4873_);
                    v___x_4878_ = v_reuseFailAlloc_4879_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4878_;
            }
            16 => {
                if crate::leanh::lean_obj_tag(v_val_x3f_4810_) == 0 {
                    v___x_4987_ = crate::leanh::lean_box(0);
                    v_____do__lift_4967_ = v___x_4987_;
                    state = 35;
                    continue;
                } else {
                    v_val_4988_ = crate::leanh::lean_ctor_get(v_val_x3f_4810_, 0);
                    v_isSharedCheck_5015_ =
                        (!crate::leanh::lean_is_exclusive(v_val_x3f_4810_)) as u8;
                    if v_isSharedCheck_5015_ == 0 {
                        v___x_4990_ = v_val_x3f_4810_;
                        v_isShared_4991_ = v_isSharedCheck_5015_;
                        state = 40;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4988_);
                        crate::leanh::lean_dec(v_val_x3f_4810_);
                        v___x_4990_ = crate::leanh::lean_box(0);
                        v_isShared_4991_ = v_isSharedCheck_5015_;
                        state = 40;
                        continue;
                    }
                }
            }
            17 => {
                if v_isShared_4817_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4816_, 7, v_____do__lift_4890_);
                    crate::leanh::lean_ctor_set(v___x_4816_, 6, v___y_4887_);
                    crate::leanh::lean_ctor_set(v___x_4816_, 5, v___y_4889_);
                    crate::leanh::lean_ctor_set(v___x_4816_, 4, v___y_4886_);
                    crate::leanh::lean_ctor_set(v___x_4816_, 3, v___y_4888_);
                    crate::leanh::lean_ctor_set(v___x_4816_, 2, v_a_4881_);
                    crate::leanh::lean_ctor_set(v___x_4816_, 1, v_a_4860_);
                    crate::leanh::lean_ctor_set(v___x_4816_, 0, v_a_4839_);
                    v___x_4892_ = v___x_4816_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4896_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4896_, 0, v_a_4839_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4896_, 1, v_a_4860_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4896_, 2, v_a_4881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4896_, 3, v___y_4888_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4896_, 4, v___y_4886_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4896_, 5, v___y_4889_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4896_, 6, v___y_4887_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4896_, 7, v_____do__lift_4890_);
                    v___x_4892_ = v_reuseFailAlloc_4896_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_4884_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4883_, 0, v___x_4892_);
                    v___x_4894_ = v___x_4883_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4895_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4895_, 0, v___x_4892_);
                    v___x_4894_ = v_reuseFailAlloc_4895_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4894_;
            }
            20 => {
                if crate::leanh::lean_obj_tag(v_isRemoved_x3f_4814_) == 0 {
                    v___x_4902_ = crate::leanh::lean_box(0);
                    v___y_4886_ = v___y_4898_;
                    v___y_4887_ = v_____do__lift_4901_;
                    v___y_4888_ = v___y_4899_;
                    v___y_4889_ = v___y_4900_;
                    v_____do__lift_4890_ = v___x_4902_;
                    state = 17;
                    continue;
                } else {
                    v_val_4903_ = crate::leanh::lean_ctor_get(v_isRemoved_x3f_4814_, 0);
                    v_isSharedCheck_4920_ =
                        (!crate::leanh::lean_is_exclusive(v_isRemoved_x3f_4814_)) as u8;
                    if v_isSharedCheck_4920_ == 0 {
                        v___x_4905_ = v_isRemoved_x3f_4814_;
                        v_isShared_4906_ = v_isSharedCheck_4920_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4903_);
                        crate::leanh::lean_dec(v_isRemoved_x3f_4814_);
                        v___x_4905_ = crate::leanh::lean_box(0);
                        v_isShared_4906_ = v_isSharedCheck_4920_;
                        state = 21;
                        continue;
                    }
                }
            }
            21 => {
                v___x_4907_ = l_Lean_Json_getBool_x3f(v_val_4903_);
                crate::leanh::lean_dec(v_val_4903_);
                if crate::leanh::lean_obj_tag(v___x_4907_) == 0 {
                    crate::leanh::lean_del_object(v___x_4905_);
                    crate::leanh::lean_dec(v_____do__lift_4901_);
                    crate::leanh::lean_dec(v___y_4900_);
                    crate::leanh::lean_dec(v___y_4899_);
                    crate::leanh::lean_dec(v___y_4898_);
                    crate::leanh::lean_del_object(v___x_4883_);
                    crate::leanh::lean_dec(v_a_4881_);
                    crate::leanh::lean_dec(v_a_4860_);
                    crate::leanh::lean_dec(v_a_4839_);
                    crate::leanh::lean_del_object(v___x_4816_);
                    v_a_4908_ = crate::leanh::lean_ctor_get(v___x_4907_, 0);
                    v_isSharedCheck_4915_ = (!crate::leanh::lean_is_exclusive(v___x_4907_)) as u8;
                    if v_isSharedCheck_4915_ == 0 {
                        v___x_4910_ = v___x_4907_;
                        v_isShared_4911_ = v_isSharedCheck_4915_;
                        state = 22;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4908_);
                        crate::leanh::lean_dec(v___x_4907_);
                        v___x_4910_ = crate::leanh::lean_box(0);
                        v_isShared_4911_ = v_isSharedCheck_4915_;
                        state = 22;
                        continue;
                    }
                } else {
                    v_a_4916_ = crate::leanh::lean_ctor_get(v___x_4907_, 0);
                    crate::leanh::lean_inc(v_a_4916_);
                    crate::leanh::lean_dec_ref_known(v___x_4907_, 1);
                    if v_isShared_4906_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4905_, 0, v_a_4916_);
                        v___x_4918_ = v___x_4905_;
                        state = 24;
                        continue;
                    } else {
                        v_reuseFailAlloc_4919_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4919_, 0, v_a_4916_);
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
                    v_reuseFailAlloc_4914_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4914_, 0, v_a_4908_);
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
                if crate::leanh::lean_obj_tag(v_isInserted_x3f_4813_) == 0 {
                    v___x_4925_ = crate::leanh::lean_box(0);
                    v___y_4898_ = v___y_4922_;
                    v___y_4899_ = v___y_4923_;
                    v___y_4900_ = v_____do__lift_4924_;
                    v_____do__lift_4901_ = v___x_4925_;
                    state = 20;
                    continue;
                } else {
                    v_val_4926_ = crate::leanh::lean_ctor_get(v_isInserted_x3f_4813_, 0);
                    v_isSharedCheck_4943_ =
                        (!crate::leanh::lean_is_exclusive(v_isInserted_x3f_4813_)) as u8;
                    if v_isSharedCheck_4943_ == 0 {
                        v___x_4928_ = v_isInserted_x3f_4813_;
                        v_isShared_4929_ = v_isSharedCheck_4943_;
                        state = 26;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4926_);
                        crate::leanh::lean_dec(v_isInserted_x3f_4813_);
                        v___x_4928_ = crate::leanh::lean_box(0);
                        v_isShared_4929_ = v_isSharedCheck_4943_;
                        state = 26;
                        continue;
                    }
                }
            }
            26 => {
                v___x_4930_ = l_Lean_Json_getBool_x3f(v_val_4926_);
                crate::leanh::lean_dec(v_val_4926_);
                if crate::leanh::lean_obj_tag(v___x_4930_) == 0 {
                    crate::leanh::lean_del_object(v___x_4928_);
                    crate::leanh::lean_dec(v_____do__lift_4924_);
                    crate::leanh::lean_dec(v___y_4923_);
                    crate::leanh::lean_dec(v___y_4922_);
                    crate::leanh::lean_del_object(v___x_4883_);
                    crate::leanh::lean_dec(v_a_4881_);
                    crate::leanh::lean_dec(v_a_4860_);
                    crate::leanh::lean_dec(v_a_4839_);
                    crate::leanh::lean_del_object(v___x_4816_);
                    crate::leanh::lean_dec(v_isRemoved_x3f_4814_);
                    v_a_4931_ = crate::leanh::lean_ctor_get(v___x_4930_, 0);
                    v_isSharedCheck_4938_ = (!crate::leanh::lean_is_exclusive(v___x_4930_)) as u8;
                    if v_isSharedCheck_4938_ == 0 {
                        v___x_4933_ = v___x_4930_;
                        v_isShared_4934_ = v_isSharedCheck_4938_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4931_);
                        crate::leanh::lean_dec(v___x_4930_);
                        v___x_4933_ = crate::leanh::lean_box(0);
                        v_isShared_4934_ = v_isSharedCheck_4938_;
                        state = 27;
                        continue;
                    }
                } else {
                    v_a_4939_ = crate::leanh::lean_ctor_get(v___x_4930_, 0);
                    crate::leanh::lean_inc(v_a_4939_);
                    crate::leanh::lean_dec_ref_known(v___x_4930_, 1);
                    if v_isShared_4929_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4928_, 0, v_a_4939_);
                        v___x_4941_ = v___x_4928_;
                        state = 29;
                        continue;
                    } else {
                        v_reuseFailAlloc_4942_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4942_, 0, v_a_4939_);
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
                    v_reuseFailAlloc_4937_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4937_, 0, v_a_4931_);
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
                if crate::leanh::lean_obj_tag(v_isType_x3f_4812_) == 0 {
                    v___x_4947_ = crate::leanh::lean_box(0);
                    v___y_4922_ = v_____do__lift_4946_;
                    v___y_4923_ = v___y_4945_;
                    v_____do__lift_4924_ = v___x_4947_;
                    state = 25;
                    continue;
                } else {
                    v_val_4948_ = crate::leanh::lean_ctor_get(v_isType_x3f_4812_, 0);
                    v_isSharedCheck_4965_ =
                        (!crate::leanh::lean_is_exclusive(v_isType_x3f_4812_)) as u8;
                    if v_isSharedCheck_4965_ == 0 {
                        v___x_4950_ = v_isType_x3f_4812_;
                        v_isShared_4951_ = v_isSharedCheck_4965_;
                        state = 31;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4948_);
                        crate::leanh::lean_dec(v_isType_x3f_4812_);
                        v___x_4950_ = crate::leanh::lean_box(0);
                        v_isShared_4951_ = v_isSharedCheck_4965_;
                        state = 31;
                        continue;
                    }
                }
            }
            31 => {
                v___x_4952_ = l_Lean_Json_getBool_x3f(v_val_4948_);
                crate::leanh::lean_dec(v_val_4948_);
                if crate::leanh::lean_obj_tag(v___x_4952_) == 0 {
                    crate::leanh::lean_del_object(v___x_4950_);
                    crate::leanh::lean_dec(v_____do__lift_4946_);
                    crate::leanh::lean_dec(v___y_4945_);
                    crate::leanh::lean_del_object(v___x_4883_);
                    crate::leanh::lean_dec(v_a_4881_);
                    crate::leanh::lean_dec(v_a_4860_);
                    crate::leanh::lean_dec(v_a_4839_);
                    crate::leanh::lean_del_object(v___x_4816_);
                    crate::leanh::lean_dec(v_isRemoved_x3f_4814_);
                    crate::leanh::lean_dec(v_isInserted_x3f_4813_);
                    v_a_4953_ = crate::leanh::lean_ctor_get(v___x_4952_, 0);
                    v_isSharedCheck_4960_ = (!crate::leanh::lean_is_exclusive(v___x_4952_)) as u8;
                    if v_isSharedCheck_4960_ == 0 {
                        v___x_4955_ = v___x_4952_;
                        v_isShared_4956_ = v_isSharedCheck_4960_;
                        state = 32;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4953_);
                        crate::leanh::lean_dec(v___x_4952_);
                        v___x_4955_ = crate::leanh::lean_box(0);
                        v_isShared_4956_ = v_isSharedCheck_4960_;
                        state = 32;
                        continue;
                    }
                } else {
                    v_a_4961_ = crate::leanh::lean_ctor_get(v___x_4952_, 0);
                    crate::leanh::lean_inc(v_a_4961_);
                    crate::leanh::lean_dec_ref_known(v___x_4952_, 1);
                    if v_isShared_4951_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4950_, 0, v_a_4961_);
                        v___x_4963_ = v___x_4950_;
                        state = 34;
                        continue;
                    } else {
                        v_reuseFailAlloc_4964_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4964_, 0, v_a_4961_);
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
                    v_reuseFailAlloc_4959_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4959_, 0, v_a_4953_);
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
                if crate::leanh::lean_obj_tag(v_isInstance_x3f_4811_) == 0 {
                    v___x_4968_ = crate::leanh::lean_box(0);
                    v___y_4945_ = v_____do__lift_4967_;
                    v_____do__lift_4946_ = v___x_4968_;
                    state = 30;
                    continue;
                } else {
                    v_val_4969_ = crate::leanh::lean_ctor_get(v_isInstance_x3f_4811_, 0);
                    v_isSharedCheck_4986_ =
                        (!crate::leanh::lean_is_exclusive(v_isInstance_x3f_4811_)) as u8;
                    if v_isSharedCheck_4986_ == 0 {
                        v___x_4971_ = v_isInstance_x3f_4811_;
                        v_isShared_4972_ = v_isSharedCheck_4986_;
                        state = 36;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4969_);
                        crate::leanh::lean_dec(v_isInstance_x3f_4811_);
                        v___x_4971_ = crate::leanh::lean_box(0);
                        v_isShared_4972_ = v_isSharedCheck_4986_;
                        state = 36;
                        continue;
                    }
                }
            }
            36 => {
                v___x_4973_ = l_Lean_Json_getBool_x3f(v_val_4969_);
                crate::leanh::lean_dec(v_val_4969_);
                if crate::leanh::lean_obj_tag(v___x_4973_) == 0 {
                    crate::leanh::lean_del_object(v___x_4971_);
                    crate::leanh::lean_dec(v_____do__lift_4967_);
                    crate::leanh::lean_del_object(v___x_4883_);
                    crate::leanh::lean_dec(v_a_4881_);
                    crate::leanh::lean_dec(v_a_4860_);
                    crate::leanh::lean_dec(v_a_4839_);
                    crate::leanh::lean_del_object(v___x_4816_);
                    crate::leanh::lean_dec(v_isRemoved_x3f_4814_);
                    crate::leanh::lean_dec(v_isInserted_x3f_4813_);
                    crate::leanh::lean_dec(v_isType_x3f_4812_);
                    v_a_4974_ = crate::leanh::lean_ctor_get(v___x_4973_, 0);
                    v_isSharedCheck_4981_ = (!crate::leanh::lean_is_exclusive(v___x_4973_)) as u8;
                    if v_isSharedCheck_4981_ == 0 {
                        v___x_4976_ = v___x_4973_;
                        v_isShared_4977_ = v_isSharedCheck_4981_;
                        state = 37;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4974_);
                        crate::leanh::lean_dec(v___x_4973_);
                        v___x_4976_ = crate::leanh::lean_box(0);
                        v_isShared_4977_ = v_isSharedCheck_4981_;
                        state = 37;
                        continue;
                    }
                } else {
                    v_a_4982_ = crate::leanh::lean_ctor_get(v___x_4973_, 0);
                    crate::leanh::lean_inc(v_a_4982_);
                    crate::leanh::lean_dec_ref_known(v___x_4973_, 1);
                    if v_isShared_4972_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4971_, 0, v_a_4982_);
                        v___x_4984_ = v___x_4971_;
                        state = 39;
                        continue;
                    } else {
                        v_reuseFailAlloc_4985_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4985_, 0, v_a_4982_);
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
                    v_reuseFailAlloc_4980_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4980_, 0, v_a_4974_);
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
                if crate::leanh::lean_obj_tag(v___x_4992_) == 0 {
                    crate::leanh::lean_del_object(v___x_4990_);
                    crate::leanh::lean_del_object(v___x_4883_);
                    crate::leanh::lean_dec(v_a_4881_);
                    crate::leanh::lean_dec(v_a_4860_);
                    crate::leanh::lean_dec(v_a_4839_);
                    crate::leanh::lean_del_object(v___x_4816_);
                    crate::leanh::lean_dec(v_isRemoved_x3f_4814_);
                    crate::leanh::lean_dec(v_isInserted_x3f_4813_);
                    crate::leanh::lean_dec(v_isType_x3f_4812_);
                    crate::leanh::lean_dec(v_isInstance_x3f_4811_);
                    v_a_4993_ = crate::leanh::lean_ctor_get(v___x_4992_, 0);
                    v_isSharedCheck_5000_ = (!crate::leanh::lean_is_exclusive(v___x_4992_)) as u8;
                    if v_isSharedCheck_5000_ == 0 {
                        v___x_4995_ = v___x_4992_;
                        v_isShared_4996_ = v_isSharedCheck_5000_;
                        state = 41;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4993_);
                        crate::leanh::lean_dec(v___x_4992_);
                        v___x_4995_ = crate::leanh::lean_box(0);
                        v_isShared_4996_ = v_isSharedCheck_5000_;
                        state = 41;
                        continue;
                    }
                } else {
                    v_a_5001_ = crate::leanh::lean_ctor_get(v___x_4992_, 0);
                    crate::leanh::lean_inc(v_a_5001_);
                    crate::leanh::lean_dec_ref_known(v___x_4992_, 1);
                    v___x_5002_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5___redArg(v___x_4871_, v_a_5001_, v_a_4796_);
                    if crate::leanh::lean_obj_tag(v___x_5002_) == 0 {
                        crate::leanh::lean_del_object(v___x_4990_);
                        crate::leanh::lean_del_object(v___x_4883_);
                        crate::leanh::lean_dec(v_a_4881_);
                        crate::leanh::lean_dec(v_a_4860_);
                        crate::leanh::lean_dec(v_a_4839_);
                        crate::leanh::lean_del_object(v___x_4816_);
                        crate::leanh::lean_dec(v_isRemoved_x3f_4814_);
                        crate::leanh::lean_dec(v_isInserted_x3f_4813_);
                        crate::leanh::lean_dec(v_isType_x3f_4812_);
                        crate::leanh::lean_dec(v_isInstance_x3f_4811_);
                        v_a_5003_ = crate::leanh::lean_ctor_get(v___x_5002_, 0);
                        v_isSharedCheck_5010_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5002_)) as u8;
                        if v_isSharedCheck_5010_ == 0 {
                            v___x_5005_ = v___x_5002_;
                            v_isShared_5006_ = v_isSharedCheck_5010_;
                            state = 43;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5003_);
                            crate::leanh::lean_dec(v___x_5002_);
                            v___x_5005_ = crate::leanh::lean_box(0);
                            v_isShared_5006_ = v_isSharedCheck_5010_;
                            state = 43;
                            continue;
                        }
                    } else {
                        v_a_5011_ = crate::leanh::lean_ctor_get(v___x_5002_, 0);
                        crate::leanh::lean_inc(v_a_5011_);
                        crate::leanh::lean_dec_ref_known(v___x_5002_, 1);
                        if v_isShared_4991_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4990_, 0, v_a_5011_);
                            v___x_5013_ = v___x_4990_;
                            state = 45;
                            continue;
                        } else {
                            v_reuseFailAlloc_5014_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5014_, 0, v_a_5011_);
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
                    v_reuseFailAlloc_4999_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_a_4993_);
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
                    v_reuseFailAlloc_5009_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5009_, 0, v_a_5003_);
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
    mut v_j_5018_: *mut crate::leanh::LeanObject,
    mut v_a_5019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5020_ = l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_(v_j_5018_, v_a_5019_);
    crate::leanh::lean_dec_ref(v_a_5019_);
    return v_res_5020_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2(
    mut v_sz_5021_: usize,
    mut v_i_5022_: usize,
    mut v_bs_5023_: *mut crate::leanh::LeanObject,
    mut v___y_5024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5025_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___redArg(v_sz_5021_, v_i_5022_, v_bs_5023_);
    return v___x_5025_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___boxed(
    mut v_sz_5026_: *mut crate::leanh::LeanObject,
    mut v_i_5027_: *mut crate::leanh::LeanObject,
    mut v_bs_5028_: *mut crate::leanh::LeanObject,
    mut v___y_5029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5030_: usize = 0;
    let mut v_i_boxed_5031_: usize = 0;
    let mut v_res_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5030_ = crate::leanh::lean_unbox_usize(v_sz_5026_);
    crate::leanh::lean_dec(v_sz_5026_);
    v_i_boxed_5031_ = crate::leanh::lean_unbox_usize(v_i_5027_);
    crate::leanh::lean_dec(v_i_5027_);
    v_res_5032_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2(v_sz_boxed_5030_, v_i_boxed_5031_, v_bs_5028_, v___y_5029_);
    crate::leanh::lean_dec_ref(v___y_5029_);
    return v_res_5032_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3(
    mut v_sz_5033_: usize,
    mut v_i_5034_: usize,
    mut v_bs_5035_: *mut crate::leanh::LeanObject,
    mut v___y_5036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3___redArg(v_sz_5033_, v_i_5034_, v_bs_5035_);
    return v___x_5037_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3___boxed(
    mut v_sz_5038_: *mut crate::leanh::LeanObject,
    mut v_i_5039_: *mut crate::leanh::LeanObject,
    mut v_bs_5040_: *mut crate::leanh::LeanObject,
    mut v___y_5041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5042_: usize = 0;
    let mut v_i_boxed_5043_: usize = 0;
    let mut v_res_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5042_ = crate::leanh::lean_unbox_usize(v_sz_5038_);
    crate::leanh::lean_dec(v_sz_5038_);
    v_i_boxed_5043_ = crate::leanh::lean_unbox_usize(v_i_5039_);
    crate::leanh::lean_dec(v_i_5039_);
    v_res_5044_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3(v_sz_boxed_5042_, v_i_boxed_5043_, v_bs_5040_, v___y_5041_);
    crate::leanh::lean_dec_ref(v___y_5041_);
    return v_res_5044_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5(
    mut v_00_u03b1_5045_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5046_: *mut crate::leanh::LeanObject,
    mut v_f_5047_: *mut crate::leanh::LeanObject,
    mut v_x_5048_: *mut crate::leanh::LeanObject,
    mut v___y_5049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5050_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5___redArg(v_f_5047_, v_x_5048_, v___y_5049_);
    return v___x_5050_;
}
pub unsafe fn l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5___boxed(
    mut v_00_u03b1_5051_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5052_: *mut crate::leanh::LeanObject,
    mut v_f_5053_: *mut crate::leanh::LeanObject,
    mut v_x_5054_: *mut crate::leanh::LeanObject,
    mut v___y_5055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5056_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5(v_00_u03b1_5051_, v_00_u03b2_5052_, v_f_5053_, v_x_5054_, v___y_5055_);
    crate::leanh::lean_dec_ref(v___y_5055_);
    return v_res_5056_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5_spec__7(
    mut v_00_u03b1_5057_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5058_: *mut crate::leanh::LeanObject,
    mut v_f_5059_: *mut crate::leanh::LeanObject,
    mut v_sz_5060_: usize,
    mut v_i_5061_: usize,
    mut v_bs_5062_: *mut crate::leanh::LeanObject,
    mut v___y_5063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5064_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5_spec__7___redArg(v_f_5059_, v_sz_5060_, v_i_5061_, v_bs_5062_, v___y_5063_);
    return v___x_5064_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5_spec__7___boxed(
    mut v_00_u03b1_5065_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_5066_: *mut crate::leanh::LeanObject,
    mut v_f_5067_: *mut crate::leanh::LeanObject,
    mut v_sz_5068_: *mut crate::leanh::LeanObject,
    mut v_i_5069_: *mut crate::leanh::LeanObject,
    mut v_bs_5070_: *mut crate::leanh::LeanObject,
    mut v___y_5071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5072_: usize = 0;
    let mut v_i_boxed_5073_: usize = 0;
    let mut v_res_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5072_ = crate::leanh::lean_unbox_usize(v_sz_5068_);
    crate::leanh::lean_dec(v_sz_5068_);
    v_i_boxed_5073_ = crate::leanh::lean_unbox_usize(v_i_5069_);
    crate::leanh::lean_dec(v_i_5069_);
    v_res_5074_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5_spec__7(v_00_u03b1_5065_, v_00_u03b2_5066_, v_f_5067_, v_sz_boxed_5072_, v_i_boxed_5073_, v_bs_5070_, v___y_5071_);
    crate::leanh::lean_dec_ref(v___y_5071_);
    return v_res_5074_;
}
pub unsafe fn l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_(
    mut v_json_5086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5113_: u8 = 0;
    let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5118_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5087_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
                crate::leanh::lean_inc_n(v_json_5086_, 7);
                v___x_5088_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_5086_, v___x_5087_);
                v_a_5089_ = crate::leanh::lean_ctor_get(v___x_5088_, 0);
                crate::leanh::lean_inc(v_a_5089_);
                crate::leanh::lean_dec_ref(v___x_5088_);
                v___x_5090_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
                v___x_5091_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_5086_, v___x_5090_);
                v_a_5092_ = crate::leanh::lean_ctor_get(v___x_5091_, 0);
                crate::leanh::lean_inc(v_a_5092_);
                crate::leanh::lean_dec_ref(v___x_5091_);
                v___x_5093_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
                v___x_5094_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_5086_, v___x_5093_);
                v_a_5095_ = crate::leanh::lean_ctor_get(v___x_5094_, 0);
                crate::leanh::lean_inc(v_a_5095_);
                crate::leanh::lean_dec_ref(v___x_5094_);
                v___x_5096_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
                v___x_5097_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1(v_json_5086_, v___x_5096_);
                v_a_5098_ = crate::leanh::lean_ctor_get(v___x_5097_, 0);
                crate::leanh::lean_inc(v_a_5098_);
                crate::leanh::lean_dec_ref(v___x_5097_);
                v___x_5099_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
                v___x_5100_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_5086_, v___x_5099_);
                v_a_5101_ = crate::leanh::lean_ctor_get(v___x_5100_, 0);
                crate::leanh::lean_inc(v_a_5101_);
                crate::leanh::lean_dec_ref(v___x_5100_);
                v___x_5102_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
                v___x_5103_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_5086_, v___x_5102_);
                v_a_5104_ = crate::leanh::lean_ctor_get(v___x_5103_, 0);
                crate::leanh::lean_inc(v_a_5104_);
                crate::leanh::lean_dec_ref(v___x_5103_);
                v___x_5105_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
                v___x_5106_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1(v_json_5086_, v___x_5105_);
                v_a_5107_ = crate::leanh::lean_ctor_get(v___x_5106_, 0);
                crate::leanh::lean_inc(v_a_5107_);
                crate::leanh::lean_dec_ref(v___x_5106_);
                v___x_5108_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
                v___x_5109_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__1(v_json_5086_, v___x_5108_);
                v_a_5110_ = crate::leanh::lean_ctor_get(v___x_5109_, 0);
                v_isSharedCheck_5118_ = (!crate::leanh::lean_is_exclusive(v___x_5109_)) as u8;
                if v_isSharedCheck_5118_ == 0 {
                    v___x_5112_ = v___x_5109_;
                    v_isShared_5113_ = v_isSharedCheck_5118_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5110_);
                    crate::leanh::lean_dec(v___x_5109_);
                    v___x_5112_ = crate::leanh::lean_box(0);
                    v_isShared_5113_ = v_isSharedCheck_5118_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5114_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5114_, 0, v_a_5089_);
                crate::leanh::lean_ctor_set(v___x_5114_, 1, v_a_5092_);
                crate::leanh::lean_ctor_set(v___x_5114_, 2, v_a_5095_);
                crate::leanh::lean_ctor_set(v___x_5114_, 3, v_a_5098_);
                crate::leanh::lean_ctor_set(v___x_5114_, 4, v_a_5101_);
                crate::leanh::lean_ctor_set(v___x_5114_, 5, v_a_5104_);
                crate::leanh::lean_ctor_set(v___x_5114_, 6, v_a_5107_);
                crate::leanh::lean_ctor_set(v___x_5114_, 7, v_a_5110_);
                if v_isShared_5113_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5112_, 0, v___x_5114_);
                    v___x_5116_ = v___x_5112_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5117_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5117_, 0, v___x_5114_);
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
    mut v_x_5121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hyps_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_x3f_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_goalPrefix_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInserted_x3f_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRemoved_x3f_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_hyps_5122_ = crate::leanh::lean_ctor_get(v_x_5121_, 0);
    v_type_5123_ = crate::leanh::lean_ctor_get(v_x_5121_, 1);
    v_ctx_5124_ = crate::leanh::lean_ctor_get(v_x_5121_, 2);
    v_userName_x3f_5125_ = crate::leanh::lean_ctor_get(v_x_5121_, 3);
    v_goalPrefix_5126_ = crate::leanh::lean_ctor_get(v_x_5121_, 4);
    v_mvarId_5127_ = crate::leanh::lean_ctor_get(v_x_5121_, 5);
    v_isInserted_x3f_5128_ = crate::leanh::lean_ctor_get(v_x_5121_, 6);
    v_isRemoved_x3f_5129_ = crate::leanh::lean_ctor_get(v_x_5121_, 7);
    v___x_5130_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
    crate::leanh::lean_inc(v_hyps_5122_);
    v___x_5131_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5131_, 0, v___x_5130_);
    crate::leanh::lean_ctor_set(v___x_5131_, 1, v_hyps_5122_);
    v___x_5132_ = crate::leanh::lean_box(0);
    v___x_5133_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5133_, 0, v___x_5131_);
    crate::leanh::lean_ctor_set(v___x_5133_, 1, v___x_5132_);
    v___x_5134_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
    crate::leanh::lean_inc(v_type_5123_);
    v___x_5135_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5135_, 0, v___x_5134_);
    crate::leanh::lean_ctor_set(v___x_5135_, 1, v_type_5123_);
    v___x_5136_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5136_, 0, v___x_5135_);
    crate::leanh::lean_ctor_set(v___x_5136_, 1, v___x_5132_);
    v___x_5137_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
    crate::leanh::lean_inc(v_ctx_5124_);
    v___x_5138_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5138_, 0, v___x_5137_);
    crate::leanh::lean_ctor_set(v___x_5138_, 1, v_ctx_5124_);
    v___x_5139_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5139_, 0, v___x_5138_);
    crate::leanh::lean_ctor_set(v___x_5139_, 1, v___x_5132_);
    v___x_5140_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
    v___x_5141_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__0(v___x_5140_, v_userName_x3f_5125_);
    v___x_5142_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__3_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
    crate::leanh::lean_inc(v_goalPrefix_5126_);
    v___x_5143_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5143_, 0, v___x_5142_);
    crate::leanh::lean_ctor_set(v___x_5143_, 1, v_goalPrefix_5126_);
    v___x_5144_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5144_, 0, v___x_5143_);
    crate::leanh::lean_ctor_set(v___x_5144_, 1, v___x_5132_);
    v___x_5145_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__4_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
    crate::leanh::lean_inc(v_mvarId_5127_);
    v___x_5146_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5146_, 0, v___x_5145_);
    crate::leanh::lean_ctor_set(v___x_5146_, 1, v_mvarId_5127_);
    v___x_5147_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5147_, 0, v___x_5146_);
    crate::leanh::lean_ctor_set(v___x_5147_, 1, v___x_5132_);
    v___x_5148_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__6_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
    v___x_5149_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__0(v___x_5148_, v_isInserted_x3f_5128_);
    v___x_5150_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__7_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
    v___x_5151_ = l_Lean_Json_opt___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__0(v___x_5150_, v_isRemoved_x3f_5129_);
    v___x_5152_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5152_, 0, v___x_5151_);
    crate::leanh::lean_ctor_set(v___x_5152_, 1, v___x_5132_);
    v___x_5153_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5153_, 0, v___x_5149_);
    crate::leanh::lean_ctor_set(v___x_5153_, 1, v___x_5152_);
    v___x_5154_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5154_, 0, v___x_5147_);
    crate::leanh::lean_ctor_set(v___x_5154_, 1, v___x_5153_);
    v___x_5155_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5155_, 0, v___x_5144_);
    crate::leanh::lean_ctor_set(v___x_5155_, 1, v___x_5154_);
    v___x_5156_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5156_, 0, v___x_5141_);
    crate::leanh::lean_ctor_set(v___x_5156_, 1, v___x_5155_);
    v___x_5157_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5157_, 0, v___x_5139_);
    crate::leanh::lean_ctor_set(v___x_5157_, 1, v___x_5156_);
    v___x_5158_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5158_, 0, v___x_5136_);
    crate::leanh::lean_ctor_set(v___x_5158_, 1, v___x_5157_);
    v___x_5159_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5159_, 0, v___x_5133_);
    crate::leanh::lean_ctor_set(v___x_5159_, 1, v___x_5158_);
    v___x_5160_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47_;
    v___x_5161_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__1(v___x_5159_, v___x_5160_);
    v___x_5162_ = l_Lean_Json_mkObj(v___x_5161_);
    crate::leanh::lean_dec(v___x_5161_);
    return v___x_5162_;
}
pub unsafe fn l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_45____boxed(
    mut v_x_5163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5164_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_45_(v_x_5163_);
    crate::leanh::lean_dec_ref(v_x_5163_);
    return v_res_5164_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoal_enc_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1__spec__0(
    mut v_sz_5167_: usize,
    mut v_i_5168_: usize,
    mut v_bs_5169_: *mut crate::leanh::LeanObject,
    mut v___y_5170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5171_: u8 = 0;
    let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: usize = 0;
    let mut v___x_5180_: usize = 0;
    let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5171_ = lean_usize_dec_lt(v_i_5168_, v_sz_5167_);
                if v___x_5171_ == 0 {
                    v___x_5172_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5172_, 0, v_bs_5169_);
                    crate::leanh::lean_ctor_set(v___x_5172_, 1, v___y_5170_);
                    return v___x_5172_;
                } else {
                    v_v_5173_ = lean_array_uget_borrowed(v_bs_5169_, v_i_5168_);
                    crate::leanh::lean_inc(v_v_5173_);
                    v___x_5174_ = l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_(v_v_5173_, v___y_5170_);
                    v_fst_5175_ = crate::leanh::lean_ctor_get(v___x_5174_, 0);
                    crate::leanh::lean_inc(v_fst_5175_);
                    v_snd_5176_ = crate::leanh::lean_ctor_get(v___x_5174_, 1);
                    crate::leanh::lean_inc(v_snd_5176_);
                    crate::leanh::lean_dec_ref(v___x_5174_);
                    v___x_5177_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_5183_: *mut crate::leanh::LeanObject,
    mut v_i_5184_: *mut crate::leanh::LeanObject,
    mut v_bs_5185_: *mut crate::leanh::LeanObject,
    mut v___y_5186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5187_: usize = 0;
    let mut v_i_boxed_5188_: usize = 0;
    let mut v_res_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5187_ = crate::leanh::lean_unbox_usize(v_sz_5183_);
    crate::leanh::lean_dec(v_sz_5183_);
    v_i_boxed_5188_ = crate::leanh::lean_unbox_usize(v_i_5184_);
    crate::leanh::lean_dec(v_i_5184_);
    v_res_5189_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoal_enc_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1__spec__0(v_sz_boxed_5187_, v_i_boxed_5188_, v_bs_5185_, v___y_5186_);
    return v_res_5189_;
}
pub unsafe fn l_Lean_Widget_instRpcEncodableInteractiveGoal_enc_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1_(
    mut v_a_5190_: *mut crate::leanh::LeanObject,
    mut v_a_5191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toInteractiveGoalCore_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_x3f_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_goalPrefix_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInserted_x3f_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRemoved_x3f_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5201_: usize = 0;
    let mut v___x_5202_: usize = 0;
    let mut v___x_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5216_: u8 = 0;
    let mut v___x_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5241_: u8 = 0;
    let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: u8 = 0;
    let mut v___x_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5247_: u8 = 0;
    let mut v_fst_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: u8 = 0;
    let mut v___x_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5258_: u8 = 0;
    let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: u8 = 0;
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5264_: u8 = 0;
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5269_: u8 = 0;
    let mut v___x_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5274_: u8 = 0;
    let mut v_isSharedCheck_5275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInteractiveGoalCore_5192_ = crate::leanh::lean_ctor_get(v_a_5190_, 0);
                crate::leanh::lean_inc_ref(v_toInteractiveGoalCore_5192_);
                v_userName_x3f_5193_ = crate::leanh::lean_ctor_get(v_a_5190_, 1);
                crate::leanh::lean_inc(v_userName_x3f_5193_);
                v_goalPrefix_5194_ = crate::leanh::lean_ctor_get(v_a_5190_, 2);
                crate::leanh::lean_inc_ref(v_goalPrefix_5194_);
                v_mvarId_5195_ = crate::leanh::lean_ctor_get(v_a_5190_, 3);
                crate::leanh::lean_inc(v_mvarId_5195_);
                v_isInserted_x3f_5196_ = crate::leanh::lean_ctor_get(v_a_5190_, 4);
                crate::leanh::lean_inc(v_isInserted_x3f_5196_);
                v_isRemoved_x3f_5197_ = crate::leanh::lean_ctor_get(v_a_5190_, 5);
                crate::leanh::lean_inc(v_isRemoved_x3f_5197_);
                crate::leanh::lean_dec_ref(v_a_5190_);
                v_hyps_5198_ = crate::leanh::lean_ctor_get(v_toInteractiveGoalCore_5192_, 0);
                crate::leanh::lean_inc_ref(v_hyps_5198_);
                v_type_5199_ = crate::leanh::lean_ctor_get(v_toInteractiveGoalCore_5192_, 1);
                crate::leanh::lean_inc_ref(v_type_5199_);
                v_ctx_5200_ = crate::leanh::lean_ctor_get(v_toInteractiveGoalCore_5192_, 2);
                crate::leanh::lean_inc_ref(v_ctx_5200_);
                crate::leanh::lean_dec_ref(v_toInteractiveGoalCore_5192_);
                v_sz_5201_ = lean_array_size(v_hyps_5198_);
                v___x_5202_ = 0usize;
                v___x_5203_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoal_enc_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1__spec__0(v_sz_5201_, v___x_5202_, v_hyps_5198_, v_a_5191_);
                v_fst_5204_ = crate::leanh::lean_ctor_get(v___x_5203_, 0);
                crate::leanh::lean_inc(v_fst_5204_);
                v_snd_5205_ = crate::leanh::lean_ctor_get(v___x_5203_, 1);
                crate::leanh::lean_inc(v_snd_5205_);
                crate::leanh::lean_dec_ref(v___x_5203_);
                v___x_5206_ = l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc___closed__0_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_;
                v___x_5207_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___redArg(v___x_5206_, v_type_5199_, v_snd_5205_);
                v_fst_5208_ = crate::leanh::lean_ctor_get(v___x_5207_, 0);
                crate::leanh::lean_inc(v_fst_5208_);
                v_snd_5209_ = crate::leanh::lean_ctor_get(v___x_5207_, 1);
                crate::leanh::lean_inc(v_snd_5209_);
                crate::leanh::lean_dec_ref(v___x_5207_);
                v___x_5210_ =
                    l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_2318528980____hygCtx___hyg_3_;
                v___x_5211_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(
                    v___x_5210_,
                    v_ctx_5200_,
                    v_snd_5209_,
                );
                crate::leanh::lean_dec_ref(v_ctx_5200_);
                v_fst_5212_ = crate::leanh::lean_ctor_get(v___x_5211_, 0);
                v_snd_5213_ = crate::leanh::lean_ctor_get(v___x_5211_, 1);
                v_isSharedCheck_5275_ = (!crate::leanh::lean_is_exclusive(v___x_5211_)) as u8;
                if v_isSharedCheck_5275_ == 0 {
                    v___x_5215_ = v___x_5211_;
                    v_isShared_5216_ = v_isSharedCheck_5275_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5213_);
                    crate::leanh::lean_inc(v_fst_5212_);
                    crate::leanh::lean_dec(v___x_5211_);
                    v___x_5215_ = crate::leanh::lean_box(0);
                    v_isShared_5216_ = v_isSharedCheck_5275_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5217_ = l_Array_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3(v_fst_5204_);
                v___x_5218_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(v_fst_5208_);
                if crate::leanh::lean_obj_tag(v_userName_x3f_5193_) == 0 {
                    v___x_5265_ = crate::leanh::lean_box(0);
                    v_fst_5249_ = v___x_5265_;
                    state = 7;
                    continue;
                } else {
                    v_val_5266_ = crate::leanh::lean_ctor_get(v_userName_x3f_5193_, 0);
                    v_isSharedCheck_5274_ =
                        (!crate::leanh::lean_is_exclusive(v_userName_x3f_5193_)) as u8;
                    if v_isSharedCheck_5274_ == 0 {
                        v___x_5268_ = v_userName_x3f_5193_;
                        v_isShared_5269_ = v_isSharedCheck_5274_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5266_);
                        crate::leanh::lean_dec(v_userName_x3f_5193_);
                        v___x_5268_ = crate::leanh::lean_box(0);
                        v_isShared_5269_ = v_isSharedCheck_5274_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5226_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5226_, 0, v___x_5217_);
                crate::leanh::lean_ctor_set(v___x_5226_, 1, v___x_5218_);
                crate::leanh::lean_ctor_set(v___x_5226_, 2, v_fst_5212_);
                crate::leanh::lean_ctor_set(v___x_5226_, 3, v___y_5223_);
                crate::leanh::lean_ctor_set(v___x_5226_, 4, v___y_5220_);
                crate::leanh::lean_ctor_set(v___x_5226_, 5, v___y_5222_);
                crate::leanh::lean_ctor_set(v___x_5226_, 6, v___y_5221_);
                crate::leanh::lean_ctor_set(v___x_5226_, 7, v_fst_5224_);
                v___x_5227_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_45_(v___x_5226_);
                crate::leanh::lean_dec_ref_known(v___x_5226_, 8);
                if v_isShared_5216_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5215_, 1, v_snd_5225_);
                    crate::leanh::lean_ctor_set(v___x_5215_, 0, v___x_5227_);
                    v___x_5229_ = v___x_5215_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5230_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5230_, 0, v___x_5227_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5230_, 1, v_snd_5225_);
                    v___x_5229_ = v_reuseFailAlloc_5230_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5229_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_isRemoved_x3f_5197_) == 0 {
                    v___x_5237_ = crate::leanh::lean_box(0);
                    v___y_5220_ = v___y_5232_;
                    v___y_5221_ = v_fst_5235_;
                    v___y_5222_ = v___y_5233_;
                    v___y_5223_ = v___y_5234_;
                    v_fst_5224_ = v___x_5237_;
                    v_snd_5225_ = v_snd_5236_;
                    state = 2;
                    continue;
                } else {
                    v_val_5238_ = crate::leanh::lean_ctor_get(v_isRemoved_x3f_5197_, 0);
                    v_isSharedCheck_5247_ =
                        (!crate::leanh::lean_is_exclusive(v_isRemoved_x3f_5197_)) as u8;
                    if v_isSharedCheck_5247_ == 0 {
                        v___x_5240_ = v_isRemoved_x3f_5197_;
                        v_isShared_5241_ = v_isSharedCheck_5247_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5238_);
                        crate::leanh::lean_dec(v_isRemoved_x3f_5197_);
                        v___x_5240_ = crate::leanh::lean_box(0);
                        v_isShared_5241_ = v_isSharedCheck_5247_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___x_5242_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_5243_ = (crate::leanh::lean_unbox(v_val_5238_) as u8);
                crate::leanh::lean_dec(v_val_5238_);
                crate::leanh::lean_ctor_set_uint8(v___x_5242_, 0 as u32, v___x_5243_);
                if v_isShared_5241_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5240_, 0, v___x_5242_);
                    v___x_5245_ = v___x_5240_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5246_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 0, v___x_5242_);
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
                v___x_5250_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5250_, 0, v_goalPrefix_5194_);
                v___x_5251_ = 1;
                v___x_5252_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_mvarId_5195_,
                    v___x_5251_,
                );
                v___x_5253_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5253_, 0, v___x_5252_);
                if crate::leanh::lean_obj_tag(v_isInserted_x3f_5196_) == 0 {
                    v___x_5254_ = crate::leanh::lean_box(0);
                    v___y_5232_ = v___x_5250_;
                    v___y_5233_ = v___x_5253_;
                    v___y_5234_ = v_fst_5249_;
                    v_fst_5235_ = v___x_5254_;
                    v_snd_5236_ = v_snd_5213_;
                    state = 4;
                    continue;
                } else {
                    v_val_5255_ = crate::leanh::lean_ctor_get(v_isInserted_x3f_5196_, 0);
                    v_isSharedCheck_5264_ =
                        (!crate::leanh::lean_is_exclusive(v_isInserted_x3f_5196_)) as u8;
                    if v_isSharedCheck_5264_ == 0 {
                        v___x_5257_ = v_isInserted_x3f_5196_;
                        v_isShared_5258_ = v_isSharedCheck_5264_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5255_);
                        crate::leanh::lean_dec(v_isInserted_x3f_5196_);
                        v___x_5257_ = crate::leanh::lean_box(0);
                        v_isShared_5258_ = v_isSharedCheck_5264_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                v___x_5259_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_5260_ = (crate::leanh::lean_unbox(v_val_5255_) as u8);
                crate::leanh::lean_dec(v_val_5255_);
                crate::leanh::lean_ctor_set_uint8(v___x_5259_, 0 as u32, v___x_5260_);
                if v_isShared_5258_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5257_, 0, v___x_5259_);
                    v___x_5262_ = v___x_5257_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5263_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5263_, 0, v___x_5259_);
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
                v___x_5270_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5270_, 0, v_val_5266_);
                if v_isShared_5269_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5268_, 0, v___x_5270_);
                    v___x_5272_ = v___x_5268_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5273_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5273_, 0, v___x_5270_);
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
    mut v_bs_5278_: *mut crate::leanh::LeanObject,
    mut v___y_5279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5280_: u8 = 0;
    let mut v___x_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5287_: u8 = 0;
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5291_: u8 = 0;
    let mut v_a_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: usize = 0;
    let mut v___x_5296_: usize = 0;
    let mut v___x_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5280_ = lean_usize_dec_lt(v_i_5277_, v_sz_5276_);
                if v___x_5280_ == 0 {
                    v___x_5281_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5281_, 0, v_bs_5278_);
                    return v___x_5281_;
                } else {
                    v_v_5282_ = lean_array_uget_borrowed(v_bs_5278_, v_i_5277_);
                    crate::leanh::lean_inc(v_v_5282_);
                    v___x_5283_ = l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_(v_v_5282_, v___y_5279_);
                    if crate::leanh::lean_obj_tag(v___x_5283_) == 0 {
                        crate::leanh::lean_dec_ref(v_bs_5278_);
                        v_a_5284_ = crate::leanh::lean_ctor_get(v___x_5283_, 0);
                        v_isSharedCheck_5291_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5283_)) as u8;
                        if v_isSharedCheck_5291_ == 0 {
                            v___x_5286_ = v___x_5283_;
                            v_isShared_5287_ = v_isSharedCheck_5291_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5284_);
                            crate::leanh::lean_dec(v___x_5283_);
                            v___x_5286_ = crate::leanh::lean_box(0);
                            v_isShared_5287_ = v_isSharedCheck_5291_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5292_ = crate::leanh::lean_ctor_get(v___x_5283_, 0);
                        crate::leanh::lean_inc(v_a_5292_);
                        crate::leanh::lean_dec_ref_known(v___x_5283_, 1);
                        v___x_5293_ = crate::leanh::lean_unsigned_to_nat(0);
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
                    v_reuseFailAlloc_5290_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5290_, 0, v_a_5284_);
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
    mut v_sz_5299_: *mut crate::leanh::LeanObject,
    mut v_i_5300_: *mut crate::leanh::LeanObject,
    mut v_bs_5301_: *mut crate::leanh::LeanObject,
    mut v___y_5302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5303_: usize = 0;
    let mut v_i_boxed_5304_: usize = 0;
    let mut v_res_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5303_ = crate::leanh::lean_unbox_usize(v_sz_5299_);
    crate::leanh::lean_dec(v_sz_5299_);
    v_i_boxed_5304_ = crate::leanh::lean_unbox_usize(v_i_5300_);
    crate::leanh::lean_dec(v_i_5300_);
    v_res_5305_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoal_dec_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1__spec__0(v_sz_boxed_5303_, v_i_boxed_5304_, v_bs_5301_, v___y_5302_);
    crate::leanh::lean_dec_ref(v___y_5302_);
    return v_res_5305_;
}
pub unsafe fn l_Lean_Widget_instRpcEncodableInteractiveGoal_dec_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1_(
    mut v_j_5306_: *mut crate::leanh::LeanObject,
    mut v_a_5307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5312_: u8 = 0;
    let mut v___x_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5316_: u8 = 0;
    let mut v_a_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_x3f_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_goalPrefix_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInserted_x3f_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRemoved_x3f_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5330_: u8 = 0;
    let mut v___x_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5334_: u8 = 0;
    let mut v_a_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5336_: usize = 0;
    let mut v___x_5337_: usize = 0;
    let mut v___x_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5342_: u8 = 0;
    let mut v___x_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5346_: u8 = 0;
    let mut v_a_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5352_: u8 = 0;
    let mut v___x_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5356_: u8 = 0;
    let mut v_a_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5363_: u8 = 0;
    let mut v___x_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5367_: u8 = 0;
    let mut v_a_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5374_: u8 = 0;
    let mut v___x_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5378_: u8 = 0;
    let mut v_a_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5382_: u8 = 0;
    let mut v___y_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_____do__lift_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_____do__lift_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5403_: u8 = 0;
    let mut v___x_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5408_: u8 = 0;
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5412_: u8 = 0;
    let mut v_a_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5417_: u8 = 0;
    let mut v_____do__lift_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5424_: u8 = 0;
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5428_: u8 = 0;
    let mut v_a_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5434_: u8 = 0;
    let mut v___x_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5438_: u8 = 0;
    let mut v_a_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5445_: u8 = 0;
    let mut v___x_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5450_: u8 = 0;
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5454_: u8 = 0;
    let mut v_a_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5459_: u8 = 0;
    let mut v___x_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5464_: u8 = 0;
    let mut v___x_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5469_: u8 = 0;
    let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5473_: u8 = 0;
    let mut v_a_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5478_: u8 = 0;
    let mut v_isSharedCheck_5479_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5308_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_(v_j_5306_);
                if crate::leanh::lean_obj_tag(v___x_5308_) == 0 {
                    v_a_5309_ = crate::leanh::lean_ctor_get(v___x_5308_, 0);
                    v_isSharedCheck_5316_ = (!crate::leanh::lean_is_exclusive(v___x_5308_)) as u8;
                    if v_isSharedCheck_5316_ == 0 {
                        v___x_5311_ = v___x_5308_;
                        v_isShared_5312_ = v_isSharedCheck_5316_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5309_);
                        crate::leanh::lean_dec(v___x_5308_);
                        v___x_5311_ = crate::leanh::lean_box(0);
                        v_isShared_5312_ = v_isSharedCheck_5316_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5317_ = crate::leanh::lean_ctor_get(v___x_5308_, 0);
                    crate::leanh::lean_inc(v_a_5317_);
                    crate::leanh::lean_dec_ref_known(v___x_5308_, 1);
                    v_hyps_5318_ = crate::leanh::lean_ctor_get(v_a_5317_, 0);
                    crate::leanh::lean_inc(v_hyps_5318_);
                    v_type_5319_ = crate::leanh::lean_ctor_get(v_a_5317_, 1);
                    crate::leanh::lean_inc(v_type_5319_);
                    v_ctx_5320_ = crate::leanh::lean_ctor_get(v_a_5317_, 2);
                    crate::leanh::lean_inc(v_ctx_5320_);
                    v_userName_x3f_5321_ = crate::leanh::lean_ctor_get(v_a_5317_, 3);
                    crate::leanh::lean_inc(v_userName_x3f_5321_);
                    v_goalPrefix_5322_ = crate::leanh::lean_ctor_get(v_a_5317_, 4);
                    crate::leanh::lean_inc(v_goalPrefix_5322_);
                    v_mvarId_5323_ = crate::leanh::lean_ctor_get(v_a_5317_, 5);
                    crate::leanh::lean_inc(v_mvarId_5323_);
                    v_isInserted_x3f_5324_ = crate::leanh::lean_ctor_get(v_a_5317_, 6);
                    crate::leanh::lean_inc(v_isInserted_x3f_5324_);
                    v_isRemoved_x3f_5325_ = crate::leanh::lean_ctor_get(v_a_5317_, 7);
                    crate::leanh::lean_inc(v_isRemoved_x3f_5325_);
                    crate::leanh::lean_dec(v_a_5317_);
                    v___x_5326_ = l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0(v_hyps_5318_);
                    if crate::leanh::lean_obj_tag(v___x_5326_) == 0 {
                        crate::leanh::lean_dec(v_isRemoved_x3f_5325_);
                        crate::leanh::lean_dec(v_isInserted_x3f_5324_);
                        crate::leanh::lean_dec(v_mvarId_5323_);
                        crate::leanh::lean_dec(v_goalPrefix_5322_);
                        crate::leanh::lean_dec(v_userName_x3f_5321_);
                        crate::leanh::lean_dec(v_ctx_5320_);
                        crate::leanh::lean_dec(v_type_5319_);
                        v_a_5327_ = crate::leanh::lean_ctor_get(v___x_5326_, 0);
                        v_isSharedCheck_5334_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5326_)) as u8;
                        if v_isSharedCheck_5334_ == 0 {
                            v___x_5329_ = v___x_5326_;
                            v_isShared_5330_ = v_isSharedCheck_5334_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5327_);
                            crate::leanh::lean_dec(v___x_5326_);
                            v___x_5329_ = crate::leanh::lean_box(0);
                            v_isShared_5330_ = v_isSharedCheck_5334_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5335_ = crate::leanh::lean_ctor_get(v___x_5326_, 0);
                        crate::leanh::lean_inc(v_a_5335_);
                        crate::leanh::lean_dec_ref_known(v___x_5326_, 1);
                        v_sz_5336_ = lean_array_size(v_a_5335_);
                        v___x_5337_ = 0usize;
                        v___x_5338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoal_dec_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1__spec__0(v_sz_5336_, v___x_5337_, v_a_5335_, v_a_5307_);
                        if crate::leanh::lean_obj_tag(v___x_5338_) == 0 {
                            crate::leanh::lean_dec(v_isRemoved_x3f_5325_);
                            crate::leanh::lean_dec(v_isInserted_x3f_5324_);
                            crate::leanh::lean_dec(v_mvarId_5323_);
                            crate::leanh::lean_dec(v_goalPrefix_5322_);
                            crate::leanh::lean_dec(v_userName_x3f_5321_);
                            crate::leanh::lean_dec(v_ctx_5320_);
                            crate::leanh::lean_dec(v_type_5319_);
                            v_a_5339_ = crate::leanh::lean_ctor_get(v___x_5338_, 0);
                            v_isSharedCheck_5346_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5338_)) as u8;
                            if v_isSharedCheck_5346_ == 0 {
                                v___x_5341_ = v___x_5338_;
                                v_isShared_5342_ = v_isSharedCheck_5346_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5339_);
                                crate::leanh::lean_dec(v___x_5338_);
                                v___x_5341_ = crate::leanh::lean_box(0);
                                v_isShared_5342_ = v_isSharedCheck_5346_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v_a_5347_ = crate::leanh::lean_ctor_get(v___x_5338_, 0);
                            crate::leanh::lean_inc(v_a_5347_);
                            crate::leanh::lean_dec_ref_known(v___x_5338_, 1);
                            v___x_5348_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(v_type_5319_);
                            if crate::leanh::lean_obj_tag(v___x_5348_) == 0 {
                                crate::leanh::lean_dec(v_a_5347_);
                                crate::leanh::lean_dec(v_isRemoved_x3f_5325_);
                                crate::leanh::lean_dec(v_isInserted_x3f_5324_);
                                crate::leanh::lean_dec(v_mvarId_5323_);
                                crate::leanh::lean_dec(v_goalPrefix_5322_);
                                crate::leanh::lean_dec(v_userName_x3f_5321_);
                                crate::leanh::lean_dec(v_ctx_5320_);
                                v_a_5349_ = crate::leanh::lean_ctor_get(v___x_5348_, 0);
                                v_isSharedCheck_5356_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5348_)) as u8;
                                if v_isSharedCheck_5356_ == 0 {
                                    v___x_5351_ = v___x_5348_;
                                    v_isShared_5352_ = v_isSharedCheck_5356_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5349_);
                                    crate::leanh::lean_dec(v___x_5348_);
                                    v___x_5351_ = crate::leanh::lean_box(0);
                                    v_isShared_5352_ = v_isSharedCheck_5356_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_5357_ = crate::leanh::lean_ctor_get(v___x_5348_, 0);
                                crate::leanh::lean_inc(v_a_5357_);
                                crate::leanh::lean_dec_ref_known(v___x_5348_, 1);
                                v___x_5358_ = l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec___closed__0_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_;
                                v___x_5359_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5___redArg(v___x_5358_, v_a_5357_, v_a_5307_);
                                if crate::leanh::lean_obj_tag(v___x_5359_) == 0 {
                                    crate::leanh::lean_dec(v_a_5347_);
                                    crate::leanh::lean_dec(v_isRemoved_x3f_5325_);
                                    crate::leanh::lean_dec(v_isInserted_x3f_5324_);
                                    crate::leanh::lean_dec(v_mvarId_5323_);
                                    crate::leanh::lean_dec(v_goalPrefix_5322_);
                                    crate::leanh::lean_dec(v_userName_x3f_5321_);
                                    crate::leanh::lean_dec(v_ctx_5320_);
                                    v_a_5360_ = crate::leanh::lean_ctor_get(v___x_5359_, 0);
                                    v_isSharedCheck_5367_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5359_)) as u8;
                                    if v_isSharedCheck_5367_ == 0 {
                                        v___x_5362_ = v___x_5359_;
                                        v_isShared_5363_ = v_isSharedCheck_5367_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5360_);
                                        crate::leanh::lean_dec(v___x_5359_);
                                        v___x_5362_ = crate::leanh::lean_box(0);
                                        v_isShared_5363_ = v_isSharedCheck_5367_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    v_a_5368_ = crate::leanh::lean_ctor_get(v___x_5359_, 0);
                                    crate::leanh::lean_inc(v_a_5368_);
                                    crate::leanh::lean_dec_ref_known(v___x_5359_, 1);
                                    v___x_5369_ = l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_2318528980____hygCtx___hyg_3_;
                                    v___x_5370_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(v___x_5369_, v_ctx_5320_, v_a_5307_);
                                    if crate::leanh::lean_obj_tag(v___x_5370_) == 0 {
                                        crate::leanh::lean_dec(v_a_5368_);
                                        crate::leanh::lean_dec(v_a_5347_);
                                        crate::leanh::lean_dec(v_isRemoved_x3f_5325_);
                                        crate::leanh::lean_dec(v_isInserted_x3f_5324_);
                                        crate::leanh::lean_dec(v_mvarId_5323_);
                                        crate::leanh::lean_dec(v_goalPrefix_5322_);
                                        crate::leanh::lean_dec(v_userName_x3f_5321_);
                                        v_a_5371_ = crate::leanh::lean_ctor_get(v___x_5370_, 0);
                                        v_isSharedCheck_5378_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5370_)) as u8;
                                        if v_isSharedCheck_5378_ == 0 {
                                            v___x_5373_ = v___x_5370_;
                                            v_isShared_5374_ = v_isSharedCheck_5378_;
                                            state = 11;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5371_);
                                            crate::leanh::lean_dec(v___x_5370_);
                                            v___x_5373_ = crate::leanh::lean_box(0);
                                            v_isShared_5374_ = v_isSharedCheck_5378_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_5379_ = crate::leanh::lean_ctor_get(v___x_5370_, 0);
                                        v_isSharedCheck_5479_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5370_)) as u8;
                                        if v_isSharedCheck_5479_ == 0 {
                                            v___x_5381_ = v___x_5370_;
                                            v_isShared_5382_ = v_isSharedCheck_5479_;
                                            state = 13;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5379_);
                                            crate::leanh::lean_dec(v___x_5370_);
                                            v___x_5381_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5315_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5315_, 0, v_a_5309_);
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
                    v_reuseFailAlloc_5333_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5333_, 0, v_a_5327_);
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
                    v_reuseFailAlloc_5345_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5345_, 0, v_a_5339_);
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
                    v_reuseFailAlloc_5355_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5355_, 0, v_a_5349_);
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
                    v_reuseFailAlloc_5366_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_a_5360_);
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
                    v_reuseFailAlloc_5377_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5377_, 0, v_a_5371_);
                    v___x_5376_ = v_reuseFailAlloc_5377_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5376_;
            }
            13 => {
                if crate::leanh::lean_obj_tag(v_userName_x3f_5321_) == 0 {
                    v___x_5460_ = crate::leanh::lean_box(0);
                    v_____do__lift_5419_ = v___x_5460_;
                    state = 21;
                    continue;
                } else {
                    v_val_5461_ = crate::leanh::lean_ctor_get(v_userName_x3f_5321_, 0);
                    v_isSharedCheck_5478_ =
                        (!crate::leanh::lean_is_exclusive(v_userName_x3f_5321_)) as u8;
                    if v_isSharedCheck_5478_ == 0 {
                        v___x_5463_ = v_userName_x3f_5321_;
                        v_isShared_5464_ = v_isSharedCheck_5478_;
                        state = 30;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5461_);
                        crate::leanh::lean_dec(v_userName_x3f_5321_);
                        v___x_5463_ = crate::leanh::lean_box(0);
                        v_isShared_5464_ = v_isSharedCheck_5478_;
                        state = 30;
                        continue;
                    }
                }
            }
            14 => {
                v___x_5389_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5389_, 0, v_a_5347_);
                crate::leanh::lean_ctor_set(v___x_5389_, 1, v_a_5368_);
                crate::leanh::lean_ctor_set(v___x_5389_, 2, v_a_5379_);
                v___x_5390_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5390_, 0, v___x_5389_);
                crate::leanh::lean_ctor_set(v___x_5390_, 1, v___y_5387_);
                crate::leanh::lean_ctor_set(v___x_5390_, 2, v___y_5386_);
                crate::leanh::lean_ctor_set(v___x_5390_, 3, v___y_5384_);
                crate::leanh::lean_ctor_set(v___x_5390_, 4, v___y_5385_);
                crate::leanh::lean_ctor_set(v___x_5390_, 5, v_____do__lift_5388_);
                if v_isShared_5382_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5381_, 0, v___x_5390_);
                    v___x_5392_ = v___x_5381_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5393_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5393_, 0, v___x_5390_);
                    v___x_5392_ = v_reuseFailAlloc_5393_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5392_;
            }
            16 => {
                if crate::leanh::lean_obj_tag(v_isRemoved_x3f_5325_) == 0 {
                    v___x_5399_ = crate::leanh::lean_box(0);
                    v___y_5384_ = v___y_5395_;
                    v___y_5385_ = v_____do__lift_5398_;
                    v___y_5386_ = v___y_5396_;
                    v___y_5387_ = v___y_5397_;
                    v_____do__lift_5388_ = v___x_5399_;
                    state = 14;
                    continue;
                } else {
                    v_val_5400_ = crate::leanh::lean_ctor_get(v_isRemoved_x3f_5325_, 0);
                    v_isSharedCheck_5417_ =
                        (!crate::leanh::lean_is_exclusive(v_isRemoved_x3f_5325_)) as u8;
                    if v_isSharedCheck_5417_ == 0 {
                        v___x_5402_ = v_isRemoved_x3f_5325_;
                        v_isShared_5403_ = v_isSharedCheck_5417_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5400_);
                        crate::leanh::lean_dec(v_isRemoved_x3f_5325_);
                        v___x_5402_ = crate::leanh::lean_box(0);
                        v_isShared_5403_ = v_isSharedCheck_5417_;
                        state = 17;
                        continue;
                    }
                }
            }
            17 => {
                v___x_5404_ = l_Lean_Json_getBool_x3f(v_val_5400_);
                crate::leanh::lean_dec(v_val_5400_);
                if crate::leanh::lean_obj_tag(v___x_5404_) == 0 {
                    crate::leanh::lean_del_object(v___x_5402_);
                    crate::leanh::lean_dec(v_____do__lift_5398_);
                    crate::leanh::lean_dec(v___y_5397_);
                    crate::leanh::lean_dec_ref(v___y_5396_);
                    crate::leanh::lean_dec(v___y_5395_);
                    crate::leanh::lean_del_object(v___x_5381_);
                    crate::leanh::lean_dec(v_a_5379_);
                    crate::leanh::lean_dec(v_a_5368_);
                    crate::leanh::lean_dec(v_a_5347_);
                    v_a_5405_ = crate::leanh::lean_ctor_get(v___x_5404_, 0);
                    v_isSharedCheck_5412_ = (!crate::leanh::lean_is_exclusive(v___x_5404_)) as u8;
                    if v_isSharedCheck_5412_ == 0 {
                        v___x_5407_ = v___x_5404_;
                        v_isShared_5408_ = v_isSharedCheck_5412_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5405_);
                        crate::leanh::lean_dec(v___x_5404_);
                        v___x_5407_ = crate::leanh::lean_box(0);
                        v_isShared_5408_ = v_isSharedCheck_5412_;
                        state = 18;
                        continue;
                    }
                } else {
                    v_a_5413_ = crate::leanh::lean_ctor_get(v___x_5404_, 0);
                    crate::leanh::lean_inc(v_a_5413_);
                    crate::leanh::lean_dec_ref_known(v___x_5404_, 1);
                    if v_isShared_5403_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5402_, 0, v_a_5413_);
                        v___x_5415_ = v___x_5402_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_5416_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5416_, 0, v_a_5413_);
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
                    v_reuseFailAlloc_5411_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5411_, 0, v_a_5405_);
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
                if crate::leanh::lean_obj_tag(v___x_5420_) == 0 {
                    crate::leanh::lean_dec(v_____do__lift_5419_);
                    crate::leanh::lean_del_object(v___x_5381_);
                    crate::leanh::lean_dec(v_a_5379_);
                    crate::leanh::lean_dec(v_a_5368_);
                    crate::leanh::lean_dec(v_a_5347_);
                    crate::leanh::lean_dec(v_isRemoved_x3f_5325_);
                    crate::leanh::lean_dec(v_isInserted_x3f_5324_);
                    crate::leanh::lean_dec(v_mvarId_5323_);
                    v_a_5421_ = crate::leanh::lean_ctor_get(v___x_5420_, 0);
                    v_isSharedCheck_5428_ = (!crate::leanh::lean_is_exclusive(v___x_5420_)) as u8;
                    if v_isSharedCheck_5428_ == 0 {
                        v___x_5423_ = v___x_5420_;
                        v_isShared_5424_ = v_isSharedCheck_5428_;
                        state = 22;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5421_);
                        crate::leanh::lean_dec(v___x_5420_);
                        v___x_5423_ = crate::leanh::lean_box(0);
                        v_isShared_5424_ = v_isSharedCheck_5428_;
                        state = 22;
                        continue;
                    }
                } else {
                    v_a_5429_ = crate::leanh::lean_ctor_get(v___x_5420_, 0);
                    crate::leanh::lean_inc(v_a_5429_);
                    crate::leanh::lean_dec_ref_known(v___x_5420_, 1);
                    v___x_5430_ = l_Lean_Name_fromJson_x3f(v_mvarId_5323_);
                    if crate::leanh::lean_obj_tag(v___x_5430_) == 0 {
                        crate::leanh::lean_dec(v_a_5429_);
                        crate::leanh::lean_dec(v_____do__lift_5419_);
                        crate::leanh::lean_del_object(v___x_5381_);
                        crate::leanh::lean_dec(v_a_5379_);
                        crate::leanh::lean_dec(v_a_5368_);
                        crate::leanh::lean_dec(v_a_5347_);
                        crate::leanh::lean_dec(v_isRemoved_x3f_5325_);
                        crate::leanh::lean_dec(v_isInserted_x3f_5324_);
                        v_a_5431_ = crate::leanh::lean_ctor_get(v___x_5430_, 0);
                        v_isSharedCheck_5438_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5430_)) as u8;
                        if v_isSharedCheck_5438_ == 0 {
                            v___x_5433_ = v___x_5430_;
                            v_isShared_5434_ = v_isSharedCheck_5438_;
                            state = 24;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5431_);
                            crate::leanh::lean_dec(v___x_5430_);
                            v___x_5433_ = crate::leanh::lean_box(0);
                            v_isShared_5434_ = v_isSharedCheck_5438_;
                            state = 24;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v_isInserted_x3f_5324_) == 0 {
                            v_a_5439_ = crate::leanh::lean_ctor_get(v___x_5430_, 0);
                            crate::leanh::lean_inc(v_a_5439_);
                            crate::leanh::lean_dec_ref_known(v___x_5430_, 1);
                            v___x_5440_ = crate::leanh::lean_box(0);
                            v___y_5395_ = v_a_5439_;
                            v___y_5396_ = v_a_5429_;
                            v___y_5397_ = v_____do__lift_5419_;
                            v_____do__lift_5398_ = v___x_5440_;
                            state = 16;
                            continue;
                        } else {
                            v_a_5441_ = crate::leanh::lean_ctor_get(v___x_5430_, 0);
                            crate::leanh::lean_inc(v_a_5441_);
                            crate::leanh::lean_dec_ref_known(v___x_5430_, 1);
                            v_val_5442_ = crate::leanh::lean_ctor_get(v_isInserted_x3f_5324_, 0);
                            v_isSharedCheck_5459_ =
                                (!crate::leanh::lean_is_exclusive(v_isInserted_x3f_5324_)) as u8;
                            if v_isSharedCheck_5459_ == 0 {
                                v___x_5444_ = v_isInserted_x3f_5324_;
                                v_isShared_5445_ = v_isSharedCheck_5459_;
                                state = 26;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_5442_);
                                crate::leanh::lean_dec(v_isInserted_x3f_5324_);
                                v___x_5444_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5427_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5427_, 0, v_a_5421_);
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
                    v_reuseFailAlloc_5437_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5437_, 0, v_a_5431_);
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
                crate::leanh::lean_dec(v_val_5442_);
                if crate::leanh::lean_obj_tag(v___x_5446_) == 0 {
                    crate::leanh::lean_del_object(v___x_5444_);
                    crate::leanh::lean_dec(v_a_5441_);
                    crate::leanh::lean_dec(v_a_5429_);
                    crate::leanh::lean_dec(v_____do__lift_5419_);
                    crate::leanh::lean_del_object(v___x_5381_);
                    crate::leanh::lean_dec(v_a_5379_);
                    crate::leanh::lean_dec(v_a_5368_);
                    crate::leanh::lean_dec(v_a_5347_);
                    crate::leanh::lean_dec(v_isRemoved_x3f_5325_);
                    v_a_5447_ = crate::leanh::lean_ctor_get(v___x_5446_, 0);
                    v_isSharedCheck_5454_ = (!crate::leanh::lean_is_exclusive(v___x_5446_)) as u8;
                    if v_isSharedCheck_5454_ == 0 {
                        v___x_5449_ = v___x_5446_;
                        v_isShared_5450_ = v_isSharedCheck_5454_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5447_);
                        crate::leanh::lean_dec(v___x_5446_);
                        v___x_5449_ = crate::leanh::lean_box(0);
                        v_isShared_5450_ = v_isSharedCheck_5454_;
                        state = 27;
                        continue;
                    }
                } else {
                    v_a_5455_ = crate::leanh::lean_ctor_get(v___x_5446_, 0);
                    crate::leanh::lean_inc(v_a_5455_);
                    crate::leanh::lean_dec_ref_known(v___x_5446_, 1);
                    if v_isShared_5445_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5444_, 0, v_a_5455_);
                        v___x_5457_ = v___x_5444_;
                        state = 29;
                        continue;
                    } else {
                        v_reuseFailAlloc_5458_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5458_, 0, v_a_5455_);
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
                    v_reuseFailAlloc_5453_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5453_, 0, v_a_5447_);
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
                if crate::leanh::lean_obj_tag(v___x_5465_) == 0 {
                    crate::leanh::lean_del_object(v___x_5463_);
                    crate::leanh::lean_del_object(v___x_5381_);
                    crate::leanh::lean_dec(v_a_5379_);
                    crate::leanh::lean_dec(v_a_5368_);
                    crate::leanh::lean_dec(v_a_5347_);
                    crate::leanh::lean_dec(v_isRemoved_x3f_5325_);
                    crate::leanh::lean_dec(v_isInserted_x3f_5324_);
                    crate::leanh::lean_dec(v_mvarId_5323_);
                    crate::leanh::lean_dec(v_goalPrefix_5322_);
                    v_a_5466_ = crate::leanh::lean_ctor_get(v___x_5465_, 0);
                    v_isSharedCheck_5473_ = (!crate::leanh::lean_is_exclusive(v___x_5465_)) as u8;
                    if v_isSharedCheck_5473_ == 0 {
                        v___x_5468_ = v___x_5465_;
                        v_isShared_5469_ = v_isSharedCheck_5473_;
                        state = 31;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5466_);
                        crate::leanh::lean_dec(v___x_5465_);
                        v___x_5468_ = crate::leanh::lean_box(0);
                        v_isShared_5469_ = v_isSharedCheck_5473_;
                        state = 31;
                        continue;
                    }
                } else {
                    v_a_5474_ = crate::leanh::lean_ctor_get(v___x_5465_, 0);
                    crate::leanh::lean_inc(v_a_5474_);
                    crate::leanh::lean_dec_ref_known(v___x_5465_, 1);
                    if v_isShared_5464_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5463_, 0, v_a_5474_);
                        v___x_5476_ = v___x_5463_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_5477_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5477_, 0, v_a_5474_);
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
                    v_reuseFailAlloc_5472_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5472_, 0, v_a_5466_);
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
    mut v_j_5480_: *mut crate::leanh::LeanObject,
    mut v_a_5481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5482_ = l_Lean_Widget_instRpcEncodableInteractiveGoal_dec_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1_(v_j_5480_, v_a_5481_);
    crate::leanh::lean_dec_ref(v_a_5481_);
    return v_res_5482_;
}
pub unsafe fn l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18_(
    mut v_json_5491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5509_: u8 = 0;
    let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5514_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5492_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
                crate::leanh::lean_inc_n(v_json_5491_, 4);
                v___x_5493_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_5491_, v___x_5492_);
                v_a_5494_ = crate::leanh::lean_ctor_get(v___x_5493_, 0);
                crate::leanh::lean_inc(v_a_5494_);
                crate::leanh::lean_dec_ref(v___x_5493_);
                v___x_5495_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
                v___x_5496_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_5491_, v___x_5495_);
                v_a_5497_ = crate::leanh::lean_ctor_get(v___x_5496_, 0);
                crate::leanh::lean_inc(v_a_5497_);
                crate::leanh::lean_dec_ref(v___x_5496_);
                v___x_5498_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
                v___x_5499_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_5491_, v___x_5498_);
                v_a_5500_ = crate::leanh::lean_ctor_get(v___x_5499_, 0);
                crate::leanh::lean_inc(v_a_5500_);
                crate::leanh::lean_dec_ref(v___x_5499_);
                v___x_5501_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18_;
                v___x_5502_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_5491_, v___x_5501_);
                v_a_5503_ = crate::leanh::lean_ctor_get(v___x_5502_, 0);
                crate::leanh::lean_inc(v_a_5503_);
                crate::leanh::lean_dec_ref(v___x_5502_);
                v___x_5504_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18_;
                v___x_5505_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_5491_, v___x_5504_);
                v_a_5506_ = crate::leanh::lean_ctor_get(v___x_5505_, 0);
                v_isSharedCheck_5514_ = (!crate::leanh::lean_is_exclusive(v___x_5505_)) as u8;
                if v_isSharedCheck_5514_ == 0 {
                    v___x_5508_ = v___x_5505_;
                    v_isShared_5509_ = v_isSharedCheck_5514_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5506_);
                    crate::leanh::lean_dec(v___x_5505_);
                    v___x_5508_ = crate::leanh::lean_box(0);
                    v_isShared_5509_ = v_isSharedCheck_5514_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5510_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5510_, 0, v_a_5494_);
                crate::leanh::lean_ctor_set(v___x_5510_, 1, v_a_5497_);
                crate::leanh::lean_ctor_set(v___x_5510_, 2, v_a_5500_);
                crate::leanh::lean_ctor_set(v___x_5510_, 3, v_a_5503_);
                crate::leanh::lean_ctor_set(v___x_5510_, 4, v_a_5506_);
                if v_isShared_5509_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5508_, 0, v___x_5510_);
                    v___x_5512_ = v___x_5508_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5513_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5513_, 0, v___x_5510_);
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
    mut v_x_5517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_hyps_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_hyps_5518_ = crate::leanh::lean_ctor_get(v_x_5517_, 0);
    v_type_5519_ = crate::leanh::lean_ctor_get(v_x_5517_, 1);
    v_ctx_5520_ = crate::leanh::lean_ctor_get(v_x_5517_, 2);
    v_range_5521_ = crate::leanh::lean_ctor_get(v_x_5517_, 3);
    v_term_5522_ = crate::leanh::lean_ctor_get(v_x_5517_, 4);
    v___x_5523_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
    crate::leanh::lean_inc(v_hyps_5518_);
    v___x_5524_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5524_, 0, v___x_5523_);
    crate::leanh::lean_ctor_set(v___x_5524_, 1, v_hyps_5518_);
    v___x_5525_ = crate::leanh::lean_box(0);
    v___x_5526_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5526_, 0, v___x_5524_);
    crate::leanh::lean_ctor_set(v___x_5526_, 1, v___x_5525_);
    v___x_5527_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29_;
    crate::leanh::lean_inc(v_type_5519_);
    v___x_5528_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5528_, 0, v___x_5527_);
    crate::leanh::lean_ctor_set(v___x_5528_, 1, v_type_5519_);
    v___x_5529_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5529_, 0, v___x_5528_);
    crate::leanh::lean_ctor_set(v___x_5529_, 1, v___x_5525_);
    v___x_5530_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_1056429149____hygCtx___hyg_27_;
    crate::leanh::lean_inc(v_ctx_5520_);
    v___x_5531_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5531_, 0, v___x_5530_);
    crate::leanh::lean_ctor_set(v___x_5531_, 1, v_ctx_5520_);
    v___x_5532_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5532_, 0, v___x_5531_);
    crate::leanh::lean_ctor_set(v___x_5532_, 1, v___x_5525_);
    v___x_5533_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18_;
    crate::leanh::lean_inc(v_range_5521_);
    v___x_5534_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5534_, 0, v___x_5533_);
    crate::leanh::lean_ctor_set(v___x_5534_, 1, v_range_5521_);
    v___x_5535_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5535_, 0, v___x_5534_);
    crate::leanh::lean_ctor_set(v___x_5535_, 1, v___x_5525_);
    v___x_5536_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18_;
    crate::leanh::lean_inc(v_term_5522_);
    v___x_5537_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5537_, 0, v___x_5536_);
    crate::leanh::lean_ctor_set(v___x_5537_, 1, v_term_5522_);
    v___x_5538_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5538_, 0, v___x_5537_);
    crate::leanh::lean_ctor_set(v___x_5538_, 1, v___x_5525_);
    v___x_5539_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5539_, 0, v___x_5538_);
    crate::leanh::lean_ctor_set(v___x_5539_, 1, v___x_5525_);
    v___x_5540_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5540_, 0, v___x_5535_);
    crate::leanh::lean_ctor_set(v___x_5540_, 1, v___x_5539_);
    v___x_5541_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5541_, 0, v___x_5532_);
    crate::leanh::lean_ctor_set(v___x_5541_, 1, v___x_5540_);
    v___x_5542_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5542_, 0, v___x_5529_);
    crate::leanh::lean_ctor_set(v___x_5542_, 1, v___x_5541_);
    v___x_5543_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5543_, 0, v___x_5526_);
    crate::leanh::lean_ctor_set(v___x_5543_, 1, v___x_5542_);
    v___x_5544_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47_;
    v___x_5545_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__1(v___x_5543_, v___x_5544_);
    v___x_5546_ = l_Lean_Json_mkObj(v___x_5545_);
    crate::leanh::lean_dec(v___x_5545_);
    return v___x_5546_;
}
pub unsafe fn l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_36____boxed(
    mut v_x_5547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5548_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_36_(v_x_5547_);
    crate::leanh::lean_dec_ref(v_x_5547_);
    return v_res_5548_;
}
pub unsafe fn l_Lean_Widget_instRpcEncodableInteractiveTermGoal_enc_00___x40_Lean_Widget_InteractiveGoal_2553565095____hygCtx___hyg_1_(
    mut v_a_5551_: *mut crate::leanh::LeanObject,
    mut v_a_5552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toInteractiveGoalCore_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5559_: usize = 0;
    let mut v___x_5560_: usize = 0;
    let mut v___x_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5578_: u8 = 0;
    let mut v___x_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInteractiveGoalCore_5553_ = crate::leanh::lean_ctor_get(v_a_5551_, 0);
                crate::leanh::lean_inc_ref(v_toInteractiveGoalCore_5553_);
                v_range_5554_ = crate::leanh::lean_ctor_get(v_a_5551_, 1);
                crate::leanh::lean_inc_ref(v_range_5554_);
                v_term_5555_ = crate::leanh::lean_ctor_get(v_a_5551_, 2);
                crate::leanh::lean_inc_ref(v_term_5555_);
                crate::leanh::lean_dec_ref(v_a_5551_);
                v_hyps_5556_ = crate::leanh::lean_ctor_get(v_toInteractiveGoalCore_5553_, 0);
                crate::leanh::lean_inc_ref(v_hyps_5556_);
                v_type_5557_ = crate::leanh::lean_ctor_get(v_toInteractiveGoalCore_5553_, 1);
                crate::leanh::lean_inc_ref(v_type_5557_);
                v_ctx_5558_ = crate::leanh::lean_ctor_get(v_toInteractiveGoalCore_5553_, 2);
                crate::leanh::lean_inc_ref(v_ctx_5558_);
                crate::leanh::lean_dec_ref(v_toInteractiveGoalCore_5553_);
                v_sz_5559_ = lean_array_size(v_hyps_5556_);
                v___x_5560_ = 0usize;
                v___x_5561_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoal_enc_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1__spec__0(v_sz_5559_, v___x_5560_, v_hyps_5556_, v_a_5552_);
                v_fst_5562_ = crate::leanh::lean_ctor_get(v___x_5561_, 0);
                crate::leanh::lean_inc(v_fst_5562_);
                v_snd_5563_ = crate::leanh::lean_ctor_get(v___x_5561_, 1);
                crate::leanh::lean_inc(v_snd_5563_);
                crate::leanh::lean_dec_ref(v___x_5561_);
                v___x_5564_ = l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc___closed__0_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_;
                v___x_5565_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__2___redArg(v___x_5564_, v_type_5557_, v_snd_5563_);
                v_fst_5566_ = crate::leanh::lean_ctor_get(v___x_5565_, 0);
                crate::leanh::lean_inc(v_fst_5566_);
                v_snd_5567_ = crate::leanh::lean_ctor_get(v___x_5565_, 1);
                crate::leanh::lean_inc(v_snd_5567_);
                crate::leanh::lean_dec_ref(v___x_5565_);
                v___x_5568_ =
                    l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_2318528980____hygCtx___hyg_3_;
                v___x_5569_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(
                    v___x_5568_,
                    v_ctx_5558_,
                    v_snd_5567_,
                );
                crate::leanh::lean_dec_ref(v_ctx_5558_);
                v_fst_5570_ = crate::leanh::lean_ctor_get(v___x_5569_, 0);
                crate::leanh::lean_inc(v_fst_5570_);
                v_snd_5571_ = crate::leanh::lean_ctor_get(v___x_5569_, 1);
                crate::leanh::lean_inc(v_snd_5571_);
                crate::leanh::lean_dec_ref(v___x_5569_);
                v___x_5572_ =
                    l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_173954553____hygCtx___hyg_3_;
                v___x_5573_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcEncode___redArg(
                    v___x_5572_,
                    v_term_5555_,
                    v_snd_5571_,
                );
                crate::leanh::lean_dec_ref(v_term_5555_);
                v_fst_5574_ = crate::leanh::lean_ctor_get(v___x_5573_, 0);
                v_snd_5575_ = crate::leanh::lean_ctor_get(v___x_5573_, 1);
                v_isSharedCheck_5587_ = (!crate::leanh::lean_is_exclusive(v___x_5573_)) as u8;
                if v_isSharedCheck_5587_ == 0 {
                    v___x_5577_ = v___x_5573_;
                    v_isShared_5578_ = v_isSharedCheck_5587_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5575_);
                    crate::leanh::lean_inc(v_fst_5574_);
                    crate::leanh::lean_dec(v___x_5573_);
                    v___x_5577_ = crate::leanh::lean_box(0);
                    v_isShared_5578_ = v_isSharedCheck_5587_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5579_ = l_Array_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3(v_fst_5562_);
                v___x_5580_ = l_Lean_Widget_instToJsonTaggedText_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(v_fst_5566_);
                v___x_5581_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_5554_);
                v___x_5582_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5582_, 0, v___x_5579_);
                crate::leanh::lean_ctor_set(v___x_5582_, 1, v___x_5580_);
                crate::leanh::lean_ctor_set(v___x_5582_, 2, v_fst_5570_);
                crate::leanh::lean_ctor_set(v___x_5582_, 3, v___x_5581_);
                crate::leanh::lean_ctor_set(v___x_5582_, 4, v_fst_5574_);
                v___x_5583_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_36_(v___x_5582_);
                crate::leanh::lean_dec_ref_known(v___x_5582_, 5);
                if v_isShared_5578_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5577_, 0, v___x_5583_);
                    v___x_5585_ = v___x_5577_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5586_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5586_, 0, v___x_5583_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5586_, 1, v_snd_5575_);
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
    mut v_j_5588_: *mut crate::leanh::LeanObject,
    mut v_a_5589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5594_: u8 = 0;
    let mut v___x_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5598_: u8 = 0;
    let mut v_a_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5609_: u8 = 0;
    let mut v___x_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5613_: u8 = 0;
    let mut v_a_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5615_: usize = 0;
    let mut v___x_5616_: usize = 0;
    let mut v___x_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5621_: u8 = 0;
    let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5625_: u8 = 0;
    let mut v_a_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5631_: u8 = 0;
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5635_: u8 = 0;
    let mut v_a_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5642_: u8 = 0;
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5646_: u8 = 0;
    let mut v_a_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5653_: u8 = 0;
    let mut v___x_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5657_: u8 = 0;
    let mut v_a_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5663_: u8 = 0;
    let mut v___x_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5667_: u8 = 0;
    let mut v_a_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5674_: u8 = 0;
    let mut v___x_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5678_: u8 = 0;
    let mut v_a_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5682_: u8 = 0;
    let mut v___x_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5688_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5590_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_2427803292____hygCtx___hyg_18_(v_j_5588_);
                if crate::leanh::lean_obj_tag(v___x_5590_) == 0 {
                    v_a_5591_ = crate::leanh::lean_ctor_get(v___x_5590_, 0);
                    v_isSharedCheck_5598_ = (!crate::leanh::lean_is_exclusive(v___x_5590_)) as u8;
                    if v_isSharedCheck_5598_ == 0 {
                        v___x_5593_ = v___x_5590_;
                        v_isShared_5594_ = v_isSharedCheck_5598_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5591_);
                        crate::leanh::lean_dec(v___x_5590_);
                        v___x_5593_ = crate::leanh::lean_box(0);
                        v_isShared_5594_ = v_isSharedCheck_5598_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5599_ = crate::leanh::lean_ctor_get(v___x_5590_, 0);
                    crate::leanh::lean_inc(v_a_5599_);
                    crate::leanh::lean_dec_ref_known(v___x_5590_, 1);
                    v_hyps_5600_ = crate::leanh::lean_ctor_get(v_a_5599_, 0);
                    crate::leanh::lean_inc(v_hyps_5600_);
                    v_type_5601_ = crate::leanh::lean_ctor_get(v_a_5599_, 1);
                    crate::leanh::lean_inc(v_type_5601_);
                    v_ctx_5602_ = crate::leanh::lean_ctor_get(v_a_5599_, 2);
                    crate::leanh::lean_inc(v_ctx_5602_);
                    v_range_5603_ = crate::leanh::lean_ctor_get(v_a_5599_, 3);
                    crate::leanh::lean_inc(v_range_5603_);
                    v_term_5604_ = crate::leanh::lean_ctor_get(v_a_5599_, 4);
                    crate::leanh::lean_inc(v_term_5604_);
                    crate::leanh::lean_dec(v_a_5599_);
                    v___x_5605_ = l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0(v_hyps_5600_);
                    if crate::leanh::lean_obj_tag(v___x_5605_) == 0 {
                        crate::leanh::lean_dec(v_term_5604_);
                        crate::leanh::lean_dec(v_range_5603_);
                        crate::leanh::lean_dec(v_ctx_5602_);
                        crate::leanh::lean_dec(v_type_5601_);
                        v_a_5606_ = crate::leanh::lean_ctor_get(v___x_5605_, 0);
                        v_isSharedCheck_5613_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5605_)) as u8;
                        if v_isSharedCheck_5613_ == 0 {
                            v___x_5608_ = v___x_5605_;
                            v_isShared_5609_ = v_isSharedCheck_5613_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5606_);
                            crate::leanh::lean_dec(v___x_5605_);
                            v___x_5608_ = crate::leanh::lean_box(0);
                            v_isShared_5609_ = v_isSharedCheck_5613_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5614_ = crate::leanh::lean_ctor_get(v___x_5605_, 0);
                        crate::leanh::lean_inc(v_a_5614_);
                        crate::leanh::lean_dec_ref_known(v___x_5605_, 1);
                        v_sz_5615_ = lean_array_size(v_a_5614_);
                        v___x_5616_ = 0usize;
                        v___x_5617_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoal_dec_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1__spec__0(v_sz_5615_, v___x_5616_, v_a_5614_, v_a_5589_);
                        if crate::leanh::lean_obj_tag(v___x_5617_) == 0 {
                            crate::leanh::lean_dec(v_term_5604_);
                            crate::leanh::lean_dec(v_range_5603_);
                            crate::leanh::lean_dec(v_ctx_5602_);
                            crate::leanh::lean_dec(v_type_5601_);
                            v_a_5618_ = crate::leanh::lean_ctor_get(v___x_5617_, 0);
                            v_isSharedCheck_5625_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5617_)) as u8;
                            if v_isSharedCheck_5625_ == 0 {
                                v___x_5620_ = v___x_5617_;
                                v_isShared_5621_ = v_isSharedCheck_5625_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5618_);
                                crate::leanh::lean_dec(v___x_5617_);
                                v___x_5620_ = crate::leanh::lean_box(0);
                                v_isShared_5621_ = v_isSharedCheck_5625_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v_a_5626_ = crate::leanh::lean_ctor_get(v___x_5617_, 0);
                            crate::leanh::lean_inc(v_a_5626_);
                            crate::leanh::lean_dec_ref_known(v___x_5617_, 1);
                            v___x_5627_ = l_Lean_Widget_instFromJsonTaggedText_fromJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__4(v_type_5601_);
                            if crate::leanh::lean_obj_tag(v___x_5627_) == 0 {
                                crate::leanh::lean_dec(v_a_5626_);
                                crate::leanh::lean_dec(v_term_5604_);
                                crate::leanh::lean_dec(v_range_5603_);
                                crate::leanh::lean_dec(v_ctx_5602_);
                                v_a_5628_ = crate::leanh::lean_ctor_get(v___x_5627_, 0);
                                v_isSharedCheck_5635_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5627_)) as u8;
                                if v_isSharedCheck_5635_ == 0 {
                                    v___x_5630_ = v___x_5627_;
                                    v_isShared_5631_ = v_isSharedCheck_5635_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5628_);
                                    crate::leanh::lean_dec(v___x_5627_);
                                    v___x_5630_ = crate::leanh::lean_box(0);
                                    v_isShared_5631_ = v_isSharedCheck_5635_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_5636_ = crate::leanh::lean_ctor_get(v___x_5627_, 0);
                                crate::leanh::lean_inc(v_a_5636_);
                                crate::leanh::lean_dec_ref_known(v___x_5627_, 1);
                                v___x_5637_ = l_Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec___closed__0_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1_;
                                v___x_5638_ = l_Lean_Widget_TaggedText_mapM___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__5___redArg(v___x_5637_, v_a_5636_, v_a_5589_);
                                if crate::leanh::lean_obj_tag(v___x_5638_) == 0 {
                                    crate::leanh::lean_dec(v_a_5626_);
                                    crate::leanh::lean_dec(v_term_5604_);
                                    crate::leanh::lean_dec(v_range_5603_);
                                    crate::leanh::lean_dec(v_ctx_5602_);
                                    v_a_5639_ = crate::leanh::lean_ctor_get(v___x_5638_, 0);
                                    v_isSharedCheck_5646_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5638_)) as u8;
                                    if v_isSharedCheck_5646_ == 0 {
                                        v___x_5641_ = v___x_5638_;
                                        v_isShared_5642_ = v_isSharedCheck_5646_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5639_);
                                        crate::leanh::lean_dec(v___x_5638_);
                                        v___x_5641_ = crate::leanh::lean_box(0);
                                        v_isShared_5642_ = v_isSharedCheck_5646_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    v_a_5647_ = crate::leanh::lean_ctor_get(v___x_5638_, 0);
                                    crate::leanh::lean_inc(v_a_5647_);
                                    crate::leanh::lean_dec_ref_known(v___x_5638_, 1);
                                    v___x_5648_ = l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_2318528980____hygCtx___hyg_3_;
                                    v___x_5649_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(v___x_5648_, v_ctx_5602_, v_a_5589_);
                                    if crate::leanh::lean_obj_tag(v___x_5649_) == 0 {
                                        crate::leanh::lean_dec(v_a_5647_);
                                        crate::leanh::lean_dec(v_a_5626_);
                                        crate::leanh::lean_dec(v_term_5604_);
                                        crate::leanh::lean_dec(v_range_5603_);
                                        v_a_5650_ = crate::leanh::lean_ctor_get(v___x_5649_, 0);
                                        v_isSharedCheck_5657_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5649_)) as u8;
                                        if v_isSharedCheck_5657_ == 0 {
                                            v___x_5652_ = v___x_5649_;
                                            v_isShared_5653_ = v_isSharedCheck_5657_;
                                            state = 11;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5650_);
                                            crate::leanh::lean_dec(v___x_5649_);
                                            v___x_5652_ = crate::leanh::lean_box(0);
                                            v_isShared_5653_ = v_isSharedCheck_5657_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_5658_ = crate::leanh::lean_ctor_get(v___x_5649_, 0);
                                        crate::leanh::lean_inc(v_a_5658_);
                                        crate::leanh::lean_dec_ref_known(v___x_5649_, 1);
                                        v___x_5659_ =
                                            l_Lean_Lsp_instFromJsonRange_fromJson(v_range_5603_);
                                        if crate::leanh::lean_obj_tag(v___x_5659_) == 0 {
                                            crate::leanh::lean_dec(v_a_5658_);
                                            crate::leanh::lean_dec(v_a_5647_);
                                            crate::leanh::lean_dec(v_a_5626_);
                                            crate::leanh::lean_dec(v_term_5604_);
                                            v_a_5660_ = crate::leanh::lean_ctor_get(v___x_5659_, 0);
                                            v_isSharedCheck_5667_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_5659_))
                                                    as u8;
                                            if v_isSharedCheck_5667_ == 0 {
                                                v___x_5662_ = v___x_5659_;
                                                v_isShared_5663_ = v_isSharedCheck_5667_;
                                                state = 13;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_5660_);
                                                crate::leanh::lean_dec(v___x_5659_);
                                                v___x_5662_ = crate::leanh::lean_box(0);
                                                v_isShared_5663_ = v_isSharedCheck_5667_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            v_a_5668_ = crate::leanh::lean_ctor_get(v___x_5659_, 0);
                                            crate::leanh::lean_inc(v_a_5668_);
                                            crate::leanh::lean_dec_ref_known(v___x_5659_, 1);
                                            v___x_5669_ = l_Lean_Widget_instImpl_00___x40_Lean_Widget_Basic_173954553____hygCtx___hyg_3_;
                                            v___x_5670_ = l_Lean_Server_instRpcEncodableWithRpcRefOfTypeName_rpcDecode___redArg(v___x_5669_, v_term_5604_, v_a_5589_);
                                            if crate::leanh::lean_obj_tag(v___x_5670_) == 0 {
                                                crate::leanh::lean_dec(v_a_5668_);
                                                crate::leanh::lean_dec(v_a_5658_);
                                                crate::leanh::lean_dec(v_a_5647_);
                                                crate::leanh::lean_dec(v_a_5626_);
                                                v_a_5671_ =
                                                    crate::leanh::lean_ctor_get(v___x_5670_, 0);
                                                v_isSharedCheck_5678_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_5670_))
                                                        as u8;
                                                if v_isSharedCheck_5678_ == 0 {
                                                    v___x_5673_ = v___x_5670_;
                                                    v_isShared_5674_ = v_isSharedCheck_5678_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_5671_);
                                                    crate::leanh::lean_dec(v___x_5670_);
                                                    v___x_5673_ = crate::leanh::lean_box(0);
                                                    v_isShared_5674_ = v_isSharedCheck_5678_;
                                                    state = 15;
                                                    continue;
                                                }
                                            } else {
                                                v_a_5679_ =
                                                    crate::leanh::lean_ctor_get(v___x_5670_, 0);
                                                v_isSharedCheck_5688_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_5670_))
                                                        as u8;
                                                if v_isSharedCheck_5688_ == 0 {
                                                    v___x_5681_ = v___x_5670_;
                                                    v_isShared_5682_ = v_isSharedCheck_5688_;
                                                    state = 17;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_5679_);
                                                    crate::leanh::lean_dec(v___x_5670_);
                                                    v___x_5681_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5597_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5597_, 0, v_a_5591_);
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
                    v_reuseFailAlloc_5612_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5612_, 0, v_a_5606_);
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
                    v_reuseFailAlloc_5624_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5624_, 0, v_a_5618_);
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
                    v_reuseFailAlloc_5634_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5634_, 0, v_a_5628_);
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
                    v_reuseFailAlloc_5645_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5645_, 0, v_a_5639_);
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
                    v_reuseFailAlloc_5656_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5656_, 0, v_a_5650_);
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
                    v_reuseFailAlloc_5666_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5666_, 0, v_a_5660_);
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
                    v_reuseFailAlloc_5677_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5677_, 0, v_a_5671_);
                    v___x_5676_ = v_reuseFailAlloc_5677_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5676_;
            }
            17 => {
                v___x_5683_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5683_, 0, v_a_5626_);
                crate::leanh::lean_ctor_set(v___x_5683_, 1, v_a_5647_);
                crate::leanh::lean_ctor_set(v___x_5683_, 2, v_a_5658_);
                v___x_5684_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5684_, 0, v___x_5683_);
                crate::leanh::lean_ctor_set(v___x_5684_, 1, v_a_5668_);
                crate::leanh::lean_ctor_set(v___x_5684_, 2, v_a_5679_);
                if v_isShared_5682_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5681_, 0, v___x_5684_);
                    v___x_5686_ = v___x_5681_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5687_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5687_, 0, v___x_5684_);
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
    mut v_j_5689_: *mut crate::leanh::LeanObject,
    mut v_a_5690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5691_ = l_Lean_Widget_instRpcEncodableInteractiveTermGoal_dec_00___x40_Lean_Widget_InteractiveGoal_2553565095____hygCtx___hyg_1_(v_j_5689_, v_a_5690_);
    crate::leanh::lean_dec_ref(v_a_5690_);
    return v_res_5691_;
}
pub unsafe fn l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_InteractiveGoalCore_pretty_addLine(
    mut v_fmt_5698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5699_: u8 = 0;
    v___x_5699_ = l_Std_Format_isNil(v_fmt_5698_);
    if v___x_5699_ == 0 {
        let mut v___x_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5700_ = crate::leanh::lean_box(1);
        v___x_5701_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5701_, 0, v_fmt_5698_);
        crate::leanh::lean_ctor_set(v___x_5701_, 1, v___x_5700_);
        return v___x_5701_;
    } else {
        return v_fmt_5698_;
    }
}
pub unsafe fn _init_l_List_filterTR_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5702_: u8 = 0;
    let mut v___x_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5702_ = 1;
    v___x_5703_ = crate::leanh::lean_box(0);
    v___x_5704_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_5703_, v___x_5702_);
    return v___x_5704_;
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__0(
    mut v_a_5705_: *mut crate::leanh::LeanObject,
    mut v_a_5706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5712_: u8 = 0;
    let mut v___x_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: u8 = 0;
    let mut v___x_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5720_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_5705_) == 0 {
                    v___x_5707_ = l_List_reverse___redArg(v_a_5706_);
                    return v___x_5707_;
                } else {
                    v_head_5708_ = crate::leanh::lean_ctor_get(v_a_5705_, 0);
                    v_tail_5709_ = crate::leanh::lean_ctor_get(v_a_5705_, 1);
                    v_isSharedCheck_5720_ = (!crate::leanh::lean_is_exclusive(v_a_5705_)) as u8;
                    if v_isSharedCheck_5720_ == 0 {
                        v___x_5711_ = v_a_5705_;
                        v_isShared_5712_ = v_isSharedCheck_5720_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5709_);
                        crate::leanh::lean_inc(v_head_5708_);
                        crate::leanh::lean_dec(v_a_5705_);
                        v___x_5711_ = crate::leanh::lean_box(0);
                        v_isShared_5712_ = v_isSharedCheck_5720_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5713_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_filterTR_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__0___closed__0), core::ptr::addr_of_mut!(l_List_filterTR_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__0___closed__0_once), _init_l_List_filterTR_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__0___closed__0);
                v___x_5714_ = lean_string_dec_eq(v_head_5708_, v___x_5713_);
                if v___x_5714_ == 0 {
                    if v_isShared_5712_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5711_, 1, v_a_5706_);
                        v___x_5716_ = v___x_5711_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5718_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5718_, 0, v_head_5708_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5718_, 1, v_a_5706_);
                        v___x_5716_ = v_reuseFailAlloc_5718_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5711_);
                    crate::leanh::lean_dec(v_head_5708_);
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indent_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5721_ = crate::leanh::lean_unsigned_to_nat(2);
    v_indent_5722_ = lean_nat_to_int(v___x_5721_);
    return v_indent_5722_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1(
    mut v_as_5737_: *mut crate::leanh::LeanObject,
    mut v_sz_5738_: usize,
    mut v_i_5739_: usize,
    mut v_b_5740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: usize = 0;
    let mut v___x_5744_: usize = 0;
    let mut v___x_5746_: u8 = 0;
    let mut v_a_5747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_names_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_x3f_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indent_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: u8 = 0;
    let mut v___x_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: u8 = 0;
    let mut v___x_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5775_: u8 = 0;
    let mut v___x_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: u8 = 0;
    let mut v___x_5792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5795_: u8 = 0;
    let mut v___x_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: u8 = 0;
    let mut v___x_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5746_ = lean_usize_dec_lt(v_i_5739_, v_sz_5738_);
                if v___x_5746_ == 0 {
                    return v_b_5740_;
                } else {
                    v_a_5747_ = lean_array_uget_borrowed(v_as_5737_, v_i_5739_);
                    v_names_5748_ = crate::leanh::lean_ctor_get(v_a_5747_, 0);
                    v_type_5749_ = crate::leanh::lean_ctor_get(v_a_5747_, 2);
                    v_val_x3f_5750_ = crate::leanh::lean_ctor_get(v_a_5747_, 3);
                    crate::leanh::lean_inc(v_val_x3f_5750_);
                    v_indent_5751_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__0);
                    v___x_5752_ = l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_InteractiveGoalCore_pretty_addLine(v_b_5740_);
                    v___x_5753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__1;
                    crate::leanh::lean_inc_ref(v_names_5748_);
                    v___x_5754_ = lean_array_to_list(v_names_5748_);
                    v___x_5755_ = crate::leanh::lean_box(0);
                    v___x_5756_ = l_List_filterTR_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__0(v___x_5754_, v___x_5755_);
                    v___x_5757_ = l_String_intercalate(v___x_5753_, v___x_5756_);
                    v___x_5758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__2;
                    v___x_5759_ = lean_string_dec_eq(v___x_5757_, v___x_5758_);
                    if v___x_5759_ == 0 {
                        if crate::leanh::lean_obj_tag(v_val_x3f_5750_) == 0 {
                            v___x_5760_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5760_, 0, v___x_5757_);
                            v___x_5761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__4;
                            v___x_5762_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5762_, 0, v___x_5760_);
                            crate::leanh::lean_ctor_set(v___x_5762_, 1, v___x_5761_);
                            v___x_5763_ = crate::leanh::lean_box(1);
                            crate::leanh::lean_inc_ref(v_type_5749_);
                            v___x_5764_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_type_5749_);
                            v___x_5765_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5765_, 0, v___x_5764_);
                            v___x_5766_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5766_, 0, v___x_5763_);
                            crate::leanh::lean_ctor_set(v___x_5766_, 1, v___x_5765_);
                            v___x_5767_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5767_, 0, v_indent_5751_);
                            crate::leanh::lean_ctor_set(v___x_5767_, 1, v___x_5766_);
                            v___x_5768_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5768_, 0, v___x_5762_);
                            crate::leanh::lean_ctor_set(v___x_5768_, 1, v___x_5767_);
                            v___x_5769_ = 0;
                            v___x_5770_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_5770_, 0, v___x_5768_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_5770_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                                v___x_5769_,
                            );
                            v___x_5771_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5771_, 0, v___x_5752_);
                            crate::leanh::lean_ctor_set(v___x_5771_, 1, v___x_5770_);
                            v_a_5742_ = v___x_5771_;
                            state = 1;
                            continue;
                        } else {
                            v_val_5772_ = crate::leanh::lean_ctor_get(v_val_x3f_5750_, 0);
                            v_isSharedCheck_5795_ =
                                (!crate::leanh::lean_is_exclusive(v_val_x3f_5750_)) as u8;
                            if v_isSharedCheck_5795_ == 0 {
                                v___x_5774_ = v_val_x3f_5750_;
                                v_isShared_5775_ = v_isSharedCheck_5795_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_5772_);
                                crate::leanh::lean_dec(v_val_x3f_5750_);
                                v___x_5774_ = crate::leanh::lean_box(0);
                                v_isShared_5775_ = v_isSharedCheck_5795_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_5757_);
                        crate::leanh::lean_dec(v_val_x3f_5750_);
                        v___x_5796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__10;
                        v___x_5797_ = crate::leanh::lean_box(1);
                        crate::leanh::lean_inc_ref(v_type_5749_);
                        v___x_5798_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_type_5749_);
                        v___x_5799_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5799_, 0, v___x_5798_);
                        v___x_5800_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5800_, 0, v___x_5797_);
                        crate::leanh::lean_ctor_set(v___x_5800_, 1, v___x_5799_);
                        v___x_5801_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5801_, 0, v_indent_5751_);
                        crate::leanh::lean_ctor_set(v___x_5801_, 1, v___x_5800_);
                        v___x_5802_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5802_, 0, v___x_5796_);
                        crate::leanh::lean_ctor_set(v___x_5802_, 1, v___x_5801_);
                        v___x_5803_ = 0;
                        v___x_5804_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_5804_, 0, v___x_5802_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_5804_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_5803_,
                        );
                        v___x_5805_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5805_, 0, v___x_5752_);
                        crate::leanh::lean_ctor_set(v___x_5805_, 1, v___x_5804_);
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
                    crate::leanh::lean_ctor_set_tag(v___x_5774_, 3);
                    crate::leanh::lean_ctor_set(v___x_5774_, 0, v___x_5757_);
                    v___x_5777_ = v___x_5774_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5794_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5794_, 0, v___x_5757_);
                    v___x_5777_ = v_reuseFailAlloc_5794_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__6;
                v___x_5779_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5779_, 0, v___x_5777_);
                crate::leanh::lean_ctor_set(v___x_5779_, 1, v___x_5778_);
                crate::leanh::lean_inc_ref(v_type_5749_);
                v___x_5780_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_type_5749_);
                v___x_5781_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5781_, 0, v___x_5780_);
                v___x_5782_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5782_, 0, v___x_5779_);
                crate::leanh::lean_ctor_set(v___x_5782_, 1, v___x_5781_);
                v___x_5783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__8;
                v___x_5784_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5784_, 0, v___x_5782_);
                crate::leanh::lean_ctor_set(v___x_5784_, 1, v___x_5783_);
                v___x_5785_ = crate::leanh::lean_box(1);
                v___x_5786_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_val_5772_);
                v___x_5787_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5787_, 0, v___x_5786_);
                v___x_5788_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5788_, 0, v___x_5785_);
                crate::leanh::lean_ctor_set(v___x_5788_, 1, v___x_5787_);
                v___x_5789_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5789_, 0, v_indent_5751_);
                crate::leanh::lean_ctor_set(v___x_5789_, 1, v___x_5788_);
                v___x_5790_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5790_, 0, v___x_5784_);
                crate::leanh::lean_ctor_set(v___x_5790_, 1, v___x_5789_);
                v___x_5791_ = 0;
                v___x_5792_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5792_, 0, v___x_5790_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5792_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5791_,
                );
                v___x_5793_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5793_, 0, v___x_5752_);
                crate::leanh::lean_ctor_set(v___x_5793_, 1, v___x_5792_);
                v_a_5742_ = v___x_5793_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___boxed(
    mut v_as_5806_: *mut crate::leanh::LeanObject,
    mut v_sz_5807_: *mut crate::leanh::LeanObject,
    mut v_i_5808_: *mut crate::leanh::LeanObject,
    mut v_b_5809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5810_: usize = 0;
    let mut v_i_boxed_5811_: usize = 0;
    let mut v_res_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5810_ = crate::leanh::lean_unbox_usize(v_sz_5807_);
    crate::leanh::lean_dec(v_sz_5807_);
    v_i_boxed_5811_ = crate::leanh::lean_unbox_usize(v_i_5808_);
    crate::leanh::lean_dec(v_i_5808_);
    v_res_5812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1(v_as_5806_, v_sz_boxed_5810_, v_i_boxed_5811_, v_b_5809_);
    crate::leanh::lean_dec_ref(v_as_5806_);
    return v_res_5812_;
}
pub unsafe fn l_Lean_Widget_InteractiveGoalCore_pretty(
    mut v_g_5816_: *mut crate::leanh::LeanObject,
    mut v_userName_x3f_5817_: *mut crate::leanh::LeanObject,
    mut v_goalPrefix_5818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_indent_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5824_: usize = 0;
    let mut v___x_5825_: usize = 0;
    let mut v___x_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5838_: u8 = 0;
    let mut v___x_5839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5844_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_indent_5819_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1___closed__0);
                if crate::leanh::lean_obj_tag(v_userName_x3f_5817_) == 0 {
                    v___x_5834_ = crate::leanh::lean_box(0);
                    v___y_5821_ = v___x_5834_;
                    state = 1;
                    continue;
                } else {
                    v_val_5835_ = crate::leanh::lean_ctor_get(v_userName_x3f_5817_, 0);
                    v_isSharedCheck_5844_ =
                        (!crate::leanh::lean_is_exclusive(v_userName_x3f_5817_)) as u8;
                    if v_isSharedCheck_5844_ == 0 {
                        v___x_5837_ = v_userName_x3f_5817_;
                        v_isShared_5838_ = v_isSharedCheck_5844_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5835_);
                        crate::leanh::lean_dec(v_userName_x3f_5817_);
                        v___x_5837_ = crate::leanh::lean_box(0);
                        v_isShared_5838_ = v_isSharedCheck_5844_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v_hyps_5822_ = crate::leanh::lean_ctor_get(v_g_5816_, 0);
                crate::leanh::lean_inc_ref(v_hyps_5822_);
                v_type_5823_ = crate::leanh::lean_ctor_get(v_g_5816_, 1);
                crate::leanh::lean_inc_ref(v_type_5823_);
                crate::leanh::lean_dec_ref(v_g_5816_);
                v_sz_5824_ = lean_array_size(v_hyps_5822_);
                v___x_5825_ = 0usize;
                v___x_5826_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Widget_InteractiveGoalCore_pretty_spec__1(v_hyps_5822_, v_sz_5824_, v___x_5825_, v___y_5821_);
                crate::leanh::lean_dec_ref(v_hyps_5822_);
                v___x_5827_ = l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_InteractiveGoalCore_pretty_addLine(v___x_5826_);
                v___x_5828_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5828_, 0, v_goalPrefix_5818_);
                v___x_5829_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_type_5823_);
                v___x_5830_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5830_, 0, v___x_5829_);
                v___x_5831_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5831_, 0, v_indent_5819_);
                crate::leanh::lean_ctor_set(v___x_5831_, 1, v___x_5830_);
                v___x_5832_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5832_, 0, v___x_5828_);
                crate::leanh::lean_ctor_set(v___x_5832_, 1, v___x_5831_);
                v___x_5833_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5833_, 0, v___x_5827_);
                crate::leanh::lean_ctor_set(v___x_5833_, 1, v___x_5832_);
                return v___x_5833_;
            }
            2 => {
                v___x_5839_ = l_Lean_Widget_InteractiveGoalCore_pretty___closed__1;
                if v_isShared_5838_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5837_, 3);
                    v___x_5841_ = v___x_5837_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5843_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5843_, 0, v_val_5835_);
                    v___x_5841_ = v_reuseFailAlloc_5843_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5842_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5842_, 0, v___x_5839_);
                crate::leanh::lean_ctor_set(v___x_5842_, 1, v___x_5841_);
                v___y_5821_ = v___x_5842_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_InteractiveGoal_pretty(
    mut v_g_5845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toInteractiveGoalCore_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_x3f_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_goalPrefix_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toInteractiveGoalCore_5846_ = crate::leanh::lean_ctor_get(v_g_5845_, 0);
    crate::leanh::lean_inc_ref(v_toInteractiveGoalCore_5846_);
    v_userName_x3f_5847_ = crate::leanh::lean_ctor_get(v_g_5845_, 1);
    crate::leanh::lean_inc(v_userName_x3f_5847_);
    v_goalPrefix_5848_ = crate::leanh::lean_ctor_get(v_g_5845_, 2);
    crate::leanh::lean_inc_ref(v_goalPrefix_5848_);
    crate::leanh::lean_dec_ref(v_g_5845_);
    v___x_5849_ = l_Lean_Widget_InteractiveGoalCore_pretty(
        v_toInteractiveGoalCore_5846_,
        v_userName_x3f_5847_,
        v_goalPrefix_5848_,
    );
    return v___x_5849_;
}
pub unsafe fn l_Lean_Widget_InteractiveTermGoal_pretty(
    mut v_g_5851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toInteractiveGoalCore_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toInteractiveGoalCore_5852_ = crate::leanh::lean_ctor_get(v_g_5851_, 0);
    crate::leanh::lean_inc_ref(v_toInteractiveGoalCore_5852_);
    crate::leanh::lean_dec_ref(v_g_5851_);
    v___x_5853_ = crate::leanh::lean_box(0);
    v___x_5854_ = l_Lean_Widget_InteractiveTermGoal_pretty___closed__0;
    v___x_5855_ = l_Lean_Widget_InteractiveGoalCore_pretty(
        v_toInteractiveGoalCore_5852_,
        v___x_5853_,
        v___x_5854_,
    );
    return v___x_5855_;
}
pub unsafe fn l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10_(
    mut v_json_5857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5863_: u8 = 0;
    let mut v___x_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5858_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10_;
                v___x_5859_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_29__spec__0(v_json_5857_, v___x_5858_);
                v_a_5860_ = crate::leanh::lean_ctor_get(v___x_5859_, 0);
                v_isSharedCheck_5867_ = (!crate::leanh::lean_is_exclusive(v___x_5859_)) as u8;
                if v_isSharedCheck_5867_ == 0 {
                    v___x_5862_ = v___x_5859_;
                    v_isShared_5863_ = v_isSharedCheck_5867_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5860_);
                    crate::leanh::lean_dec(v___x_5859_);
                    v___x_5862_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5866_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5866_, 0, v_a_5860_);
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
    mut v_x_5870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5871_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10_;
    v___x_5872_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5872_, 0, v___x_5871_);
    crate::leanh::lean_ctor_set(v___x_5872_, 1, v_x_5870_);
    v___x_5873_ = crate::leanh::lean_box(0);
    v___x_5874_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5874_, 0, v___x_5872_);
    crate::leanh::lean_ctor_set(v___x_5874_, 1, v___x_5873_);
    v___x_5875_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5875_, 0, v___x_5874_);
    crate::leanh::lean_ctor_set(v___x_5875_, 1, v___x_5873_);
    v___x_5876_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47_;
    v___x_5877_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_1924226853____hygCtx___hyg_47__spec__1(v___x_5875_, v___x_5876_);
    v___x_5878_ = l_Lean_Json_mkObj(v___x_5877_);
    crate::leanh::lean_dec(v___x_5877_);
    return v___x_5878_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoals_enc_00___x40_Lean_Widget_InteractiveGoal_1490754142____hygCtx___hyg_1__spec__0(
    mut v_sz_5881_: usize,
    mut v_i_5882_: usize,
    mut v_bs_5883_: *mut crate::leanh::LeanObject,
    mut v___y_5884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5885_: u8 = 0;
    let mut v___x_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: usize = 0;
    let mut v___x_5894_: usize = 0;
    let mut v___x_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5885_ = lean_usize_dec_lt(v_i_5882_, v_sz_5881_);
                if v___x_5885_ == 0 {
                    v___x_5886_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5886_, 0, v_bs_5883_);
                    crate::leanh::lean_ctor_set(v___x_5886_, 1, v___y_5884_);
                    return v___x_5886_;
                } else {
                    v_v_5887_ = lean_array_uget_borrowed(v_bs_5883_, v_i_5882_);
                    crate::leanh::lean_inc(v_v_5887_);
                    v___x_5888_ = l_Lean_Widget_instRpcEncodableInteractiveGoal_enc_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1_(v_v_5887_, v___y_5884_);
                    v_fst_5889_ = crate::leanh::lean_ctor_get(v___x_5888_, 0);
                    crate::leanh::lean_inc(v_fst_5889_);
                    v_snd_5890_ = crate::leanh::lean_ctor_get(v___x_5888_, 1);
                    crate::leanh::lean_inc(v_snd_5890_);
                    crate::leanh::lean_dec_ref(v___x_5888_);
                    v___x_5891_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_5897_: *mut crate::leanh::LeanObject,
    mut v_i_5898_: *mut crate::leanh::LeanObject,
    mut v_bs_5899_: *mut crate::leanh::LeanObject,
    mut v___y_5900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5901_: usize = 0;
    let mut v_i_boxed_5902_: usize = 0;
    let mut v_res_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5901_ = crate::leanh::lean_unbox_usize(v_sz_5897_);
    crate::leanh::lean_dec(v_sz_5897_);
    v_i_boxed_5902_ = crate::leanh::lean_unbox_usize(v_i_5898_);
    crate::leanh::lean_dec(v_i_5898_);
    v_res_5903_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoals_enc_00___x40_Lean_Widget_InteractiveGoal_1490754142____hygCtx___hyg_1__spec__0(v_sz_boxed_5901_, v_i_boxed_5902_, v_bs_5899_, v___y_5900_);
    return v_res_5903_;
}
pub unsafe fn l_Lean_Widget_instRpcEncodableInteractiveGoals_enc_00___x40_Lean_Widget_InteractiveGoal_1490754142____hygCtx___hyg_1_(
    mut v_a_5904_: *mut crate::leanh::LeanObject,
    mut v_a_5905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_5906_: usize = 0;
    let mut v___x_5907_: usize = 0;
    let mut v___x_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5913_: u8 = 0;
    let mut v___x_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5919_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_5906_ = lean_array_size(v_a_5904_);
                v___x_5907_ = 0usize;
                v___x_5908_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoals_enc_00___x40_Lean_Widget_InteractiveGoal_1490754142____hygCtx___hyg_1__spec__0(v_sz_5906_, v___x_5907_, v_a_5904_, v_a_5905_);
                v_fst_5909_ = crate::leanh::lean_ctor_get(v___x_5908_, 0);
                v_snd_5910_ = crate::leanh::lean_ctor_get(v___x_5908_, 1);
                v_isSharedCheck_5919_ = (!crate::leanh::lean_is_exclusive(v___x_5908_)) as u8;
                if v_isSharedCheck_5919_ == 0 {
                    v___x_5912_ = v___x_5908_;
                    v_isShared_5913_ = v_isSharedCheck_5919_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5910_);
                    crate::leanh::lean_inc(v_fst_5909_);
                    crate::leanh::lean_dec(v___x_5908_);
                    v___x_5912_ = crate::leanh::lean_box(0);
                    v_isShared_5913_ = v_isSharedCheck_5919_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5914_ = l_Array_toJson___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_enc_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__3(v_fst_5909_);
                v___x_5915_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_28_(v___x_5914_);
                if v_isShared_5913_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5912_, 0, v___x_5915_);
                    v___x_5917_ = v___x_5912_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5918_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5918_, 0, v___x_5915_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5918_, 1, v_snd_5910_);
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
    mut v_bs_5922_: *mut crate::leanh::LeanObject,
    mut v___y_5923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5924_: u8 = 0;
    let mut v___x_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5931_: u8 = 0;
    let mut v___x_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5935_: u8 = 0;
    let mut v_a_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: usize = 0;
    let mut v___x_5940_: usize = 0;
    let mut v___x_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5924_ = lean_usize_dec_lt(v_i_5921_, v_sz_5920_);
                if v___x_5924_ == 0 {
                    v___x_5925_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5925_, 0, v_bs_5922_);
                    return v___x_5925_;
                } else {
                    v_v_5926_ = lean_array_uget_borrowed(v_bs_5922_, v_i_5921_);
                    crate::leanh::lean_inc(v_v_5926_);
                    v___x_5927_ = l_Lean_Widget_instRpcEncodableInteractiveGoal_dec_00___x40_Lean_Widget_InteractiveGoal_3114798910____hygCtx___hyg_1_(v_v_5926_, v___y_5923_);
                    if crate::leanh::lean_obj_tag(v___x_5927_) == 0 {
                        crate::leanh::lean_dec_ref(v_bs_5922_);
                        v_a_5928_ = crate::leanh::lean_ctor_get(v___x_5927_, 0);
                        v_isSharedCheck_5935_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5927_)) as u8;
                        if v_isSharedCheck_5935_ == 0 {
                            v___x_5930_ = v___x_5927_;
                            v_isShared_5931_ = v_isSharedCheck_5935_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5928_);
                            crate::leanh::lean_dec(v___x_5927_);
                            v___x_5930_ = crate::leanh::lean_box(0);
                            v_isShared_5931_ = v_isSharedCheck_5935_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5936_ = crate::leanh::lean_ctor_get(v___x_5927_, 0);
                        crate::leanh::lean_inc(v_a_5936_);
                        crate::leanh::lean_dec_ref_known(v___x_5927_, 1);
                        v___x_5937_ = crate::leanh::lean_unsigned_to_nat(0);
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
                    v_reuseFailAlloc_5934_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5934_, 0, v_a_5928_);
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
    mut v_sz_5943_: *mut crate::leanh::LeanObject,
    mut v_i_5944_: *mut crate::leanh::LeanObject,
    mut v_bs_5945_: *mut crate::leanh::LeanObject,
    mut v___y_5946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5947_: usize = 0;
    let mut v_i_boxed_5948_: usize = 0;
    let mut v_res_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5947_ = crate::leanh::lean_unbox_usize(v_sz_5943_);
    crate::leanh::lean_dec(v_sz_5943_);
    v_i_boxed_5948_ = crate::leanh::lean_unbox_usize(v_i_5944_);
    crate::leanh::lean_dec(v_i_5944_);
    v_res_5949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoals_dec_00___x40_Lean_Widget_InteractiveGoal_1490754142____hygCtx___hyg_1__spec__0(v_sz_boxed_5947_, v_i_boxed_5948_, v_bs_5945_, v___y_5946_);
    crate::leanh::lean_dec_ref(v___y_5946_);
    return v_res_5949_;
}
pub unsafe fn l_Lean_Widget_instRpcEncodableInteractiveGoals_dec_00___x40_Lean_Widget_InteractiveGoal_1490754142____hygCtx___hyg_1_(
    mut v_j_5950_: *mut crate::leanh::LeanObject,
    mut v_a_5951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5956_: u8 = 0;
    let mut v___x_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5960_: u8 = 0;
    let mut v_a_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5966_: u8 = 0;
    let mut v___x_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5970_: u8 = 0;
    let mut v_a_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5972_: usize = 0;
    let mut v___x_5973_: usize = 0;
    let mut v___x_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5978_: u8 = 0;
    let mut v___x_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5982_: u8 = 0;
    let mut v_a_5983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5986_: u8 = 0;
    let mut v___x_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5990_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5952_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_InteractiveGoal_2032952811____hygCtx___hyg_10_(v_j_5950_);
                if crate::leanh::lean_obj_tag(v___x_5952_) == 0 {
                    v_a_5953_ = crate::leanh::lean_ctor_get(v___x_5952_, 0);
                    v_isSharedCheck_5960_ = (!crate::leanh::lean_is_exclusive(v___x_5952_)) as u8;
                    if v_isSharedCheck_5960_ == 0 {
                        v___x_5955_ = v___x_5952_;
                        v_isShared_5956_ = v_isSharedCheck_5960_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5953_);
                        crate::leanh::lean_dec(v___x_5952_);
                        v___x_5955_ = crate::leanh::lean_box(0);
                        v_isShared_5956_ = v_isSharedCheck_5960_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5961_ = crate::leanh::lean_ctor_get(v___x_5952_, 0);
                    crate::leanh::lean_inc(v_a_5961_);
                    crate::leanh::lean_dec_ref_known(v___x_5952_, 1);
                    v___x_5962_ = l_Array_fromJson_x3f___at___00Lean_Widget_instRpcEncodableInteractiveHypothesisBundle_dec_00___x40_Lean_Widget_InteractiveGoal_562241082____hygCtx___hyg_1__spec__0(v_a_5961_);
                    if crate::leanh::lean_obj_tag(v___x_5962_) == 0 {
                        v_a_5963_ = crate::leanh::lean_ctor_get(v___x_5962_, 0);
                        v_isSharedCheck_5970_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5962_)) as u8;
                        if v_isSharedCheck_5970_ == 0 {
                            v___x_5965_ = v___x_5962_;
                            v_isShared_5966_ = v_isSharedCheck_5970_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5963_);
                            crate::leanh::lean_dec(v___x_5962_);
                            v___x_5965_ = crate::leanh::lean_box(0);
                            v_isShared_5966_ = v_isSharedCheck_5970_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5971_ = crate::leanh::lean_ctor_get(v___x_5962_, 0);
                        crate::leanh::lean_inc(v_a_5971_);
                        crate::leanh::lean_dec_ref_known(v___x_5962_, 1);
                        v_sz_5972_ = lean_array_size(v_a_5971_);
                        v___x_5973_ = 0usize;
                        v___x_5974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_instRpcEncodableInteractiveGoals_dec_00___x40_Lean_Widget_InteractiveGoal_1490754142____hygCtx___hyg_1__spec__0(v_sz_5972_, v___x_5973_, v_a_5971_, v_a_5951_);
                        if crate::leanh::lean_obj_tag(v___x_5974_) == 0 {
                            v_a_5975_ = crate::leanh::lean_ctor_get(v___x_5974_, 0);
                            v_isSharedCheck_5982_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5974_)) as u8;
                            if v_isSharedCheck_5982_ == 0 {
                                v___x_5977_ = v___x_5974_;
                                v_isShared_5978_ = v_isSharedCheck_5982_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5975_);
                                crate::leanh::lean_dec(v___x_5974_);
                                v___x_5977_ = crate::leanh::lean_box(0);
                                v_isShared_5978_ = v_isSharedCheck_5982_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v_a_5983_ = crate::leanh::lean_ctor_get(v___x_5974_, 0);
                            v_isSharedCheck_5990_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5974_)) as u8;
                            if v_isSharedCheck_5990_ == 0 {
                                v___x_5985_ = v___x_5974_;
                                v_isShared_5986_ = v_isSharedCheck_5990_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5983_);
                                crate::leanh::lean_dec(v___x_5974_);
                                v___x_5985_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5959_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5959_, 0, v_a_5953_);
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
                    v_reuseFailAlloc_5969_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5969_, 0, v_a_5963_);
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
                    v_reuseFailAlloc_5981_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5981_, 0, v_a_5975_);
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
                    v_reuseFailAlloc_5989_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5989_, 0, v_a_5983_);
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
    mut v_j_5991_: *mut crate::leanh::LeanObject,
    mut v_a_5992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5993_ = l_Lean_Widget_instRpcEncodableInteractiveGoals_dec_00___x40_Lean_Widget_InteractiveGoal_1490754142____hygCtx___hyg_1_(v_j_5991_, v_a_5992_);
    crate::leanh::lean_dec_ref(v_a_5992_);
    return v_res_5993_;
}
pub unsafe fn l_Lean_Widget_InteractiveGoals_append(
    mut v_l_6000_: *mut crate::leanh::LeanObject,
    mut v_r_6001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6002_ = l_Array_append___redArg(v_l_6000_, v_r_6001_);
    return v___x_6002_;
}
pub unsafe fn l_Lean_Widget_InteractiveGoals_append___boxed(
    mut v_l_6003_: *mut crate::leanh::LeanObject,
    mut v_r_6004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6005_ = l_Lean_Widget_InteractiveGoals_append(v_l_6003_, v_r_6004_);
    crate::leanh::lean_dec_ref(v_r_6004_);
    return v_res_6005_;
}
pub unsafe fn l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged(
    mut v_tactic_6014_: u8,
    mut v_value_6015_: *mut crate::leanh::LeanObject,
    mut v_a_6016_: *mut crate::leanh::LeanObject,
    mut v_a_6017_: *mut crate::leanh::LeanObject,
    mut v_a_6018_: *mut crate::leanh::LeanObject,
    mut v_a_6019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: u8 = 0;
    let mut v___x_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6036_: u8 = 0;
    let mut v___x_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                if crate::leanh::lean_obj_tag(v___x_6021_) == 0 {
                    v_a_6022_ = crate::leanh::lean_ctor_get(v___x_6021_, 0);
                    crate::leanh::lean_inc(v_a_6022_);
                    crate::leanh::lean_dec_ref_known(v___x_6021_, 1);
                    v___x_6028_ = (crate::leanh::lean_unbox(v_a_6022_) as u8);
                    crate::leanh::lean_dec(v_a_6022_);
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
                    crate::leanh::lean_dec_ref(v_value_6015_);
                    v_a_6033_ = crate::leanh::lean_ctor_get(v___x_6021_, 0);
                    v_isSharedCheck_6040_ = (!crate::leanh::lean_is_exclusive(v___x_6021_)) as u8;
                    if v_isSharedCheck_6040_ == 0 {
                        v___x_6035_ = v___x_6021_;
                        v_isShared_6036_ = v_isSharedCheck_6040_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6033_);
                        crate::leanh::lean_dec(v___x_6021_);
                        v___x_6035_ = crate::leanh::lean_box(0);
                        v_isShared_6036_ = v_isSharedCheck_6040_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_6024_);
                v___x_6025_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6025_, 0, v___y_6024_);
                v___x_6026_ = crate::leanh::lean_alloc_closure(
                    l_Lean_PrettyPrinter_Delaborator_omission___boxed as *mut core::ffi::c_void,
                    8,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_6026_, 0, v___x_6025_);
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
                    v_reuseFailAlloc_6039_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6039_, 0, v_a_6033_);
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
    mut v_tactic_6041_: *mut crate::leanh::LeanObject,
    mut v_value_6042_: *mut crate::leanh::LeanObject,
    mut v_a_6043_: *mut crate::leanh::LeanObject,
    mut v_a_6044_: *mut crate::leanh::LeanObject,
    mut v_a_6045_: *mut crate::leanh::LeanObject,
    mut v_a_6046_: *mut crate::leanh::LeanObject,
    mut v_a_6047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tactic_boxed_6048_: u8 = 0;
    let mut v_res_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tactic_boxed_6048_ = (crate::leanh::lean_unbox(v_tactic_6041_) as u8);
    v_res_6049_ = l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged(v_tactic_boxed_6048_, v_value_6042_, v_a_6043_, v_a_6044_, v_a_6045_, v_a_6046_);
    crate::leanh::lean_dec(v_a_6046_);
    crate::leanh::lean_dec_ref(v_a_6045_);
    crate::leanh::lean_dec(v_a_6044_);
    crate::leanh::lean_dec_ref(v_a_6043_);
    return v_res_6049_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(
    mut v_e_6050_: *mut crate::leanh::LeanObject,
    mut v___y_6051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6053_: u8 = 0;
    let mut v___x_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6067_: u8 = 0;
    let mut v___x_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6073_: u8 = 0;
    let mut v_unused_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6053_ = l_Lean_Expr_hasMVar(v_e_6050_);
                if v___x_6053_ == 0 {
                    v___x_6054_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6054_, 0, v_e_6050_);
                    return v___x_6054_;
                } else {
                    v___x_6055_ = lean_st_ref_get(v___y_6051_);
                    v_mctx_6056_ = crate::leanh::lean_ctor_get(v___x_6055_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_6056_);
                    crate::leanh::lean_dec(v___x_6055_);
                    v___x_6057_ = l_Lean_instantiateMVarsCore(v_mctx_6056_, v_e_6050_);
                    v_fst_6058_ = crate::leanh::lean_ctor_get(v___x_6057_, 0);
                    crate::leanh::lean_inc(v_fst_6058_);
                    v_snd_6059_ = crate::leanh::lean_ctor_get(v___x_6057_, 1);
                    crate::leanh::lean_inc(v_snd_6059_);
                    crate::leanh::lean_dec_ref(v___x_6057_);
                    v___x_6060_ = lean_st_ref_take(v___y_6051_);
                    v_cache_6061_ = crate::leanh::lean_ctor_get(v___x_6060_, 1);
                    v_zetaDeltaFVarIds_6062_ = crate::leanh::lean_ctor_get(v___x_6060_, 2);
                    v_postponed_6063_ = crate::leanh::lean_ctor_get(v___x_6060_, 3);
                    v_diag_6064_ = crate::leanh::lean_ctor_get(v___x_6060_, 4);
                    v_isSharedCheck_6073_ = (!crate::leanh::lean_is_exclusive(v___x_6060_)) as u8;
                    if v_isSharedCheck_6073_ == 0 {
                        v_unused_6074_ = crate::leanh::lean_ctor_get(v___x_6060_, 0);
                        crate::leanh::lean_dec(v_unused_6074_);
                        v___x_6066_ = v___x_6060_;
                        v_isShared_6067_ = v_isSharedCheck_6073_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_6064_);
                        crate::leanh::lean_inc(v_postponed_6063_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_6062_);
                        crate::leanh::lean_inc(v_cache_6061_);
                        crate::leanh::lean_dec(v___x_6060_);
                        v___x_6066_ = crate::leanh::lean_box(0);
                        v_isShared_6067_ = v_isSharedCheck_6073_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6067_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6066_, 0, v_snd_6059_);
                    v___x_6069_ = v___x_6066_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6072_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6072_, 0, v_snd_6059_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6072_, 1, v_cache_6061_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_6072_,
                        2,
                        v_zetaDeltaFVarIds_6062_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6072_, 3, v_postponed_6063_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6072_, 4, v_diag_6064_);
                    v___x_6069_ = v_reuseFailAlloc_6072_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6070_ = lean_st_ref_set(v___y_6051_, v___x_6069_);
                v___x_6071_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6071_, 0, v_fst_6058_);
                return v___x_6071_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg___boxed(
    mut v_e_6075_: *mut crate::leanh::LeanObject,
    mut v___y_6076_: *mut crate::leanh::LeanObject,
    mut v___y_6077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6078_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_e_6075_, v___y_6076_);
    crate::leanh::lean_dec(v___y_6076_);
    return v_res_6078_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2(
    mut v_e_6079_: *mut crate::leanh::LeanObject,
    mut v___y_6080_: *mut crate::leanh::LeanObject,
    mut v___y_6081_: *mut crate::leanh::LeanObject,
    mut v___y_6082_: *mut crate::leanh::LeanObject,
    mut v___y_6083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6085_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_e_6079_, v___y_6081_);
    return v___x_6085_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___boxed(
    mut v_e_6086_: *mut crate::leanh::LeanObject,
    mut v___y_6087_: *mut crate::leanh::LeanObject,
    mut v___y_6088_: *mut crate::leanh::LeanObject,
    mut v___y_6089_: *mut crate::leanh::LeanObject,
    mut v___y_6090_: *mut crate::leanh::LeanObject,
    mut v___y_6091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6092_ =
        l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2(
            v_e_6086_,
            v___y_6087_,
            v___y_6088_,
            v___y_6089_,
            v___y_6090_,
        );
    crate::leanh::lean_dec(v___y_6090_);
    crate::leanh::lean_dec_ref(v___y_6089_);
    crate::leanh::lean_dec(v___y_6088_);
    crate::leanh::lean_dec_ref(v___y_6087_);
    return v_res_6092_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__0(
    mut v_sz_6093_: usize,
    mut v_i_6094_: usize,
    mut v_bs_6095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6096_: u8 = 0;
    let mut v_v_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: usize = 0;
    let mut v___x_6102_: usize = 0;
    let mut v___x_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6096_ = lean_usize_dec_lt(v_i_6094_, v_sz_6093_);
                if v___x_6096_ == 0 {
                    return v_bs_6095_;
                } else {
                    v_v_6097_ = lean_array_uget_borrowed(v_bs_6095_, v_i_6094_);
                    v_snd_6098_ = crate::leanh::lean_ctor_get(v_v_6097_, 1);
                    crate::leanh::lean_inc(v_snd_6098_);
                    v___x_6099_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_6105_: *mut crate::leanh::LeanObject,
    mut v_i_6106_: *mut crate::leanh::LeanObject,
    mut v_bs_6107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6108_: usize = 0;
    let mut v_i_boxed_6109_: usize = 0;
    let mut v_res_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6108_ = crate::leanh::lean_unbox_usize(v_sz_6105_);
    crate::leanh::lean_dec(v_sz_6105_);
    v_i_boxed_6109_ = crate::leanh::lean_unbox_usize(v_i_6106_);
    crate::leanh::lean_dec(v_i_6106_);
    v_res_6110_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__0(v_sz_boxed_6108_, v_i_boxed_6109_, v_bs_6107_);
    return v_res_6110_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__1(
    mut v_sz_6111_: usize,
    mut v_i_6112_: usize,
    mut v_bs_6113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6114_: u8 = 0;
    let mut v_v_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6119_: usize = 0;
    let mut v___x_6120_: usize = 0;
    let mut v___x_6121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6114_ = lean_usize_dec_lt(v_i_6112_, v_sz_6111_);
                if v___x_6114_ == 0 {
                    return v_bs_6113_;
                } else {
                    v_v_6115_ = lean_array_uget_borrowed(v_bs_6113_, v_i_6112_);
                    v_fst_6116_ = crate::leanh::lean_ctor_get(v_v_6115_, 0);
                    crate::leanh::lean_inc(v_fst_6116_);
                    v___x_6117_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_6123_: *mut crate::leanh::LeanObject,
    mut v_i_6124_: *mut crate::leanh::LeanObject,
    mut v_bs_6125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6126_: usize = 0;
    let mut v_i_boxed_6127_: usize = 0;
    let mut v_res_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6126_ = crate::leanh::lean_unbox_usize(v_sz_6123_);
    crate::leanh::lean_dec(v_sz_6123_);
    v_i_boxed_6127_ = crate::leanh::lean_unbox_usize(v_i_6124_);
    crate::leanh::lean_dec(v_i_6124_);
    v_res_6128_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__1(v_sz_boxed_6126_, v_i_boxed_6127_, v_bs_6125_);
    return v_res_6128_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__3_spec__3(
    mut v_msgData_6129_: *mut crate::leanh::LeanObject,
    mut v___y_6130_: *mut crate::leanh::LeanObject,
    mut v___y_6131_: *mut crate::leanh::LeanObject,
    mut v___y_6132_: *mut crate::leanh::LeanObject,
    mut v___y_6133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6135_ = lean_st_ref_get(v___y_6133_);
    v_env_6136_ = crate::leanh::lean_ctor_get(v___x_6135_, 0);
    crate::leanh::lean_inc_ref(v_env_6136_);
    crate::leanh::lean_dec(v___x_6135_);
    v___x_6137_ = lean_st_ref_get(v___y_6131_);
    v_mctx_6138_ = crate::leanh::lean_ctor_get(v___x_6137_, 0);
    crate::leanh::lean_inc_ref(v_mctx_6138_);
    crate::leanh::lean_dec(v___x_6137_);
    v_lctx_6139_ = crate::leanh::lean_ctor_get(v___y_6130_, 2);
    v_options_6140_ = crate::leanh::lean_ctor_get(v___y_6132_, 2);
    crate::leanh::lean_inc_ref(v_options_6140_);
    crate::leanh::lean_inc_ref(v_lctx_6139_);
    v___x_6141_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6141_, 0, v_env_6136_);
    crate::leanh::lean_ctor_set(v___x_6141_, 1, v_mctx_6138_);
    crate::leanh::lean_ctor_set(v___x_6141_, 2, v_lctx_6139_);
    crate::leanh::lean_ctor_set(v___x_6141_, 3, v_options_6140_);
    v___x_6142_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6142_, 0, v___x_6141_);
    crate::leanh::lean_ctor_set(v___x_6142_, 1, v_msgData_6129_);
    v___x_6143_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6143_, 0, v___x_6142_);
    return v___x_6143_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__3_spec__3___boxed(
    mut v_msgData_6144_: *mut crate::leanh::LeanObject,
    mut v___y_6145_: *mut crate::leanh::LeanObject,
    mut v___y_6146_: *mut crate::leanh::LeanObject,
    mut v___y_6147_: *mut crate::leanh::LeanObject,
    mut v___y_6148_: *mut crate::leanh::LeanObject,
    mut v___y_6149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6150_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__3_spec__3(v_msgData_6144_, v___y_6145_, v___y_6146_, v___y_6147_, v___y_6148_);
    crate::leanh::lean_dec(v___y_6148_);
    crate::leanh::lean_dec_ref(v___y_6147_);
    crate::leanh::lean_dec(v___y_6146_);
    crate::leanh::lean_dec_ref(v___y_6145_);
    return v_res_6150_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__3___redArg(
    mut v_msg_6151_: *mut crate::leanh::LeanObject,
    mut v___y_6152_: *mut crate::leanh::LeanObject,
    mut v___y_6153_: *mut crate::leanh::LeanObject,
    mut v___y_6154_: *mut crate::leanh::LeanObject,
    mut v___y_6155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6162_: u8 = 0;
    let mut v___x_6163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6167_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_6157_ = crate::leanh::lean_ctor_get(v___y_6154_, 5);
                v___x_6158_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__3_spec__3(v_msg_6151_, v___y_6152_, v___y_6153_, v___y_6154_, v___y_6155_);
                v_a_6159_ = crate::leanh::lean_ctor_get(v___x_6158_, 0);
                v_isSharedCheck_6167_ = (!crate::leanh::lean_is_exclusive(v___x_6158_)) as u8;
                if v_isSharedCheck_6167_ == 0 {
                    v___x_6161_ = v___x_6158_;
                    v_isShared_6162_ = v_isSharedCheck_6167_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6159_);
                    crate::leanh::lean_dec(v___x_6158_);
                    v___x_6161_ = crate::leanh::lean_box(0);
                    v_isShared_6162_ = v_isSharedCheck_6167_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_6157_);
                v___x_6163_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6163_, 0, v_ref_6157_);
                crate::leanh::lean_ctor_set(v___x_6163_, 1, v_a_6159_);
                if v_isShared_6162_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6161_, 1);
                    crate::leanh::lean_ctor_set(v___x_6161_, 0, v___x_6163_);
                    v___x_6165_ = v___x_6161_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6166_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6166_, 0, v___x_6163_);
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
    mut v_msg_6168_: *mut crate::leanh::LeanObject,
    mut v___y_6169_: *mut crate::leanh::LeanObject,
    mut v___y_6170_: *mut crate::leanh::LeanObject,
    mut v___y_6171_: *mut crate::leanh::LeanObject,
    mut v___y_6172_: *mut crate::leanh::LeanObject,
    mut v___y_6173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6174_ =
        l_Lean_throwError___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__3___redArg(
            v_msg_6168_,
            v___y_6169_,
            v___y_6170_,
            v___y_6171_,
            v___y_6172_,
        );
    crate::leanh::lean_dec(v___y_6172_);
    crate::leanh::lean_dec_ref(v___y_6171_);
    crate::leanh::lean_dec(v___y_6170_);
    crate::leanh::lean_dec_ref(v___y_6169_);
    return v_res_6174_;
}
pub unsafe fn _init_l_Lean_Widget_addInteractiveHypothesisBundle___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6179_ = l_Lean_Widget_addInteractiveHypothesisBundle___closed__1;
    v___x_6180_ = l_Lean_stringToMessageData(v___x_6179_);
    return v___x_6180_;
}
pub unsafe fn l_Lean_Widget_addInteractiveHypothesisBundle(
    mut v_hyps_6181_: *mut crate::leanh::LeanObject,
    mut v_ids_6182_: *mut crate::leanh::LeanObject,
    mut v_type_6183_: *mut crate::leanh::LeanObject,
    mut v_value_x3f_6184_: *mut crate::leanh::LeanObject,
    mut v_tactic_6185_: u8,
    mut v_a_6186_: *mut crate::leanh::LeanObject,
    mut v_a_6187_: *mut crate::leanh::LeanObject,
    mut v_a_6188_: *mut crate::leanh::LeanObject,
    mut v_a_6189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6204_: u8 = 0;
    let mut v___y_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6210_: u8 = 0;
    let mut v___x_6211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: u8 = 0;
    let mut v___x_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: u8 = 0;
    let mut v___x_6231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6235_: u8 = 0;
    let mut v___x_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6239_: u8 = 0;
    let mut v___y_6241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6248_: usize = 0;
    let mut v___x_6249_: usize = 0;
    let mut v_fvarIds_6250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_names_6251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6256_: u8 = 0;
    let mut v___x_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6265_: u8 = 0;
    let mut v___x_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6269_: u8 = 0;
    let mut v_isSharedCheck_6270_: u8 = 0;
    let mut v_a_6271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6274_: u8 = 0;
    let mut v___x_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6278_: u8 = 0;
    let mut v___x_6279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: u8 = 0;
    let mut v___x_6282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6287_: u8 = 0;
    let mut v___x_6289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6291_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6279_ = lean_array_get_size(v_ids_6182_);
                v___x_6280_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6281_ = lean_nat_dec_eq(v___x_6279_, v___x_6280_);
                if v___x_6281_ == 0 {
                    v___y_6241_ = v_a_6186_;
                    v___y_6242_ = v_a_6187_;
                    v___y_6243_ = v_a_6188_;
                    v___y_6244_ = v_a_6189_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_value_x3f_6184_);
                    crate::leanh::lean_dec_ref(v_type_6183_);
                    crate::leanh::lean_dec_ref(v_ids_6182_);
                    crate::leanh::lean_dec_ref(v_hyps_6181_);
                    v___x_6282_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Widget_addInteractiveHypothesisBundle___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Widget_addInteractiveHypothesisBundle___closed__2_once
                        ),
                        _init_l_Lean_Widget_addInteractiveHypothesisBundle___closed__2,
                    );
                    v___x_6283_ = l_Lean_throwError___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__3___redArg(v___x_6282_, v_a_6186_, v_a_6187_, v_a_6188_, v_a_6189_);
                    v_a_6284_ = crate::leanh::lean_ctor_get(v___x_6283_, 0);
                    v_isSharedCheck_6291_ = (!crate::leanh::lean_is_exclusive(v___x_6283_)) as u8;
                    if v_isSharedCheck_6291_ == 0 {
                        v___x_6286_ = v___x_6283_;
                        v_isShared_6287_ = v_isSharedCheck_6291_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6284_);
                        crate::leanh::lean_dec(v___x_6283_);
                        v___x_6286_ = crate::leanh::lean_box(0);
                        v_isShared_6287_ = v_isSharedCheck_6291_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6198_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___y_6193_);
                v___x_6199_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6199_, 0, v___y_6195_);
                crate::leanh::lean_ctor_set(v___x_6199_, 1, v___y_6194_);
                crate::leanh::lean_ctor_set(v___x_6199_, 2, v___y_6192_);
                crate::leanh::lean_ctor_set(v___x_6199_, 3, v___y_6196_);
                crate::leanh::lean_ctor_set(v___x_6199_, 4, v___y_6193_);
                crate::leanh::lean_ctor_set(v___x_6199_, 5, v___y_6197_);
                crate::leanh::lean_ctor_set(v___x_6199_, 6, v___x_6198_);
                crate::leanh::lean_ctor_set(v___x_6199_, 7, v___x_6198_);
                v___x_6200_ = lean_array_push(v_hyps_6181_, v___x_6199_);
                v___x_6201_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6201_, 0, v___x_6200_);
                return v___x_6201_;
            }
            2 => {
                v___x_6210_ = l_Lean_Expr_isSort(v___y_6208_);
                crate::leanh::lean_dec_ref(v___y_6208_);
                if v___x_6210_ == 0 {
                    v___x_6211_ = crate::leanh::lean_box(0);
                    v___y_6192_ = v___y_6203_;
                    v___y_6193_ = v___y_6209_;
                    v___y_6194_ = v___y_6205_;
                    v___y_6195_ = v___y_6206_;
                    v___y_6196_ = v___y_6207_;
                    v___y_6197_ = v___x_6211_;
                    state = 1;
                    continue;
                } else {
                    v___x_6212_ = crate::leanh::lean_box((v___y_6204_) as usize);
                    v___x_6213_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6213_, 0, v___x_6212_);
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
                crate::leanh::lean_inc_ref(v_type_6183_);
                v___x_6223_ = l_Lean_Meta_isClass_x3f(
                    v_type_6183_,
                    v___y_6218_,
                    v___y_6220_,
                    v___y_6221_,
                    v___y_6219_,
                );
                if crate::leanh::lean_obj_tag(v___x_6223_) == 0 {
                    v_a_6224_ = crate::leanh::lean_ctor_get(v___x_6223_, 0);
                    crate::leanh::lean_inc(v_a_6224_);
                    crate::leanh::lean_dec_ref_known(v___x_6223_, 1);
                    v___x_6225_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_6183_, v___y_6220_);
                    if crate::leanh::lean_obj_tag(v_a_6224_) == 0 {
                        v_a_6226_ = crate::leanh::lean_ctor_get(v___x_6225_, 0);
                        crate::leanh::lean_inc(v_a_6226_);
                        crate::leanh::lean_dec_ref(v___x_6225_);
                        v___x_6227_ = 1;
                        v___x_6228_ = crate::leanh::lean_box(0);
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
                        crate::leanh::lean_dec_ref_known(v_a_6224_, 1);
                        v_a_6229_ = crate::leanh::lean_ctor_get(v___x_6225_, 0);
                        crate::leanh::lean_inc(v_a_6229_);
                        crate::leanh::lean_dec_ref(v___x_6225_);
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
                    crate::leanh::lean_dec(v_a_6222_);
                    crate::leanh::lean_dec_ref(v___y_6217_);
                    crate::leanh::lean_dec_ref(v___y_6216_);
                    crate::leanh::lean_dec_ref(v___y_6215_);
                    crate::leanh::lean_dec_ref(v_type_6183_);
                    crate::leanh::lean_dec_ref(v_hyps_6181_);
                    v_a_6232_ = crate::leanh::lean_ctor_get(v___x_6223_, 0);
                    v_isSharedCheck_6239_ = (!crate::leanh::lean_is_exclusive(v___x_6223_)) as u8;
                    if v_isSharedCheck_6239_ == 0 {
                        v___x_6234_ = v___x_6223_;
                        v_isShared_6235_ = v_isSharedCheck_6239_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6232_);
                        crate::leanh::lean_dec(v___x_6223_);
                        v___x_6234_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_6238_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6238_, 0, v_a_6232_);
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
                crate::leanh::lean_inc_ref(v_type_6183_);
                v___x_6246_ = l_Lean_Widget_ppExprTagged(
                    v_type_6183_,
                    v___x_6245_,
                    v___y_6241_,
                    v___y_6242_,
                    v___y_6243_,
                    v___y_6244_,
                );
                if crate::leanh::lean_obj_tag(v___x_6246_) == 0 {
                    v_a_6247_ = crate::leanh::lean_ctor_get(v___x_6246_, 0);
                    crate::leanh::lean_inc(v_a_6247_);
                    crate::leanh::lean_dec_ref_known(v___x_6246_, 1);
                    v_sz_6248_ = lean_array_size(v_ids_6182_);
                    v___x_6249_ = 0usize;
                    crate::leanh::lean_inc_ref(v_ids_6182_);
                    v_fvarIds_6250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__0(v_sz_6248_, v___x_6249_, v_ids_6182_);
                    v_names_6251_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__1(v_sz_6248_, v___x_6249_, v_ids_6182_);
                    if crate::leanh::lean_obj_tag(v_value_x3f_6184_) == 0 {
                        v___x_6252_ = crate::leanh::lean_box(0);
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
                        v_val_6253_ = crate::leanh::lean_ctor_get(v_value_x3f_6184_, 0);
                        v_isSharedCheck_6270_ =
                            (!crate::leanh::lean_is_exclusive(v_value_x3f_6184_)) as u8;
                        if v_isSharedCheck_6270_ == 0 {
                            v___x_6255_ = v_value_x3f_6184_;
                            v_isShared_6256_ = v_isSharedCheck_6270_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_6253_);
                            crate::leanh::lean_dec(v_value_x3f_6184_);
                            v___x_6255_ = crate::leanh::lean_box(0);
                            v_isShared_6256_ = v_isSharedCheck_6270_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_value_x3f_6184_);
                    crate::leanh::lean_dec_ref(v_type_6183_);
                    crate::leanh::lean_dec_ref(v_ids_6182_);
                    crate::leanh::lean_dec_ref(v_hyps_6181_);
                    v_a_6271_ = crate::leanh::lean_ctor_get(v___x_6246_, 0);
                    v_isSharedCheck_6278_ = (!crate::leanh::lean_is_exclusive(v___x_6246_)) as u8;
                    if v_isSharedCheck_6278_ == 0 {
                        v___x_6273_ = v___x_6246_;
                        v_isShared_6274_ = v_isSharedCheck_6278_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6271_);
                        crate::leanh::lean_dec(v___x_6246_);
                        v___x_6273_ = crate::leanh::lean_box(0);
                        v_isShared_6274_ = v_isSharedCheck_6278_;
                        state = 11;
                        continue;
                    }
                }
            }
            7 => {
                v___x_6257_ = l___private_Lean_Widget_InteractiveGoal_0__Lean_Widget_addInteractiveHypothesisBundle_ppLetValueExprTagged(v_tactic_6185_, v_val_6253_, v___y_6241_, v___y_6242_, v___y_6243_, v___y_6244_);
                if crate::leanh::lean_obj_tag(v___x_6257_) == 0 {
                    v_a_6258_ = crate::leanh::lean_ctor_get(v___x_6257_, 0);
                    crate::leanh::lean_inc(v_a_6258_);
                    crate::leanh::lean_dec_ref_known(v___x_6257_, 1);
                    if v_isShared_6256_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6255_, 0, v_a_6258_);
                        v___x_6260_ = v___x_6255_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6261_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6261_, 0, v_a_6258_);
                        v___x_6260_ = v_reuseFailAlloc_6261_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6255_);
                    crate::leanh::lean_dec_ref(v_names_6251_);
                    crate::leanh::lean_dec_ref(v_fvarIds_6250_);
                    crate::leanh::lean_dec(v_a_6247_);
                    crate::leanh::lean_dec_ref(v_type_6183_);
                    crate::leanh::lean_dec_ref(v_hyps_6181_);
                    v_a_6262_ = crate::leanh::lean_ctor_get(v___x_6257_, 0);
                    v_isSharedCheck_6269_ = (!crate::leanh::lean_is_exclusive(v___x_6257_)) as u8;
                    if v_isSharedCheck_6269_ == 0 {
                        v___x_6264_ = v___x_6257_;
                        v_isShared_6265_ = v_isSharedCheck_6269_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6262_);
                        crate::leanh::lean_dec(v___x_6257_);
                        v___x_6264_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_6268_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6268_, 0, v_a_6262_);
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
                    v_reuseFailAlloc_6277_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6277_, 0, v_a_6271_);
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
                    v_reuseFailAlloc_6290_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6290_, 0, v_a_6284_);
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
    mut v_hyps_6292_: *mut crate::leanh::LeanObject,
    mut v_ids_6293_: *mut crate::leanh::LeanObject,
    mut v_type_6294_: *mut crate::leanh::LeanObject,
    mut v_value_x3f_6295_: *mut crate::leanh::LeanObject,
    mut v_tactic_6296_: *mut crate::leanh::LeanObject,
    mut v_a_6297_: *mut crate::leanh::LeanObject,
    mut v_a_6298_: *mut crate::leanh::LeanObject,
    mut v_a_6299_: *mut crate::leanh::LeanObject,
    mut v_a_6300_: *mut crate::leanh::LeanObject,
    mut v_a_6301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tactic_boxed_6302_: u8 = 0;
    let mut v_res_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_tactic_boxed_6302_ = (crate::leanh::lean_unbox(v_tactic_6296_) as u8);
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
    crate::leanh::lean_dec(v_a_6300_);
    crate::leanh::lean_dec_ref(v_a_6299_);
    crate::leanh::lean_dec(v_a_6298_);
    crate::leanh::lean_dec_ref(v_a_6297_);
    return v_res_6303_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__3(
    mut v_00_u03b1_6304_: *mut crate::leanh::LeanObject,
    mut v_msg_6305_: *mut crate::leanh::LeanObject,
    mut v___y_6306_: *mut crate::leanh::LeanObject,
    mut v___y_6307_: *mut crate::leanh::LeanObject,
    mut v___y_6308_: *mut crate::leanh::LeanObject,
    mut v___y_6309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_6312_: *mut crate::leanh::LeanObject,
    mut v_msg_6313_: *mut crate::leanh::LeanObject,
    mut v___y_6314_: *mut crate::leanh::LeanObject,
    mut v___y_6315_: *mut crate::leanh::LeanObject,
    mut v___y_6316_: *mut crate::leanh::LeanObject,
    mut v___y_6317_: *mut crate::leanh::LeanObject,
    mut v___y_6318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6319_ = l_Lean_throwError___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__3(
        v_00_u03b1_6312_,
        v_msg_6313_,
        v___y_6314_,
        v___y_6315_,
        v___y_6316_,
        v___y_6317_,
    );
    crate::leanh::lean_dec(v___y_6317_);
    crate::leanh::lean_dec_ref(v___y_6316_);
    crate::leanh::lean_dec(v___y_6315_);
    crate::leanh::lean_dec_ref(v___y_6314_);
    return v_res_6319_;
}
pub unsafe fn l_Lean_Widget_withGoalCtx___redArg___lam__0(
    mut v_val_6320_: *mut crate::leanh::LeanObject,
    mut v_action_6321_: *mut crate::leanh::LeanObject,
    mut v_inst_6322_: *mut crate::leanh::LeanObject,
    mut v_inst_6323_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_6324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_6326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lctx_6325_ = crate::leanh::lean_ctor_get(v_val_6320_, 1);
    v_localInstances_6326_ = crate::leanh::lean_ctor_get(v_val_6320_, 4);
    crate::leanh::lean_inc_ref(v_localInstances_6326_);
    v___x_6327_ = crate::leanh::lean_box(1);
    v___x_6328_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6328_, 0, v_____do__lift_6324_);
    crate::leanh::lean_ctor_set(v___x_6328_, 1, v___x_6327_);
    crate::leanh::lean_ctor_set(v___x_6328_, 2, v___x_6327_);
    crate::leanh::lean_inc_ref(v_lctx_6325_);
    v___x_6329_ = l_Lean_LocalContext_sanitizeNames(v_lctx_6325_, v___x_6328_);
    v_fst_6330_ = crate::leanh::lean_ctor_get(v___x_6329_, 0);
    crate::leanh::lean_inc_n(v_fst_6330_, 2);
    crate::leanh::lean_dec_ref(v___x_6329_);
    v___x_6331_ = crate::leanh::lean_apply_2(v_action_6321_, v_fst_6330_, v_val_6320_);
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_6334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6334_ = l_Lean_Widget_withGoalCtx___redArg___lam__1___closed__0;
    v___x_6335_ = l_Lean_stringToMessageData(v___x_6334_);
    return v___x_6335_;
}
pub unsafe fn l_Lean_Widget_withGoalCtx___redArg___lam__1(
    mut v_goal_6336_: *mut crate::leanh::LeanObject,
    mut v_action_6337_: *mut crate::leanh::LeanObject,
    mut v_inst_6338_: *mut crate::leanh::LeanObject,
    mut v_inst_6339_: *mut crate::leanh::LeanObject,
    mut v_toBind_6340_: *mut crate::leanh::LeanObject,
    mut v_inst_6341_: *mut crate::leanh::LeanObject,
    mut v_inst_6342_: *mut crate::leanh::LeanObject,
    mut v_mctx_6343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6344_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_6343_, v_goal_6336_);
    if crate::leanh::lean_obj_tag(v___x_6344_) == 1 {
        let mut v_val_6345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_6342_);
        crate::leanh::lean_dec(v_goal_6336_);
        v_val_6345_ = crate::leanh::lean_ctor_get(v___x_6344_, 0);
        crate::leanh::lean_inc(v_val_6345_);
        crate::leanh::lean_dec_ref_known(v___x_6344_, 1);
        v___f_6346_ = crate::leanh::lean_alloc_closure(
            l_Lean_Widget_withGoalCtx___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_6346_, 0, v_val_6345_);
        crate::leanh::lean_closure_set(v___f_6346_, 1, v_action_6337_);
        crate::leanh::lean_closure_set(v___f_6346_, 2, v_inst_6338_);
        crate::leanh::lean_closure_set(v___f_6346_, 3, v_inst_6339_);
        v___x_6347_ = crate::leanh::lean_apply_4(
            v_toBind_6340_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_inst_6341_,
            v___f_6346_,
        );
        return v___x_6347_;
    } else {
        let mut v___x_6348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_6344_);
        crate::leanh::lean_dec(v_inst_6341_);
        crate::leanh::lean_dec(v_toBind_6340_);
        crate::leanh::lean_dec_ref(v_inst_6338_);
        crate::leanh::lean_dec(v_action_6337_);
        v___x_6348_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Widget_withGoalCtx___redArg___lam__1___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Widget_withGoalCtx___redArg___lam__1___closed__1_once),
            _init_l_Lean_Widget_withGoalCtx___redArg___lam__1___closed__1,
        );
        v___x_6349_ = l_Lean_MessageData_ofName(v_goal_6336_);
        v___x_6350_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6350_, 0, v___x_6348_);
        crate::leanh::lean_ctor_set(v___x_6350_, 1, v___x_6349_);
        v___x_6351_ = l_Lean_throwError___redArg(v_inst_6339_, v_inst_6342_, v___x_6350_);
        return v___x_6351_;
    }
}
pub unsafe fn l_Lean_Widget_withGoalCtx___redArg___lam__1___boxed(
    mut v_goal_6352_: *mut crate::leanh::LeanObject,
    mut v_action_6353_: *mut crate::leanh::LeanObject,
    mut v_inst_6354_: *mut crate::leanh::LeanObject,
    mut v_inst_6355_: *mut crate::leanh::LeanObject,
    mut v_toBind_6356_: *mut crate::leanh::LeanObject,
    mut v_inst_6357_: *mut crate::leanh::LeanObject,
    mut v_inst_6358_: *mut crate::leanh::LeanObject,
    mut v_mctx_6359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_mctx_6359_);
    return v_res_6360_;
}
pub unsafe fn l_Lean_Widget_withGoalCtx___redArg(
    mut v_inst_6361_: *mut crate::leanh::LeanObject,
    mut v_inst_6362_: *mut crate::leanh::LeanObject,
    mut v_inst_6363_: *mut crate::leanh::LeanObject,
    mut v_inst_6364_: *mut crate::leanh::LeanObject,
    mut v_inst_6365_: *mut crate::leanh::LeanObject,
    mut v_goal_6366_: *mut crate::leanh::LeanObject,
    mut v_action_6367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getMCtx_6369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_6368_ = crate::leanh::lean_ctor_get(v_inst_6362_, 1);
    crate::leanh::lean_inc_n(v_toBind_6368_, 2);
    v_getMCtx_6369_ = crate::leanh::lean_ctor_get(v_inst_6365_, 0);
    crate::leanh::lean_inc(v_getMCtx_6369_);
    crate::leanh::lean_dec_ref(v_inst_6365_);
    v___f_6370_ = crate::leanh::lean_alloc_closure(
        l_Lean_Widget_withGoalCtx___redArg___lam__1___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_6370_, 0, v_goal_6366_);
    crate::leanh::lean_closure_set(v___f_6370_, 1, v_action_6367_);
    crate::leanh::lean_closure_set(v___f_6370_, 2, v_inst_6361_);
    crate::leanh::lean_closure_set(v___f_6370_, 3, v_inst_6362_);
    crate::leanh::lean_closure_set(v___f_6370_, 4, v_toBind_6368_);
    crate::leanh::lean_closure_set(v___f_6370_, 5, v_inst_6364_);
    crate::leanh::lean_closure_set(v___f_6370_, 6, v_inst_6363_);
    v___x_6371_ = crate::leanh::lean_apply_4(
        v_toBind_6368_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getMCtx_6369_,
        v___f_6370_,
    );
    return v___x_6371_;
}
pub unsafe fn l_Lean_Widget_withGoalCtx(
    mut v_n_6372_: *mut crate::leanh::LeanObject,
    mut v_inst_6373_: *mut crate::leanh::LeanObject,
    mut v_inst_6374_: *mut crate::leanh::LeanObject,
    mut v_inst_6375_: *mut crate::leanh::LeanObject,
    mut v_inst_6376_: *mut crate::leanh::LeanObject,
    mut v_inst_6377_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6378_: *mut crate::leanh::LeanObject,
    mut v_goal_6379_: *mut crate::leanh::LeanObject,
    mut v_action_6380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_opts_6382_: *mut crate::leanh::LeanObject,
    mut v_opt_6383_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_6384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_6385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_6386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_6384_ = crate::leanh::lean_ctor_get(v_opt_6383_, 0);
    v_defValue_6385_ = crate::leanh::lean_ctor_get(v_opt_6383_, 1);
    v_map_6386_ = crate::leanh::lean_ctor_get(v_opts_6382_, 0);
    v___x_6387_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_6386_,
            v_name_6384_,
        );
    if crate::leanh::lean_obj_tag(v___x_6387_) == 0 {
        let mut v___x_6388_: u8 = 0;
        v___x_6388_ = (crate::leanh::lean_unbox(v_defValue_6385_) as u8);
        return v___x_6388_;
    } else {
        let mut v_val_6389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_6389_ = crate::leanh::lean_ctor_get(v___x_6387_, 0);
        crate::leanh::lean_inc(v_val_6389_);
        crate::leanh::lean_dec_ref_known(v___x_6387_, 1);
        if crate::leanh::lean_obj_tag(v_val_6389_) == 1 {
            let mut v_v_6390_: u8 = 0;
            v_v_6390_ = crate::leanh::lean_ctor_get_uint8(v_val_6389_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_6389_, 0);
            return v_v_6390_;
        } else {
            let mut v___x_6391_: u8 = 0;
            crate::leanh::lean_dec(v_val_6389_);
            v___x_6391_ = (crate::leanh::lean_unbox(v_defValue_6385_) as u8);
            return v___x_6391_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Widget_goalToInteractive_spec__0___boxed(
    mut v_opts_6392_: *mut crate::leanh::LeanObject,
    mut v_opt_6393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6394_: u8 = 0;
    let mut v_r_6395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6394_ =
        l_Lean_Option_get___at___00Lean_Widget_goalToInteractive_spec__0(v_opts_6392_, v_opt_6393_);
    crate::leanh::lean_dec_ref(v_opt_6393_);
    crate::leanh::lean_dec_ref(v_opts_6392_);
    v_r_6395_ = crate::leanh::lean_box((v_res_6394_) as usize);
    return v_r_6395_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Widget_goalToInteractive_spec__1(
    mut v_x_6396_: *mut crate::leanh::LeanObject,
    mut v_x_6397_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_6396_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_6397_) == 0 {
            let mut v___x_6398_: u8 = 0;
            v___x_6398_ = 1;
            return v___x_6398_;
        } else {
            let mut v___x_6399_: u8 = 0;
            v___x_6399_ = 0;
            return v___x_6399_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_6397_) == 0 {
            let mut v___x_6400_: u8 = 0;
            v___x_6400_ = 0;
            return v___x_6400_;
        } else {
            let mut v_val_6401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_6402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6403_: u8 = 0;
            v_val_6401_ = crate::leanh::lean_ctor_get(v_x_6396_, 0);
            v_val_6402_ = crate::leanh::lean_ctor_get(v_x_6397_, 0);
            v___x_6403_ = lean_expr_eqv(v_val_6401_, v_val_6402_);
            return v___x_6403_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Widget_goalToInteractive_spec__1___boxed(
    mut v_x_6404_: *mut crate::leanh::LeanObject,
    mut v_x_6405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6406_: u8 = 0;
    let mut v_r_6407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6406_ =
        l_Option_instBEq_beq___at___00Lean_Widget_goalToInteractive_spec__1(v_x_6404_, v_x_6405_);
    crate::leanh::lean_dec(v_x_6405_);
    crate::leanh::lean_dec(v_x_6404_);
    v_r_6407_ = crate::leanh::lean_box((v_res_6406_) as usize);
    return v_r_6407_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3___lam__0(
    mut v_ids_6408_: *mut crate::leanh::LeanObject,
    mut v_type_x3f_6409_: *mut crate::leanh::LeanObject,
    mut v_hyps_6410_: *mut crate::leanh::LeanObject,
    mut v___y_6411_: *mut crate::leanh::LeanObject,
    mut v___y_6412_: *mut crate::leanh::LeanObject,
    mut v___y_6413_: *mut crate::leanh::LeanObject,
    mut v___y_6414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6418_: u8 = 0;
    v___x_6416_ = lean_array_get_size(v_ids_6408_);
    v___x_6417_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6418_ = lean_nat_dec_eq(v___x_6416_, v___x_6417_);
    if v___x_6418_ == 0 {
        if crate::leanh::lean_obj_tag(v_type_x3f_6409_) == 0 {
            let mut v___x_6419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_ids_6408_);
            v___x_6419_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_6419_, 0, v_hyps_6410_);
            return v___x_6419_;
        } else {
            let mut v_val_6420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_6420_ = crate::leanh::lean_ctor_get(v_type_x3f_6409_, 0);
            crate::leanh::lean_inc(v_val_6420_);
            crate::leanh::lean_dec_ref_known(v_type_x3f_6409_, 1);
            v___x_6421_ = crate::leanh::lean_box(0);
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
        let mut v___x_6423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_type_x3f_6409_);
        crate::leanh::lean_dec_ref(v_ids_6408_);
        v___x_6423_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6423_, 0, v_hyps_6410_);
        return v___x_6423_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3___lam__0___boxed(
    mut v_ids_6424_: *mut crate::leanh::LeanObject,
    mut v_type_x3f_6425_: *mut crate::leanh::LeanObject,
    mut v_hyps_6426_: *mut crate::leanh::LeanObject,
    mut v___y_6427_: *mut crate::leanh::LeanObject,
    mut v___y_6428_: *mut crate::leanh::LeanObject,
    mut v___y_6429_: *mut crate::leanh::LeanObject,
    mut v___y_6430_: *mut crate::leanh::LeanObject,
    mut v___y_6431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3___lam__0(v_ids_6424_, v_type_x3f_6425_, v_hyps_6426_, v___y_6427_, v___y_6428_, v___y_6429_, v___y_6430_);
    crate::leanh::lean_dec(v___y_6430_);
    crate::leanh::lean_dec_ref(v___y_6429_);
    crate::leanh::lean_dec(v___y_6428_);
    crate::leanh::lean_dec_ref(v___y_6427_);
    return v_res_6432_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4_spec__9(
    mut v___x_6435_: u8,
    mut v___x_6436_: u8,
    mut v___x_6437_: u8,
    mut v_as_6438_: *mut crate::leanh::LeanObject,
    mut v_sz_6439_: usize,
    mut v_i_6440_: usize,
    mut v_b_6441_: *mut crate::leanh::LeanObject,
    mut v___y_6442_: *mut crate::leanh::LeanObject,
    mut v___y_6443_: *mut crate::leanh::LeanObject,
    mut v___y_6444_: *mut crate::leanh::LeanObject,
    mut v___y_6445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6447_: u8 = 0;
    let mut v___x_6448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6452_: u8 = 0;
    let mut v___x_6453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6458_: usize = 0;
    let mut v___x_6459_: usize = 0;
    let mut v_reuseFailAlloc_6461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varNames_6464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_6465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varNames_6471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_6472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6481_: u8 = 0;
    let mut v_fst_6482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6485_: u8 = 0;
    let mut v_fst_6486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6490_: u8 = 0;
    let mut v___x_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6502_: u8 = 0;
    let mut v___x_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6512_: u8 = 0;
    let mut v___x_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6516_: u8 = 0;
    let mut v___x_6517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6523_: u8 = 0;
    let mut v___x_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6533_: u8 = 0;
    let mut v___x_6535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6537_: u8 = 0;
    let mut v___x_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_6543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6548_: u8 = 0;
    let mut v___x_6550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: u8 = 0;
    let mut v_reuseFailAlloc_6552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6556_: u8 = 0;
    let mut v___x_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6560_: u8 = 0;
    let mut v_nondep_6561_: u8 = 0;
    let mut v_fvarId_6562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_6563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6586_: u8 = 0;
    let mut v___x_6588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6590_: u8 = 0;
    let mut v_reuseFailAlloc_6591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6595_: u8 = 0;
    let mut v___x_6597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6599_: u8 = 0;
    let mut v_a_6600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6603_: u8 = 0;
    let mut v___x_6605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6607_: u8 = 0;
    let mut v_a_6608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6611_: u8 = 0;
    let mut v___x_6613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6615_: u8 = 0;
    let mut v_fvarId_6616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_6617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6622_: u8 = 0;
    let mut v___x_6624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6625_: u8 = 0;
    let mut v_reuseFailAlloc_6626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6630_: u8 = 0;
    let mut v___x_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6634_: u8 = 0;
    let mut v___x_6636_: u8 = 0;
    let mut v___x_6637_: u8 = 0;
    let mut v_isSharedCheck_6638_: u8 = 0;
    let mut v_isSharedCheck_6639_: u8 = 0;
    let mut v_unused_6640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6641_: u8 = 0;
    let mut v_isSharedCheck_6642_: u8 = 0;
    let mut v_unused_6643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6447_ = lean_usize_dec_lt(v_i_6440_, v_sz_6439_);
                if v___x_6447_ == 0 {
                    v___x_6448_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6448_, 0, v_b_6441_);
                    return v___x_6448_;
                } else {
                    v_snd_6449_ = crate::leanh::lean_ctor_get(v_b_6441_, 1);
                    v_isSharedCheck_6642_ = (!crate::leanh::lean_is_exclusive(v_b_6441_)) as u8;
                    if v_isSharedCheck_6642_ == 0 {
                        v_unused_6643_ = crate::leanh::lean_ctor_get(v_b_6441_, 0);
                        crate::leanh::lean_dec(v_unused_6643_);
                        v___x_6451_ = v_b_6441_;
                        v_isShared_6452_ = v_isSharedCheck_6642_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6449_);
                        crate::leanh::lean_dec(v_b_6441_);
                        v___x_6451_ = crate::leanh::lean_box(0);
                        v_isShared_6452_ = v_isSharedCheck_6642_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6453_ = crate::leanh::lean_box(0);
                v_a_6476_ = lean_array_uget(v_as_6438_, v_i_6440_);
                if crate::leanh::lean_obj_tag(v_a_6476_) == 0 {
                    v_a_6455_ = v_snd_6449_;
                    state = 2;
                    continue;
                } else {
                    v_snd_6477_ = crate::leanh::lean_ctor_get(v_snd_6449_, 1);
                    crate::leanh::lean_inc(v_snd_6477_);
                    v_val_6478_ = crate::leanh::lean_ctor_get(v_a_6476_, 0);
                    v_isSharedCheck_6641_ = (!crate::leanh::lean_is_exclusive(v_a_6476_)) as u8;
                    if v_isSharedCheck_6641_ == 0 {
                        v___x_6480_ = v_a_6476_;
                        v_isShared_6481_ = v_isSharedCheck_6641_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6478_);
                        crate::leanh::lean_dec(v_a_6476_);
                        v___x_6480_ = crate::leanh::lean_box(0);
                        v_isShared_6481_ = v_isSharedCheck_6641_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6452_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6451_, 1, v_a_6455_);
                    crate::leanh::lean_ctor_set(v___x_6451_, 0, v___x_6453_);
                    v___x_6457_ = v___x_6451_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6461_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6461_, 0, v___x_6453_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6461_, 1, v_a_6455_);
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
                v___x_6466_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6466_, 0, v___y_6463_);
                v___x_6467_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6467_, 0, v___x_6466_);
                crate::leanh::lean_ctor_set(v___x_6467_, 1, v_hyps_6465_);
                v___x_6468_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6468_, 0, v_varNames_6464_);
                crate::leanh::lean_ctor_set(v___x_6468_, 1, v___x_6467_);
                v_a_6455_ = v___x_6468_;
                state = 2;
                continue;
            }
            5 => {
                v___x_6473_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6473_, 0, v___y_6470_);
                v___x_6474_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6474_, 0, v___x_6473_);
                crate::leanh::lean_ctor_set(v___x_6474_, 1, v_hyps_6472_);
                v___x_6475_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6475_, 0, v_varNames_6471_);
                crate::leanh::lean_ctor_set(v___x_6475_, 1, v___x_6474_);
                v_a_6455_ = v___x_6475_;
                state = 2;
                continue;
            }
            6 => {
                v_fst_6482_ = crate::leanh::lean_ctor_get(v_snd_6449_, 0);
                v_isSharedCheck_6639_ = (!crate::leanh::lean_is_exclusive(v_snd_6449_)) as u8;
                if v_isSharedCheck_6639_ == 0 {
                    v_unused_6640_ = crate::leanh::lean_ctor_get(v_snd_6449_, 1);
                    crate::leanh::lean_dec(v_unused_6640_);
                    v___x_6484_ = v_snd_6449_;
                    v_isShared_6485_ = v_isSharedCheck_6639_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_6482_);
                    crate::leanh::lean_dec(v_snd_6449_);
                    v___x_6484_ = crate::leanh::lean_box(0);
                    v_isShared_6485_ = v_isSharedCheck_6639_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_fst_6486_ = crate::leanh::lean_ctor_get(v_snd_6477_, 0);
                v_snd_6487_ = crate::leanh::lean_ctor_get(v_snd_6477_, 1);
                v_isSharedCheck_6638_ = (!crate::leanh::lean_is_exclusive(v_snd_6477_)) as u8;
                if v_isSharedCheck_6638_ == 0 {
                    v___x_6489_ = v_snd_6477_;
                    v_isShared_6490_ = v_isSharedCheck_6638_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6487_);
                    crate::leanh::lean_inc(v_fst_6486_);
                    crate::leanh::lean_dec(v_snd_6477_);
                    v___x_6489_ = crate::leanh::lean_box(0);
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
                        crate::leanh::lean_del_object(v___x_6480_);
                        crate::leanh::lean_dec(v_val_6478_);
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
                    v_reuseFailAlloc_6497_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6497_, 0, v_fst_6486_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6497_, 1, v_snd_6487_);
                    v___x_6493_ = v_reuseFailAlloc_6497_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_6485_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6484_, 1, v___x_6493_);
                    v___x_6495_ = v___x_6484_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6496_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6496_, 0, v_fst_6482_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6496_, 1, v___x_6493_);
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
                    if crate::leanh::lean_obj_tag(v___x_6503_) == 0 {
                        v_a_6504_ = crate::leanh::lean_ctor_get(v___x_6503_, 0);
                        crate::leanh::lean_inc(v_a_6504_);
                        crate::leanh::lean_dec_ref_known(v___x_6503_, 1);
                        v___x_6505_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6505_, 0, v___y_6500_);
                        crate::leanh::lean_ctor_set(v___x_6505_, 1, v___y_6501_);
                        v___x_6506_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_6507_ = lean_mk_empty_array_with_capacity(v___x_6506_);
                        v___x_6508_ = lean_array_push(v___x_6507_, v___x_6505_);
                        v___y_6463_ = v___y_6499_;
                        v_varNames_6464_ = v___x_6508_;
                        v_hyps_6465_ = v_a_6504_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_6501_);
                        crate::leanh::lean_dec_ref(v___y_6500_);
                        crate::leanh::lean_dec_ref(v___y_6499_);
                        crate::leanh::lean_del_object(v___x_6451_);
                        v_a_6509_ = crate::leanh::lean_ctor_get(v___x_6503_, 0);
                        v_isSharedCheck_6516_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6503_)) as u8;
                        if v_isSharedCheck_6516_ == 0 {
                            v___x_6511_ = v___x_6503_;
                            v_isShared_6512_ = v_isSharedCheck_6516_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6509_);
                            crate::leanh::lean_dec(v___x_6503_);
                            v___x_6511_ = crate::leanh::lean_box(0);
                            v_isShared_6512_ = v_isSharedCheck_6516_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_6486_);
                    v___x_6517_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6517_, 0, v___y_6500_);
                    crate::leanh::lean_ctor_set(v___x_6517_, 1, v___y_6501_);
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
                    v_reuseFailAlloc_6515_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6515_, 0, v_a_6509_);
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
                    if crate::leanh::lean_obj_tag(v___x_6524_) == 0 {
                        v_a_6525_ = crate::leanh::lean_ctor_get(v___x_6524_, 0);
                        crate::leanh::lean_inc(v_a_6525_);
                        crate::leanh::lean_dec_ref_known(v___x_6524_, 1);
                        v___x_6526_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6526_, 0, v___y_6520_);
                        crate::leanh::lean_ctor_set(v___x_6526_, 1, v___y_6522_);
                        v___x_6527_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_6528_ = lean_mk_empty_array_with_capacity(v___x_6527_);
                        v___x_6529_ = lean_array_push(v___x_6528_, v___x_6526_);
                        v___y_6470_ = v___y_6521_;
                        v_varNames_6471_ = v___x_6529_;
                        v_hyps_6472_ = v_a_6525_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_6522_);
                        crate::leanh::lean_dec_ref(v___y_6521_);
                        crate::leanh::lean_dec_ref(v___y_6520_);
                        crate::leanh::lean_del_object(v___x_6451_);
                        v_a_6530_ = crate::leanh::lean_ctor_get(v___x_6524_, 0);
                        v_isSharedCheck_6537_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6524_)) as u8;
                        if v_isSharedCheck_6537_ == 0 {
                            v___x_6532_ = v___x_6524_;
                            v_isShared_6533_ = v_isSharedCheck_6537_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6530_);
                            crate::leanh::lean_dec(v___x_6524_);
                            v___x_6532_ = crate::leanh::lean_box(0);
                            v_isShared_6533_ = v_isSharedCheck_6537_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_6486_);
                    v___x_6538_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6538_, 0, v___y_6520_);
                    crate::leanh::lean_ctor_set(v___x_6538_, 1, v___y_6522_);
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
                    v_reuseFailAlloc_6536_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6536_, 0, v_a_6530_);
                    v___x_6535_ = v_reuseFailAlloc_6536_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6535_;
            }
            18 => {
                if crate::leanh::lean_obj_tag(v_val_6478_) == 0 {
                    v_fvarId_6542_ = crate::leanh::lean_ctor_get(v_val_6478_, 1);
                    crate::leanh::lean_inc(v_fvarId_6542_);
                    v_userName_6543_ = crate::leanh::lean_ctor_get(v_val_6478_, 2);
                    crate::leanh::lean_inc(v_userName_6543_);
                    v_type_6544_ = crate::leanh::lean_ctor_get(v_val_6478_, 3);
                    crate::leanh::lean_inc_ref(v_type_6544_);
                    crate::leanh::lean_dec_ref_known(v_val_6478_, 4);
                    v___x_6545_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_6544_, v___y_6443_);
                    if crate::leanh::lean_obj_tag(v___x_6545_) == 0 {
                        v_a_6546_ = crate::leanh::lean_ctor_get(v___x_6545_, 0);
                        crate::leanh::lean_inc(v_a_6546_);
                        crate::leanh::lean_dec_ref_known(v___x_6545_, 1);
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
                            crate::leanh::lean_inc(v_a_6546_);
                            if v_isShared_6481_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_6480_, 0, v_a_6546_);
                                v___x_6550_ = v___x_6480_;
                                state = 19;
                                continue;
                            } else {
                                v_reuseFailAlloc_6552_ =
                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6552_, 0, v_a_6546_);
                                v___x_6550_ = v_reuseFailAlloc_6552_;
                                state = 19;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_6480_);
                            v___y_6499_ = v_a_6546_;
                            v___y_6500_ = v___x_6547_;
                            v___y_6501_ = v_fvarId_6542_;
                            v___y_6502_ = v___x_6548_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_userName_6543_);
                        crate::leanh::lean_dec(v_fvarId_6542_);
                        crate::leanh::lean_dec(v_snd_6487_);
                        crate::leanh::lean_dec(v_fst_6486_);
                        crate::leanh::lean_dec(v_fst_6482_);
                        crate::leanh::lean_del_object(v___x_6480_);
                        crate::leanh::lean_del_object(v___x_6451_);
                        v_a_6553_ = crate::leanh::lean_ctor_get(v___x_6545_, 0);
                        v_isSharedCheck_6560_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6545_)) as u8;
                        if v_isSharedCheck_6560_ == 0 {
                            v___x_6555_ = v___x_6545_;
                            v_isShared_6556_ = v_isSharedCheck_6560_;
                            state = 20;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6553_);
                            crate::leanh::lean_dec(v___x_6545_);
                            v___x_6555_ = crate::leanh::lean_box(0);
                            v_isShared_6556_ = v_isSharedCheck_6560_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    v_nondep_6561_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_6478_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    );
                    if v_nondep_6561_ == 0 {
                        v_fvarId_6562_ = crate::leanh::lean_ctor_get(v_val_6478_, 1);
                        crate::leanh::lean_inc(v_fvarId_6562_);
                        v_userName_6563_ = crate::leanh::lean_ctor_get(v_val_6478_, 2);
                        crate::leanh::lean_inc(v_userName_6563_);
                        v_type_6564_ = crate::leanh::lean_ctor_get(v_val_6478_, 3);
                        crate::leanh::lean_inc_ref(v_type_6564_);
                        v_value_6565_ = crate::leanh::lean_ctor_get(v_val_6478_, 4);
                        crate::leanh::lean_inc_ref(v_value_6565_);
                        crate::leanh::lean_dec_ref_known(v_val_6478_, 5);
                        v___x_6566_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3___lam__0(v_fst_6482_, v_fst_6486_, v_snd_6487_, v___y_6442_, v___y_6443_, v___y_6444_, v___y_6445_);
                        if crate::leanh::lean_obj_tag(v___x_6566_) == 0 {
                            v_a_6567_ = crate::leanh::lean_ctor_get(v___x_6566_, 0);
                            crate::leanh::lean_inc(v_a_6567_);
                            crate::leanh::lean_dec_ref_known(v___x_6566_, 1);
                            v___x_6568_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_6564_, v___y_6443_);
                            if crate::leanh::lean_obj_tag(v___x_6568_) == 0 {
                                v_a_6569_ = crate::leanh::lean_ctor_get(v___x_6568_, 0);
                                crate::leanh::lean_inc(v_a_6569_);
                                crate::leanh::lean_dec_ref_known(v___x_6568_, 1);
                                v___x_6570_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_value_6565_, v___y_6443_);
                                if crate::leanh::lean_obj_tag(v___x_6570_) == 0 {
                                    v_a_6571_ = crate::leanh::lean_ctor_get(v___x_6570_, 0);
                                    crate::leanh::lean_inc(v_a_6571_);
                                    crate::leanh::lean_dec_ref_known(v___x_6570_, 1);
                                    v___x_6572_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_6563_, v___x_6447_);
                                    v___x_6573_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_6573_, 0, v___x_6572_);
                                    crate::leanh::lean_ctor_set(v___x_6573_, 1, v_fvarId_6562_);
                                    v___x_6574_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_6575_ = lean_mk_empty_array_with_capacity(v___x_6574_);
                                    v___x_6576_ = lean_array_push(v___x_6575_, v___x_6573_);
                                    if v_isShared_6481_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_6480_, 0, v_a_6571_);
                                        v___x_6578_ = v___x_6480_;
                                        state = 22;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_6591_ =
                                            crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_6591_,
                                            0,
                                            v_a_6571_,
                                        );
                                        v___x_6578_ = v_reuseFailAlloc_6591_;
                                        state = 22;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_6569_);
                                    crate::leanh::lean_dec(v_a_6567_);
                                    crate::leanh::lean_dec(v_userName_6563_);
                                    crate::leanh::lean_dec(v_fvarId_6562_);
                                    crate::leanh::lean_del_object(v___x_6480_);
                                    crate::leanh::lean_del_object(v___x_6451_);
                                    v_a_6592_ = crate::leanh::lean_ctor_get(v___x_6570_, 0);
                                    v_isSharedCheck_6599_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6570_)) as u8;
                                    if v_isSharedCheck_6599_ == 0 {
                                        v___x_6594_ = v___x_6570_;
                                        v_isShared_6595_ = v_isSharedCheck_6599_;
                                        state = 25;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6592_);
                                        crate::leanh::lean_dec(v___x_6570_);
                                        v___x_6594_ = crate::leanh::lean_box(0);
                                        v_isShared_6595_ = v_isSharedCheck_6599_;
                                        state = 25;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6567_);
                                crate::leanh::lean_dec_ref(v_value_6565_);
                                crate::leanh::lean_dec(v_userName_6563_);
                                crate::leanh::lean_dec(v_fvarId_6562_);
                                crate::leanh::lean_del_object(v___x_6480_);
                                crate::leanh::lean_del_object(v___x_6451_);
                                v_a_6600_ = crate::leanh::lean_ctor_get(v___x_6568_, 0);
                                v_isSharedCheck_6607_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6568_)) as u8;
                                if v_isSharedCheck_6607_ == 0 {
                                    v___x_6602_ = v___x_6568_;
                                    v_isShared_6603_ = v_isSharedCheck_6607_;
                                    state = 27;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6600_);
                                    crate::leanh::lean_dec(v___x_6568_);
                                    v___x_6602_ = crate::leanh::lean_box(0);
                                    v_isShared_6603_ = v_isSharedCheck_6607_;
                                    state = 27;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_value_6565_);
                            crate::leanh::lean_dec_ref(v_type_6564_);
                            crate::leanh::lean_dec(v_userName_6563_);
                            crate::leanh::lean_dec(v_fvarId_6562_);
                            crate::leanh::lean_del_object(v___x_6480_);
                            crate::leanh::lean_del_object(v___x_6451_);
                            v_a_6608_ = crate::leanh::lean_ctor_get(v___x_6566_, 0);
                            v_isSharedCheck_6615_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6566_)) as u8;
                            if v_isSharedCheck_6615_ == 0 {
                                v___x_6610_ = v___x_6566_;
                                v_isShared_6611_ = v_isSharedCheck_6615_;
                                state = 29;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6608_);
                                crate::leanh::lean_dec(v___x_6566_);
                                v___x_6610_ = crate::leanh::lean_box(0);
                                v_isShared_6611_ = v_isSharedCheck_6615_;
                                state = 29;
                                continue;
                            }
                        }
                    } else {
                        v_fvarId_6616_ = crate::leanh::lean_ctor_get(v_val_6478_, 1);
                        crate::leanh::lean_inc(v_fvarId_6616_);
                        v_userName_6617_ = crate::leanh::lean_ctor_get(v_val_6478_, 2);
                        crate::leanh::lean_inc(v_userName_6617_);
                        v_type_6618_ = crate::leanh::lean_ctor_get(v_val_6478_, 3);
                        crate::leanh::lean_inc_ref(v_type_6618_);
                        crate::leanh::lean_dec_ref_known(v_val_6478_, 5);
                        v___x_6619_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_6618_, v___y_6443_);
                        if crate::leanh::lean_obj_tag(v___x_6619_) == 0 {
                            v_a_6620_ = crate::leanh::lean_ctor_get(v___x_6619_, 0);
                            crate::leanh::lean_inc(v_a_6620_);
                            crate::leanh::lean_dec_ref_known(v___x_6619_, 1);
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
                                crate::leanh::lean_inc(v_a_6620_);
                                if v_isShared_6481_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_6480_, 0, v_a_6620_);
                                    v___x_6624_ = v___x_6480_;
                                    state = 31;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6626_ =
                                        crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6626_,
                                        0,
                                        v_a_6620_,
                                    );
                                    v___x_6624_ = v_reuseFailAlloc_6626_;
                                    state = 31;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_6480_);
                                v___y_6520_ = v___x_6621_;
                                v___y_6521_ = v_a_6620_;
                                v___y_6522_ = v_fvarId_6616_;
                                v___y_6523_ = v___x_6622_;
                                state = 15;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_userName_6617_);
                            crate::leanh::lean_dec(v_fvarId_6616_);
                            crate::leanh::lean_dec(v_snd_6487_);
                            crate::leanh::lean_dec(v_fst_6486_);
                            crate::leanh::lean_dec(v_fst_6482_);
                            crate::leanh::lean_del_object(v___x_6480_);
                            crate::leanh::lean_del_object(v___x_6451_);
                            v_a_6627_ = crate::leanh::lean_ctor_get(v___x_6619_, 0);
                            v_isSharedCheck_6634_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6619_)) as u8;
                            if v_isSharedCheck_6634_ == 0 {
                                v___x_6629_ = v___x_6619_;
                                v_isShared_6630_ = v_isSharedCheck_6634_;
                                state = 32;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6627_);
                                crate::leanh::lean_dec(v___x_6619_);
                                v___x_6629_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_dec_ref(v___x_6550_);
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
                    v_reuseFailAlloc_6559_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6559_, 0, v_a_6553_);
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
                if crate::leanh::lean_obj_tag(v___x_6579_) == 0 {
                    v_a_6580_ = crate::leanh::lean_ctor_get(v___x_6579_, 0);
                    crate::leanh::lean_inc(v_a_6580_);
                    crate::leanh::lean_dec_ref_known(v___x_6579_, 1);
                    v___x_6581_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6581_, 0, v___x_6453_);
                    crate::leanh::lean_ctor_set(v___x_6581_, 1, v_a_6580_);
                    v___x_6582_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6582_, 0, v___x_6540_);
                    crate::leanh::lean_ctor_set(v___x_6582_, 1, v___x_6581_);
                    v_a_6455_ = v___x_6582_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_6451_);
                    v_a_6583_ = crate::leanh::lean_ctor_get(v___x_6579_, 0);
                    v_isSharedCheck_6590_ = (!crate::leanh::lean_is_exclusive(v___x_6579_)) as u8;
                    if v_isSharedCheck_6590_ == 0 {
                        v___x_6585_ = v___x_6579_;
                        v_isShared_6586_ = v_isSharedCheck_6590_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6583_);
                        crate::leanh::lean_dec(v___x_6579_);
                        v___x_6585_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_6589_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6589_, 0, v_a_6583_);
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
                    v_reuseFailAlloc_6598_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6598_, 0, v_a_6592_);
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
                    v_reuseFailAlloc_6606_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6606_, 0, v_a_6600_);
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
                    v_reuseFailAlloc_6614_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6614_, 0, v_a_6608_);
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
                crate::leanh::lean_dec_ref(v___x_6624_);
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
                    v_reuseFailAlloc_6633_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6633_, 0, v_a_6627_);
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
                        crate::leanh::lean_del_object(v___x_6489_);
                        crate::leanh::lean_del_object(v___x_6484_);
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_6480_);
                        crate::leanh::lean_dec(v_val_6478_);
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6489_);
                    crate::leanh::lean_del_object(v___x_6484_);
                    state = 18;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4_spec__9___boxed(
    mut v___x_6644_: *mut crate::leanh::LeanObject,
    mut v___x_6645_: *mut crate::leanh::LeanObject,
    mut v___x_6646_: *mut crate::leanh::LeanObject,
    mut v_as_6647_: *mut crate::leanh::LeanObject,
    mut v_sz_6648_: *mut crate::leanh::LeanObject,
    mut v_i_6649_: *mut crate::leanh::LeanObject,
    mut v_b_6650_: *mut crate::leanh::LeanObject,
    mut v___y_6651_: *mut crate::leanh::LeanObject,
    mut v___y_6652_: *mut crate::leanh::LeanObject,
    mut v___y_6653_: *mut crate::leanh::LeanObject,
    mut v___y_6654_: *mut crate::leanh::LeanObject,
    mut v___y_6655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_11682__boxed_6656_: u8 = 0;
    let mut v___x_11683__boxed_6657_: u8 = 0;
    let mut v___x_11684__boxed_6658_: u8 = 0;
    let mut v_sz_boxed_6659_: usize = 0;
    let mut v_i_boxed_6660_: usize = 0;
    let mut v_res_6661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_11682__boxed_6656_ = (crate::leanh::lean_unbox(v___x_6644_) as u8);
    v___x_11683__boxed_6657_ = (crate::leanh::lean_unbox(v___x_6645_) as u8);
    v___x_11684__boxed_6658_ = (crate::leanh::lean_unbox(v___x_6646_) as u8);
    v_sz_boxed_6659_ = crate::leanh::lean_unbox_usize(v_sz_6648_);
    crate::leanh::lean_dec(v_sz_6648_);
    v_i_boxed_6660_ = crate::leanh::lean_unbox_usize(v_i_6649_);
    crate::leanh::lean_dec(v_i_6649_);
    v_res_6661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4_spec__9(v___x_11682__boxed_6656_, v___x_11683__boxed_6657_, v___x_11684__boxed_6658_, v_as_6647_, v_sz_boxed_6659_, v_i_boxed_6660_, v_b_6650_, v___y_6651_, v___y_6652_, v___y_6653_, v___y_6654_);
    crate::leanh::lean_dec(v___y_6654_);
    crate::leanh::lean_dec_ref(v___y_6653_);
    crate::leanh::lean_dec(v___y_6652_);
    crate::leanh::lean_dec_ref(v___y_6651_);
    crate::leanh::lean_dec_ref(v_as_6647_);
    return v_res_6661_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4(
    mut v___x_6662_: u8,
    mut v___x_6663_: u8,
    mut v___x_6664_: u8,
    mut v_as_6665_: *mut crate::leanh::LeanObject,
    mut v_sz_6666_: usize,
    mut v_i_6667_: usize,
    mut v_b_6668_: *mut crate::leanh::LeanObject,
    mut v___y_6669_: *mut crate::leanh::LeanObject,
    mut v___y_6670_: *mut crate::leanh::LeanObject,
    mut v___y_6671_: *mut crate::leanh::LeanObject,
    mut v___y_6672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6674_: u8 = 0;
    let mut v___x_6675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6679_: u8 = 0;
    let mut v___x_6680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: usize = 0;
    let mut v___x_6686_: usize = 0;
    let mut v___x_6687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varNames_6691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_6692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varNames_6698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_6699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6708_: u8 = 0;
    let mut v_fst_6709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6712_: u8 = 0;
    let mut v_fst_6713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6717_: u8 = 0;
    let mut v___x_6720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6729_: u8 = 0;
    let mut v___x_6730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6739_: u8 = 0;
    let mut v___x_6741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6743_: u8 = 0;
    let mut v___x_6744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6750_: u8 = 0;
    let mut v___x_6751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6760_: u8 = 0;
    let mut v___x_6762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6764_: u8 = 0;
    let mut v___x_6765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_6770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6775_: u8 = 0;
    let mut v___x_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6778_: u8 = 0;
    let mut v_reuseFailAlloc_6779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6783_: u8 = 0;
    let mut v___x_6785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6787_: u8 = 0;
    let mut v_nondep_6788_: u8 = 0;
    let mut v_fvarId_6789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_6790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6813_: u8 = 0;
    let mut v___x_6815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6817_: u8 = 0;
    let mut v_reuseFailAlloc_6818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6822_: u8 = 0;
    let mut v___x_6824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6826_: u8 = 0;
    let mut v_a_6827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6830_: u8 = 0;
    let mut v___x_6832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6834_: u8 = 0;
    let mut v_a_6835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6838_: u8 = 0;
    let mut v___x_6840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6842_: u8 = 0;
    let mut v_fvarId_6843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_6844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: u8 = 0;
    let mut v___x_6851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: u8 = 0;
    let mut v_reuseFailAlloc_6853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6857_: u8 = 0;
    let mut v___x_6859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6861_: u8 = 0;
    let mut v___x_6863_: u8 = 0;
    let mut v___x_6864_: u8 = 0;
    let mut v_isSharedCheck_6865_: u8 = 0;
    let mut v_isSharedCheck_6866_: u8 = 0;
    let mut v_unused_6867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6868_: u8 = 0;
    let mut v_isSharedCheck_6869_: u8 = 0;
    let mut v_unused_6870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6674_ = lean_usize_dec_lt(v_i_6667_, v_sz_6666_);
                if v___x_6674_ == 0 {
                    v___x_6675_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6675_, 0, v_b_6668_);
                    return v___x_6675_;
                } else {
                    v_snd_6676_ = crate::leanh::lean_ctor_get(v_b_6668_, 1);
                    v_isSharedCheck_6869_ = (!crate::leanh::lean_is_exclusive(v_b_6668_)) as u8;
                    if v_isSharedCheck_6869_ == 0 {
                        v_unused_6870_ = crate::leanh::lean_ctor_get(v_b_6668_, 0);
                        crate::leanh::lean_dec(v_unused_6870_);
                        v___x_6678_ = v_b_6668_;
                        v_isShared_6679_ = v_isSharedCheck_6869_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6676_);
                        crate::leanh::lean_dec(v_b_6668_);
                        v___x_6678_ = crate::leanh::lean_box(0);
                        v_isShared_6679_ = v_isSharedCheck_6869_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6680_ = crate::leanh::lean_box(0);
                v_a_6703_ = lean_array_uget(v_as_6665_, v_i_6667_);
                if crate::leanh::lean_obj_tag(v_a_6703_) == 0 {
                    v_a_6682_ = v_snd_6676_;
                    state = 2;
                    continue;
                } else {
                    v_snd_6704_ = crate::leanh::lean_ctor_get(v_snd_6676_, 1);
                    crate::leanh::lean_inc(v_snd_6704_);
                    v_val_6705_ = crate::leanh::lean_ctor_get(v_a_6703_, 0);
                    v_isSharedCheck_6868_ = (!crate::leanh::lean_is_exclusive(v_a_6703_)) as u8;
                    if v_isSharedCheck_6868_ == 0 {
                        v___x_6707_ = v_a_6703_;
                        v_isShared_6708_ = v_isSharedCheck_6868_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6705_);
                        crate::leanh::lean_dec(v_a_6703_);
                        v___x_6707_ = crate::leanh::lean_box(0);
                        v_isShared_6708_ = v_isSharedCheck_6868_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6679_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6678_, 1, v_a_6682_);
                    crate::leanh::lean_ctor_set(v___x_6678_, 0, v___x_6680_);
                    v___x_6684_ = v___x_6678_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6688_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6688_, 0, v___x_6680_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6688_, 1, v_a_6682_);
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
                v___x_6693_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6693_, 0, v___y_6690_);
                v___x_6694_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6694_, 0, v___x_6693_);
                crate::leanh::lean_ctor_set(v___x_6694_, 1, v_hyps_6692_);
                v___x_6695_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6695_, 0, v_varNames_6691_);
                crate::leanh::lean_ctor_set(v___x_6695_, 1, v___x_6694_);
                v_a_6682_ = v___x_6695_;
                state = 2;
                continue;
            }
            5 => {
                v___x_6700_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6700_, 0, v___y_6697_);
                v___x_6701_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6701_, 0, v___x_6700_);
                crate::leanh::lean_ctor_set(v___x_6701_, 1, v_hyps_6699_);
                v___x_6702_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6702_, 0, v_varNames_6698_);
                crate::leanh::lean_ctor_set(v___x_6702_, 1, v___x_6701_);
                v_a_6682_ = v___x_6702_;
                state = 2;
                continue;
            }
            6 => {
                v_fst_6709_ = crate::leanh::lean_ctor_get(v_snd_6676_, 0);
                v_isSharedCheck_6866_ = (!crate::leanh::lean_is_exclusive(v_snd_6676_)) as u8;
                if v_isSharedCheck_6866_ == 0 {
                    v_unused_6867_ = crate::leanh::lean_ctor_get(v_snd_6676_, 1);
                    crate::leanh::lean_dec(v_unused_6867_);
                    v___x_6711_ = v_snd_6676_;
                    v_isShared_6712_ = v_isSharedCheck_6866_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_6709_);
                    crate::leanh::lean_dec(v_snd_6676_);
                    v___x_6711_ = crate::leanh::lean_box(0);
                    v_isShared_6712_ = v_isSharedCheck_6866_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_fst_6713_ = crate::leanh::lean_ctor_get(v_snd_6704_, 0);
                v_snd_6714_ = crate::leanh::lean_ctor_get(v_snd_6704_, 1);
                v_isSharedCheck_6865_ = (!crate::leanh::lean_is_exclusive(v_snd_6704_)) as u8;
                if v_isSharedCheck_6865_ == 0 {
                    v___x_6716_ = v_snd_6704_;
                    v_isShared_6717_ = v_isSharedCheck_6865_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6714_);
                    crate::leanh::lean_inc(v_fst_6713_);
                    crate::leanh::lean_dec(v_snd_6704_);
                    v___x_6716_ = crate::leanh::lean_box(0);
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
                        crate::leanh::lean_del_object(v___x_6707_);
                        crate::leanh::lean_dec(v_val_6705_);
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
                    v_reuseFailAlloc_6724_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6724_, 0, v_fst_6713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6724_, 1, v_snd_6714_);
                    v___x_6720_ = v_reuseFailAlloc_6724_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_6712_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6711_, 1, v___x_6720_);
                    v___x_6722_ = v___x_6711_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6723_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6723_, 0, v_fst_6709_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6723_, 1, v___x_6720_);
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
                    if crate::leanh::lean_obj_tag(v___x_6730_) == 0 {
                        v_a_6731_ = crate::leanh::lean_ctor_get(v___x_6730_, 0);
                        crate::leanh::lean_inc(v_a_6731_);
                        crate::leanh::lean_dec_ref_known(v___x_6730_, 1);
                        v___x_6732_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6732_, 0, v___y_6728_);
                        crate::leanh::lean_ctor_set(v___x_6732_, 1, v___y_6727_);
                        v___x_6733_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_6734_ = lean_mk_empty_array_with_capacity(v___x_6733_);
                        v___x_6735_ = lean_array_push(v___x_6734_, v___x_6732_);
                        v___y_6690_ = v___y_6726_;
                        v_varNames_6691_ = v___x_6735_;
                        v_hyps_6692_ = v_a_6731_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_6728_);
                        crate::leanh::lean_dec(v___y_6727_);
                        crate::leanh::lean_dec_ref(v___y_6726_);
                        crate::leanh::lean_del_object(v___x_6678_);
                        v_a_6736_ = crate::leanh::lean_ctor_get(v___x_6730_, 0);
                        v_isSharedCheck_6743_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6730_)) as u8;
                        if v_isSharedCheck_6743_ == 0 {
                            v___x_6738_ = v___x_6730_;
                            v_isShared_6739_ = v_isSharedCheck_6743_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6736_);
                            crate::leanh::lean_dec(v___x_6730_);
                            v___x_6738_ = crate::leanh::lean_box(0);
                            v_isShared_6739_ = v_isSharedCheck_6743_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_6713_);
                    v___x_6744_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6744_, 0, v___y_6728_);
                    crate::leanh::lean_ctor_set(v___x_6744_, 1, v___y_6727_);
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
                    v_reuseFailAlloc_6742_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6742_, 0, v_a_6736_);
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
                    if crate::leanh::lean_obj_tag(v___x_6751_) == 0 {
                        v_a_6752_ = crate::leanh::lean_ctor_get(v___x_6751_, 0);
                        crate::leanh::lean_inc(v_a_6752_);
                        crate::leanh::lean_dec_ref_known(v___x_6751_, 1);
                        v___x_6753_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6753_, 0, v___y_6747_);
                        crate::leanh::lean_ctor_set(v___x_6753_, 1, v___y_6748_);
                        v___x_6754_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_6755_ = lean_mk_empty_array_with_capacity(v___x_6754_);
                        v___x_6756_ = lean_array_push(v___x_6755_, v___x_6753_);
                        v___y_6697_ = v___y_6749_;
                        v_varNames_6698_ = v___x_6756_;
                        v_hyps_6699_ = v_a_6752_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_6749_);
                        crate::leanh::lean_dec(v___y_6748_);
                        crate::leanh::lean_dec_ref(v___y_6747_);
                        crate::leanh::lean_del_object(v___x_6678_);
                        v_a_6757_ = crate::leanh::lean_ctor_get(v___x_6751_, 0);
                        v_isSharedCheck_6764_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6751_)) as u8;
                        if v_isSharedCheck_6764_ == 0 {
                            v___x_6759_ = v___x_6751_;
                            v_isShared_6760_ = v_isSharedCheck_6764_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6757_);
                            crate::leanh::lean_dec(v___x_6751_);
                            v___x_6759_ = crate::leanh::lean_box(0);
                            v_isShared_6760_ = v_isSharedCheck_6764_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_6713_);
                    v___x_6765_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6765_, 0, v___y_6747_);
                    crate::leanh::lean_ctor_set(v___x_6765_, 1, v___y_6748_);
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
                    v_reuseFailAlloc_6763_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6763_, 0, v_a_6757_);
                    v___x_6762_ = v_reuseFailAlloc_6763_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6762_;
            }
            18 => {
                if crate::leanh::lean_obj_tag(v_val_6705_) == 0 {
                    v_fvarId_6769_ = crate::leanh::lean_ctor_get(v_val_6705_, 1);
                    crate::leanh::lean_inc(v_fvarId_6769_);
                    v_userName_6770_ = crate::leanh::lean_ctor_get(v_val_6705_, 2);
                    crate::leanh::lean_inc(v_userName_6770_);
                    v_type_6771_ = crate::leanh::lean_ctor_get(v_val_6705_, 3);
                    crate::leanh::lean_inc_ref(v_type_6771_);
                    crate::leanh::lean_dec_ref_known(v_val_6705_, 4);
                    v___x_6772_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_6771_, v___y_6670_);
                    if crate::leanh::lean_obj_tag(v___x_6772_) == 0 {
                        v_a_6773_ = crate::leanh::lean_ctor_get(v___x_6772_, 0);
                        crate::leanh::lean_inc(v_a_6773_);
                        crate::leanh::lean_dec_ref_known(v___x_6772_, 1);
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
                            crate::leanh::lean_inc(v_a_6773_);
                            if v_isShared_6708_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_6707_, 0, v_a_6773_);
                                v___x_6777_ = v___x_6707_;
                                state = 19;
                                continue;
                            } else {
                                v_reuseFailAlloc_6779_ =
                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6779_, 0, v_a_6773_);
                                v___x_6777_ = v_reuseFailAlloc_6779_;
                                state = 19;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_6707_);
                            v___y_6726_ = v_a_6773_;
                            v___y_6727_ = v_fvarId_6769_;
                            v___y_6728_ = v___x_6774_;
                            v___y_6729_ = v___x_6775_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_userName_6770_);
                        crate::leanh::lean_dec(v_fvarId_6769_);
                        crate::leanh::lean_dec(v_snd_6714_);
                        crate::leanh::lean_dec(v_fst_6713_);
                        crate::leanh::lean_dec(v_fst_6709_);
                        crate::leanh::lean_del_object(v___x_6707_);
                        crate::leanh::lean_del_object(v___x_6678_);
                        v_a_6780_ = crate::leanh::lean_ctor_get(v___x_6772_, 0);
                        v_isSharedCheck_6787_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6772_)) as u8;
                        if v_isSharedCheck_6787_ == 0 {
                            v___x_6782_ = v___x_6772_;
                            v_isShared_6783_ = v_isSharedCheck_6787_;
                            state = 20;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6780_);
                            crate::leanh::lean_dec(v___x_6772_);
                            v___x_6782_ = crate::leanh::lean_box(0);
                            v_isShared_6783_ = v_isSharedCheck_6787_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    v_nondep_6788_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_6705_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    );
                    if v_nondep_6788_ == 0 {
                        v_fvarId_6789_ = crate::leanh::lean_ctor_get(v_val_6705_, 1);
                        crate::leanh::lean_inc(v_fvarId_6789_);
                        v_userName_6790_ = crate::leanh::lean_ctor_get(v_val_6705_, 2);
                        crate::leanh::lean_inc(v_userName_6790_);
                        v_type_6791_ = crate::leanh::lean_ctor_get(v_val_6705_, 3);
                        crate::leanh::lean_inc_ref(v_type_6791_);
                        v_value_6792_ = crate::leanh::lean_ctor_get(v_val_6705_, 4);
                        crate::leanh::lean_inc_ref(v_value_6792_);
                        crate::leanh::lean_dec_ref_known(v_val_6705_, 5);
                        v___x_6793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3___lam__0(v_fst_6709_, v_fst_6713_, v_snd_6714_, v___y_6669_, v___y_6670_, v___y_6671_, v___y_6672_);
                        if crate::leanh::lean_obj_tag(v___x_6793_) == 0 {
                            v_a_6794_ = crate::leanh::lean_ctor_get(v___x_6793_, 0);
                            crate::leanh::lean_inc(v_a_6794_);
                            crate::leanh::lean_dec_ref_known(v___x_6793_, 1);
                            v___x_6795_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_6791_, v___y_6670_);
                            if crate::leanh::lean_obj_tag(v___x_6795_) == 0 {
                                v_a_6796_ = crate::leanh::lean_ctor_get(v___x_6795_, 0);
                                crate::leanh::lean_inc(v_a_6796_);
                                crate::leanh::lean_dec_ref_known(v___x_6795_, 1);
                                v___x_6797_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_value_6792_, v___y_6670_);
                                if crate::leanh::lean_obj_tag(v___x_6797_) == 0 {
                                    v_a_6798_ = crate::leanh::lean_ctor_get(v___x_6797_, 0);
                                    crate::leanh::lean_inc(v_a_6798_);
                                    crate::leanh::lean_dec_ref_known(v___x_6797_, 1);
                                    v___x_6799_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_6790_, v___x_6674_);
                                    v___x_6800_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_6800_, 0, v___x_6799_);
                                    crate::leanh::lean_ctor_set(v___x_6800_, 1, v_fvarId_6789_);
                                    v___x_6801_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_6802_ = lean_mk_empty_array_with_capacity(v___x_6801_);
                                    v___x_6803_ = lean_array_push(v___x_6802_, v___x_6800_);
                                    if v_isShared_6708_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_6707_, 0, v_a_6798_);
                                        v___x_6805_ = v___x_6707_;
                                        state = 22;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_6818_ =
                                            crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_6818_,
                                            0,
                                            v_a_6798_,
                                        );
                                        v___x_6805_ = v_reuseFailAlloc_6818_;
                                        state = 22;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_6796_);
                                    crate::leanh::lean_dec(v_a_6794_);
                                    crate::leanh::lean_dec(v_userName_6790_);
                                    crate::leanh::lean_dec(v_fvarId_6789_);
                                    crate::leanh::lean_del_object(v___x_6707_);
                                    crate::leanh::lean_del_object(v___x_6678_);
                                    v_a_6819_ = crate::leanh::lean_ctor_get(v___x_6797_, 0);
                                    v_isSharedCheck_6826_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6797_)) as u8;
                                    if v_isSharedCheck_6826_ == 0 {
                                        v___x_6821_ = v___x_6797_;
                                        v_isShared_6822_ = v_isSharedCheck_6826_;
                                        state = 25;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6819_);
                                        crate::leanh::lean_dec(v___x_6797_);
                                        v___x_6821_ = crate::leanh::lean_box(0);
                                        v_isShared_6822_ = v_isSharedCheck_6826_;
                                        state = 25;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6794_);
                                crate::leanh::lean_dec_ref(v_value_6792_);
                                crate::leanh::lean_dec(v_userName_6790_);
                                crate::leanh::lean_dec(v_fvarId_6789_);
                                crate::leanh::lean_del_object(v___x_6707_);
                                crate::leanh::lean_del_object(v___x_6678_);
                                v_a_6827_ = crate::leanh::lean_ctor_get(v___x_6795_, 0);
                                v_isSharedCheck_6834_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6795_)) as u8;
                                if v_isSharedCheck_6834_ == 0 {
                                    v___x_6829_ = v___x_6795_;
                                    v_isShared_6830_ = v_isSharedCheck_6834_;
                                    state = 27;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6827_);
                                    crate::leanh::lean_dec(v___x_6795_);
                                    v___x_6829_ = crate::leanh::lean_box(0);
                                    v_isShared_6830_ = v_isSharedCheck_6834_;
                                    state = 27;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_value_6792_);
                            crate::leanh::lean_dec_ref(v_type_6791_);
                            crate::leanh::lean_dec(v_userName_6790_);
                            crate::leanh::lean_dec(v_fvarId_6789_);
                            crate::leanh::lean_del_object(v___x_6707_);
                            crate::leanh::lean_del_object(v___x_6678_);
                            v_a_6835_ = crate::leanh::lean_ctor_get(v___x_6793_, 0);
                            v_isSharedCheck_6842_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6793_)) as u8;
                            if v_isSharedCheck_6842_ == 0 {
                                v___x_6837_ = v___x_6793_;
                                v_isShared_6838_ = v_isSharedCheck_6842_;
                                state = 29;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6835_);
                                crate::leanh::lean_dec(v___x_6793_);
                                v___x_6837_ = crate::leanh::lean_box(0);
                                v_isShared_6838_ = v_isSharedCheck_6842_;
                                state = 29;
                                continue;
                            }
                        }
                    } else {
                        v_fvarId_6843_ = crate::leanh::lean_ctor_get(v_val_6705_, 1);
                        crate::leanh::lean_inc(v_fvarId_6843_);
                        v_userName_6844_ = crate::leanh::lean_ctor_get(v_val_6705_, 2);
                        crate::leanh::lean_inc(v_userName_6844_);
                        v_type_6845_ = crate::leanh::lean_ctor_get(v_val_6705_, 3);
                        crate::leanh::lean_inc_ref(v_type_6845_);
                        crate::leanh::lean_dec_ref_known(v_val_6705_, 5);
                        v___x_6846_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_6845_, v___y_6670_);
                        if crate::leanh::lean_obj_tag(v___x_6846_) == 0 {
                            v_a_6847_ = crate::leanh::lean_ctor_get(v___x_6846_, 0);
                            crate::leanh::lean_inc(v_a_6847_);
                            crate::leanh::lean_dec_ref_known(v___x_6846_, 1);
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
                                crate::leanh::lean_inc(v_a_6847_);
                                if v_isShared_6708_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_6707_, 0, v_a_6847_);
                                    v___x_6851_ = v___x_6707_;
                                    state = 31;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6853_ =
                                        crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_6853_,
                                        0,
                                        v_a_6847_,
                                    );
                                    v___x_6851_ = v_reuseFailAlloc_6853_;
                                    state = 31;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_6707_);
                                v___y_6747_ = v___x_6848_;
                                v___y_6748_ = v_fvarId_6843_;
                                v___y_6749_ = v_a_6847_;
                                v___y_6750_ = v___x_6849_;
                                state = 15;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_userName_6844_);
                            crate::leanh::lean_dec(v_fvarId_6843_);
                            crate::leanh::lean_dec(v_snd_6714_);
                            crate::leanh::lean_dec(v_fst_6713_);
                            crate::leanh::lean_dec(v_fst_6709_);
                            crate::leanh::lean_del_object(v___x_6707_);
                            crate::leanh::lean_del_object(v___x_6678_);
                            v_a_6854_ = crate::leanh::lean_ctor_get(v___x_6846_, 0);
                            v_isSharedCheck_6861_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6846_)) as u8;
                            if v_isSharedCheck_6861_ == 0 {
                                v___x_6856_ = v___x_6846_;
                                v_isShared_6857_ = v_isSharedCheck_6861_;
                                state = 32;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6854_);
                                crate::leanh::lean_dec(v___x_6846_);
                                v___x_6856_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_dec_ref(v___x_6777_);
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
                    v_reuseFailAlloc_6786_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6786_, 0, v_a_6780_);
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
                if crate::leanh::lean_obj_tag(v___x_6806_) == 0 {
                    v_a_6807_ = crate::leanh::lean_ctor_get(v___x_6806_, 0);
                    crate::leanh::lean_inc(v_a_6807_);
                    crate::leanh::lean_dec_ref_known(v___x_6806_, 1);
                    v___x_6808_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6808_, 0, v___x_6680_);
                    crate::leanh::lean_ctor_set(v___x_6808_, 1, v_a_6807_);
                    v___x_6809_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6809_, 0, v___x_6767_);
                    crate::leanh::lean_ctor_set(v___x_6809_, 1, v___x_6808_);
                    v_a_6682_ = v___x_6809_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_6678_);
                    v_a_6810_ = crate::leanh::lean_ctor_get(v___x_6806_, 0);
                    v_isSharedCheck_6817_ = (!crate::leanh::lean_is_exclusive(v___x_6806_)) as u8;
                    if v_isSharedCheck_6817_ == 0 {
                        v___x_6812_ = v___x_6806_;
                        v_isShared_6813_ = v_isSharedCheck_6817_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6810_);
                        crate::leanh::lean_dec(v___x_6806_);
                        v___x_6812_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_6816_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6816_, 0, v_a_6810_);
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
                    v_reuseFailAlloc_6825_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6825_, 0, v_a_6819_);
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
                    v_reuseFailAlloc_6833_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6833_, 0, v_a_6827_);
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
                    v_reuseFailAlloc_6841_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6841_, 0, v_a_6835_);
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
                crate::leanh::lean_dec_ref(v___x_6851_);
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
                    v_reuseFailAlloc_6860_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6860_, 0, v_a_6854_);
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
                        crate::leanh::lean_del_object(v___x_6716_);
                        crate::leanh::lean_del_object(v___x_6711_);
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_6707_);
                        crate::leanh::lean_dec(v_val_6705_);
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6716_);
                    crate::leanh::lean_del_object(v___x_6711_);
                    state = 18;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4___boxed(
    mut v___x_6871_: *mut crate::leanh::LeanObject,
    mut v___x_6872_: *mut crate::leanh::LeanObject,
    mut v___x_6873_: *mut crate::leanh::LeanObject,
    mut v_as_6874_: *mut crate::leanh::LeanObject,
    mut v_sz_6875_: *mut crate::leanh::LeanObject,
    mut v_i_6876_: *mut crate::leanh::LeanObject,
    mut v_b_6877_: *mut crate::leanh::LeanObject,
    mut v___y_6878_: *mut crate::leanh::LeanObject,
    mut v___y_6879_: *mut crate::leanh::LeanObject,
    mut v___y_6880_: *mut crate::leanh::LeanObject,
    mut v___y_6881_: *mut crate::leanh::LeanObject,
    mut v___y_6882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_12087__boxed_6883_: u8 = 0;
    let mut v___x_12088__boxed_6884_: u8 = 0;
    let mut v___x_12089__boxed_6885_: u8 = 0;
    let mut v_sz_boxed_6886_: usize = 0;
    let mut v_i_boxed_6887_: usize = 0;
    let mut v_res_6888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_12087__boxed_6883_ = (crate::leanh::lean_unbox(v___x_6871_) as u8);
    v___x_12088__boxed_6884_ = (crate::leanh::lean_unbox(v___x_6872_) as u8);
    v___x_12089__boxed_6885_ = (crate::leanh::lean_unbox(v___x_6873_) as u8);
    v_sz_boxed_6886_ = crate::leanh::lean_unbox_usize(v_sz_6875_);
    crate::leanh::lean_dec(v_sz_6875_);
    v_i_boxed_6887_ = crate::leanh::lean_unbox_usize(v_i_6876_);
    crate::leanh::lean_dec(v_i_6876_);
    v_res_6888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4(v___x_12087__boxed_6883_, v___x_12088__boxed_6884_, v___x_12089__boxed_6885_, v_as_6874_, v_sz_boxed_6886_, v_i_boxed_6887_, v_b_6877_, v___y_6878_, v___y_6879_, v___y_6880_, v___y_6881_);
    crate::leanh::lean_dec(v___y_6881_);
    crate::leanh::lean_dec_ref(v___y_6880_);
    crate::leanh::lean_dec(v___y_6879_);
    crate::leanh::lean_dec_ref(v___y_6878_);
    crate::leanh::lean_dec_ref(v_as_6874_);
    return v_res_6888_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2(
    mut v_init_6889_: *mut crate::leanh::LeanObject,
    mut v___x_6890_: u8,
    mut v___x_6891_: u8,
    mut v___x_6892_: u8,
    mut v_n_6893_: *mut crate::leanh::LeanObject,
    mut v_b_6894_: *mut crate::leanh::LeanObject,
    mut v___y_6895_: *mut crate::leanh::LeanObject,
    mut v___y_6896_: *mut crate::leanh::LeanObject,
    mut v___y_6897_: *mut crate::leanh::LeanObject,
    mut v___y_6898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_6900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6903_: usize = 0;
    let mut v___x_6904_: usize = 0;
    let mut v___x_6905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6909_: u8 = 0;
    let mut v_fst_6910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6920_: u8 = 0;
    let mut v_a_6921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6924_: u8 = 0;
    let mut v___x_6926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6928_: u8 = 0;
    let mut v_vs_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6932_: usize = 0;
    let mut v___x_6933_: usize = 0;
    let mut v___x_6934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6938_: u8 = 0;
    let mut v_fst_6939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6949_: u8 = 0;
    let mut v_a_6950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6953_: u8 = 0;
    let mut v___x_6955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6957_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_6893_) == 0 {
                    v_cs_6900_ = crate::leanh::lean_ctor_get(v_n_6893_, 0);
                    v___x_6901_ = crate::leanh::lean_box(0);
                    v___x_6902_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6902_, 0, v___x_6901_);
                    crate::leanh::lean_ctor_set(v___x_6902_, 1, v_b_6894_);
                    v_sz_6903_ = lean_array_size(v_cs_6900_);
                    v___x_6904_ = 0usize;
                    v___x_6905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__3(v_init_6889_, v___x_6890_, v___x_6891_, v___x_6892_, v_cs_6900_, v_sz_6903_, v___x_6904_, v___x_6902_, v___y_6895_, v___y_6896_, v___y_6897_, v___y_6898_);
                    if crate::leanh::lean_obj_tag(v___x_6905_) == 0 {
                        v_a_6906_ = crate::leanh::lean_ctor_get(v___x_6905_, 0);
                        v_isSharedCheck_6920_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6905_)) as u8;
                        if v_isSharedCheck_6920_ == 0 {
                            v___x_6908_ = v___x_6905_;
                            v_isShared_6909_ = v_isSharedCheck_6920_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6906_);
                            crate::leanh::lean_dec(v___x_6905_);
                            v___x_6908_ = crate::leanh::lean_box(0);
                            v_isShared_6909_ = v_isSharedCheck_6920_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6921_ = crate::leanh::lean_ctor_get(v___x_6905_, 0);
                        v_isSharedCheck_6928_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6905_)) as u8;
                        if v_isSharedCheck_6928_ == 0 {
                            v___x_6923_ = v___x_6905_;
                            v_isShared_6924_ = v_isSharedCheck_6928_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6921_);
                            crate::leanh::lean_dec(v___x_6905_);
                            v___x_6923_ = crate::leanh::lean_box(0);
                            v_isShared_6924_ = v_isSharedCheck_6928_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_6929_ = crate::leanh::lean_ctor_get(v_n_6893_, 0);
                    v___x_6930_ = crate::leanh::lean_box(0);
                    v___x_6931_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6931_, 0, v___x_6930_);
                    crate::leanh::lean_ctor_set(v___x_6931_, 1, v_b_6894_);
                    v_sz_6932_ = lean_array_size(v_vs_6929_);
                    v___x_6933_ = 0usize;
                    v___x_6934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__4(v___x_6890_, v___x_6891_, v___x_6892_, v_vs_6929_, v_sz_6932_, v___x_6933_, v___x_6931_, v___y_6895_, v___y_6896_, v___y_6897_, v___y_6898_);
                    if crate::leanh::lean_obj_tag(v___x_6934_) == 0 {
                        v_a_6935_ = crate::leanh::lean_ctor_get(v___x_6934_, 0);
                        v_isSharedCheck_6949_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6934_)) as u8;
                        if v_isSharedCheck_6949_ == 0 {
                            v___x_6937_ = v___x_6934_;
                            v_isShared_6938_ = v_isSharedCheck_6949_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6935_);
                            crate::leanh::lean_dec(v___x_6934_);
                            v___x_6937_ = crate::leanh::lean_box(0);
                            v_isShared_6938_ = v_isSharedCheck_6949_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_6950_ = crate::leanh::lean_ctor_get(v___x_6934_, 0);
                        v_isSharedCheck_6957_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6934_)) as u8;
                        if v_isSharedCheck_6957_ == 0 {
                            v___x_6952_ = v___x_6934_;
                            v_isShared_6953_ = v_isSharedCheck_6957_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6950_);
                            crate::leanh::lean_dec(v___x_6934_);
                            v___x_6952_ = crate::leanh::lean_box(0);
                            v_isShared_6953_ = v_isSharedCheck_6957_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_6910_ = crate::leanh::lean_ctor_get(v_a_6906_, 0);
                if crate::leanh::lean_obj_tag(v_fst_6910_) == 0 {
                    v_snd_6911_ = crate::leanh::lean_ctor_get(v_a_6906_, 1);
                    crate::leanh::lean_inc(v_snd_6911_);
                    crate::leanh::lean_dec(v_a_6906_);
                    v___x_6912_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6912_, 0, v_snd_6911_);
                    if v_isShared_6909_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6908_, 0, v___x_6912_);
                        v___x_6914_ = v___x_6908_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6915_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6915_, 0, v___x_6912_);
                        v___x_6914_ = v_reuseFailAlloc_6915_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_6910_);
                    crate::leanh::lean_dec(v_a_6906_);
                    v_val_6916_ = crate::leanh::lean_ctor_get(v_fst_6910_, 0);
                    crate::leanh::lean_inc(v_val_6916_);
                    crate::leanh::lean_dec_ref_known(v_fst_6910_, 1);
                    if v_isShared_6909_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6908_, 0, v_val_6916_);
                        v___x_6918_ = v___x_6908_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6919_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6919_, 0, v_val_6916_);
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
                    v_reuseFailAlloc_6927_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6927_, 0, v_a_6921_);
                    v___x_6926_ = v_reuseFailAlloc_6927_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6926_;
            }
            6 => {
                v_fst_6939_ = crate::leanh::lean_ctor_get(v_a_6935_, 0);
                if crate::leanh::lean_obj_tag(v_fst_6939_) == 0 {
                    v_snd_6940_ = crate::leanh::lean_ctor_get(v_a_6935_, 1);
                    crate::leanh::lean_inc(v_snd_6940_);
                    crate::leanh::lean_dec(v_a_6935_);
                    v___x_6941_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6941_, 0, v_snd_6940_);
                    if v_isShared_6938_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6937_, 0, v___x_6941_);
                        v___x_6943_ = v___x_6937_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6944_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6944_, 0, v___x_6941_);
                        v___x_6943_ = v_reuseFailAlloc_6944_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_6939_);
                    crate::leanh::lean_dec(v_a_6935_);
                    v_val_6945_ = crate::leanh::lean_ctor_get(v_fst_6939_, 0);
                    crate::leanh::lean_inc(v_val_6945_);
                    crate::leanh::lean_dec_ref_known(v_fst_6939_, 1);
                    if v_isShared_6938_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6937_, 0, v_val_6945_);
                        v___x_6947_ = v___x_6937_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6948_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6948_, 0, v_val_6945_);
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
                    v_reuseFailAlloc_6956_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6956_, 0, v_a_6950_);
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
    mut v_init_6958_: *mut crate::leanh::LeanObject,
    mut v___x_6959_: u8,
    mut v___x_6960_: u8,
    mut v___x_6961_: u8,
    mut v_as_6962_: *mut crate::leanh::LeanObject,
    mut v_sz_6963_: usize,
    mut v_i_6964_: usize,
    mut v_b_6965_: *mut crate::leanh::LeanObject,
    mut v___y_6966_: *mut crate::leanh::LeanObject,
    mut v___y_6967_: *mut crate::leanh::LeanObject,
    mut v___y_6968_: *mut crate::leanh::LeanObject,
    mut v___y_6969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6971_: u8 = 0;
    let mut v___x_6972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6976_: u8 = 0;
    let mut v_a_6977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6982_: u8 = 0;
    let mut v___x_6983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6994_: usize = 0;
    let mut v___x_6995_: usize = 0;
    let mut v_reuseFailAlloc_6997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6998_: u8 = 0;
    let mut v_a_6999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7002_: u8 = 0;
    let mut v___x_7004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7006_: u8 = 0;
    let mut v_isSharedCheck_7007_: u8 = 0;
    let mut v_unused_7008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6971_ = lean_usize_dec_lt(v_i_6964_, v_sz_6963_);
                if v___x_6971_ == 0 {
                    v___x_6972_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6972_, 0, v_b_6965_);
                    return v___x_6972_;
                } else {
                    v_snd_6973_ = crate::leanh::lean_ctor_get(v_b_6965_, 1);
                    v_isSharedCheck_7007_ = (!crate::leanh::lean_is_exclusive(v_b_6965_)) as u8;
                    if v_isSharedCheck_7007_ == 0 {
                        v_unused_7008_ = crate::leanh::lean_ctor_get(v_b_6965_, 0);
                        crate::leanh::lean_dec(v_unused_7008_);
                        v___x_6975_ = v_b_6965_;
                        v_isShared_6976_ = v_isSharedCheck_7007_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6973_);
                        crate::leanh::lean_dec(v_b_6965_);
                        v___x_6975_ = crate::leanh::lean_box(0);
                        v_isShared_6976_ = v_isSharedCheck_7007_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_6977_ = lean_array_uget_borrowed(v_as_6962_, v_i_6964_);
                crate::leanh::lean_inc(v_snd_6973_);
                v___x_6978_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2(v_init_6958_, v___x_6959_, v___x_6960_, v___x_6961_, v_a_6977_, v_snd_6973_, v___y_6966_, v___y_6967_, v___y_6968_, v___y_6969_);
                if crate::leanh::lean_obj_tag(v___x_6978_) == 0 {
                    v_a_6979_ = crate::leanh::lean_ctor_get(v___x_6978_, 0);
                    v_isSharedCheck_6998_ = (!crate::leanh::lean_is_exclusive(v___x_6978_)) as u8;
                    if v_isSharedCheck_6998_ == 0 {
                        v___x_6981_ = v___x_6978_;
                        v_isShared_6982_ = v_isSharedCheck_6998_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6979_);
                        crate::leanh::lean_dec(v___x_6978_);
                        v___x_6981_ = crate::leanh::lean_box(0);
                        v_isShared_6982_ = v_isSharedCheck_6998_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6975_);
                    crate::leanh::lean_dec(v_snd_6973_);
                    v_a_6999_ = crate::leanh::lean_ctor_get(v___x_6978_, 0);
                    v_isSharedCheck_7006_ = (!crate::leanh::lean_is_exclusive(v___x_6978_)) as u8;
                    if v_isSharedCheck_7006_ == 0 {
                        v___x_7001_ = v___x_6978_;
                        v_isShared_7002_ = v_isSharedCheck_7006_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6999_);
                        crate::leanh::lean_dec(v___x_6978_);
                        v___x_7001_ = crate::leanh::lean_box(0);
                        v_isShared_7002_ = v_isSharedCheck_7006_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_6979_) == 0 {
                    v___x_6983_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6983_, 0, v_a_6979_);
                    if v_isShared_6976_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6975_, 0, v___x_6983_);
                        v___x_6985_ = v___x_6975_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6989_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6989_, 0, v___x_6983_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6989_, 1, v_snd_6973_);
                        v___x_6985_ = v_reuseFailAlloc_6989_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6981_);
                    crate::leanh::lean_dec(v_snd_6973_);
                    v_a_6990_ = crate::leanh::lean_ctor_get(v_a_6979_, 0);
                    crate::leanh::lean_inc(v_a_6990_);
                    crate::leanh::lean_dec_ref_known(v_a_6979_, 1);
                    v___x_6991_ = crate::leanh::lean_box(0);
                    if v_isShared_6976_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6975_, 1, v_a_6990_);
                        crate::leanh::lean_ctor_set(v___x_6975_, 0, v___x_6991_);
                        v___x_6993_ = v___x_6975_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6997_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6997_, 0, v___x_6991_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6997_, 1, v_a_6990_);
                        v___x_6993_ = v_reuseFailAlloc_6997_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6982_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6981_, 0, v___x_6985_);
                    v___x_6987_ = v___x_6981_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6988_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6988_, 0, v___x_6985_);
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
                    v_reuseFailAlloc_7005_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7005_, 0, v_a_6999_);
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
    mut v_init_7009_: *mut crate::leanh::LeanObject,
    mut v___x_7010_: *mut crate::leanh::LeanObject,
    mut v___x_7011_: *mut crate::leanh::LeanObject,
    mut v___x_7012_: *mut crate::leanh::LeanObject,
    mut v_as_7013_: *mut crate::leanh::LeanObject,
    mut v_sz_7014_: *mut crate::leanh::LeanObject,
    mut v_i_7015_: *mut crate::leanh::LeanObject,
    mut v_b_7016_: *mut crate::leanh::LeanObject,
    mut v___y_7017_: *mut crate::leanh::LeanObject,
    mut v___y_7018_: *mut crate::leanh::LeanObject,
    mut v___y_7019_: *mut crate::leanh::LeanObject,
    mut v___y_7020_: *mut crate::leanh::LeanObject,
    mut v___y_7021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_12489__boxed_7022_: u8 = 0;
    let mut v___x_12490__boxed_7023_: u8 = 0;
    let mut v___x_12491__boxed_7024_: u8 = 0;
    let mut v_sz_boxed_7025_: usize = 0;
    let mut v_i_boxed_7026_: usize = 0;
    let mut v_res_7027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_12489__boxed_7022_ = (crate::leanh::lean_unbox(v___x_7010_) as u8);
    v___x_12490__boxed_7023_ = (crate::leanh::lean_unbox(v___x_7011_) as u8);
    v___x_12491__boxed_7024_ = (crate::leanh::lean_unbox(v___x_7012_) as u8);
    v_sz_boxed_7025_ = crate::leanh::lean_unbox_usize(v_sz_7014_);
    crate::leanh::lean_dec(v_sz_7014_);
    v_i_boxed_7026_ = crate::leanh::lean_unbox_usize(v_i_7015_);
    crate::leanh::lean_dec(v_i_7015_);
    v_res_7027_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2_spec__3(v_init_7009_, v___x_12489__boxed_7022_, v___x_12490__boxed_7023_, v___x_12491__boxed_7024_, v_as_7013_, v_sz_boxed_7025_, v_i_boxed_7026_, v_b_7016_, v___y_7017_, v___y_7018_, v___y_7019_, v___y_7020_);
    crate::leanh::lean_dec(v___y_7020_);
    crate::leanh::lean_dec_ref(v___y_7019_);
    crate::leanh::lean_dec(v___y_7018_);
    crate::leanh::lean_dec_ref(v___y_7017_);
    crate::leanh::lean_dec_ref(v_as_7013_);
    crate::leanh::lean_dec_ref(v_init_7009_);
    return v_res_7027_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2___boxed(
    mut v_init_7028_: *mut crate::leanh::LeanObject,
    mut v___x_7029_: *mut crate::leanh::LeanObject,
    mut v___x_7030_: *mut crate::leanh::LeanObject,
    mut v___x_7031_: *mut crate::leanh::LeanObject,
    mut v_n_7032_: *mut crate::leanh::LeanObject,
    mut v_b_7033_: *mut crate::leanh::LeanObject,
    mut v___y_7034_: *mut crate::leanh::LeanObject,
    mut v___y_7035_: *mut crate::leanh::LeanObject,
    mut v___y_7036_: *mut crate::leanh::LeanObject,
    mut v___y_7037_: *mut crate::leanh::LeanObject,
    mut v___y_7038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_12513__boxed_7039_: u8 = 0;
    let mut v___x_12514__boxed_7040_: u8 = 0;
    let mut v___x_12515__boxed_7041_: u8 = 0;
    let mut v_res_7042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_12513__boxed_7039_ = (crate::leanh::lean_unbox(v___x_7029_) as u8);
    v___x_12514__boxed_7040_ = (crate::leanh::lean_unbox(v___x_7030_) as u8);
    v___x_12515__boxed_7041_ = (crate::leanh::lean_unbox(v___x_7031_) as u8);
    v_res_7042_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2(v_init_7028_, v___x_12513__boxed_7039_, v___x_12514__boxed_7040_, v___x_12515__boxed_7041_, v_n_7032_, v_b_7033_, v___y_7034_, v___y_7035_, v___y_7036_, v___y_7037_);
    crate::leanh::lean_dec(v___y_7037_);
    crate::leanh::lean_dec_ref(v___y_7036_);
    crate::leanh::lean_dec(v___y_7035_);
    crate::leanh::lean_dec_ref(v___y_7034_);
    crate::leanh::lean_dec_ref(v_n_7032_);
    crate::leanh::lean_dec_ref(v_init_7028_);
    return v_res_7042_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3_spec__6(
    mut v___x_7043_: u8,
    mut v___x_7044_: u8,
    mut v___x_7045_: u8,
    mut v_as_7046_: *mut crate::leanh::LeanObject,
    mut v_sz_7047_: usize,
    mut v_i_7048_: usize,
    mut v_b_7049_: *mut crate::leanh::LeanObject,
    mut v___y_7050_: *mut crate::leanh::LeanObject,
    mut v___y_7051_: *mut crate::leanh::LeanObject,
    mut v___y_7052_: *mut crate::leanh::LeanObject,
    mut v___y_7053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7055_: u8 = 0;
    let mut v___x_7056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7060_: u8 = 0;
    let mut v___x_7061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: usize = 0;
    let mut v___x_7067_: usize = 0;
    let mut v_reuseFailAlloc_7069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varNames_7072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_7073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varNames_7079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_7080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7089_: u8 = 0;
    let mut v_fst_7090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7093_: u8 = 0;
    let mut v_fst_7094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7098_: u8 = 0;
    let mut v___x_7101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7110_: u8 = 0;
    let mut v___x_7111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7120_: u8 = 0;
    let mut v___x_7122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7124_: u8 = 0;
    let mut v___x_7125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7131_: u8 = 0;
    let mut v___x_7132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7141_: u8 = 0;
    let mut v___x_7143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7145_: u8 = 0;
    let mut v___x_7146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_7151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7156_: u8 = 0;
    let mut v___x_7158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7159_: u8 = 0;
    let mut v_reuseFailAlloc_7160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7164_: u8 = 0;
    let mut v___x_7166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7168_: u8 = 0;
    let mut v_nondep_7169_: u8 = 0;
    let mut v_fvarId_7170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_7171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7194_: u8 = 0;
    let mut v___x_7196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7198_: u8 = 0;
    let mut v_reuseFailAlloc_7199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7203_: u8 = 0;
    let mut v___x_7205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7207_: u8 = 0;
    let mut v_a_7208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7211_: u8 = 0;
    let mut v___x_7213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7215_: u8 = 0;
    let mut v_a_7216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7219_: u8 = 0;
    let mut v___x_7221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7223_: u8 = 0;
    let mut v_fvarId_7224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_7225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7230_: u8 = 0;
    let mut v___x_7232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7233_: u8 = 0;
    let mut v_reuseFailAlloc_7234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7238_: u8 = 0;
    let mut v___x_7240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7242_: u8 = 0;
    let mut v___x_7244_: u8 = 0;
    let mut v___x_7245_: u8 = 0;
    let mut v_isSharedCheck_7246_: u8 = 0;
    let mut v_isSharedCheck_7247_: u8 = 0;
    let mut v_unused_7248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7249_: u8 = 0;
    let mut v_isSharedCheck_7250_: u8 = 0;
    let mut v_unused_7251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7055_ = lean_usize_dec_lt(v_i_7048_, v_sz_7047_);
                if v___x_7055_ == 0 {
                    v___x_7056_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7056_, 0, v_b_7049_);
                    return v___x_7056_;
                } else {
                    v_snd_7057_ = crate::leanh::lean_ctor_get(v_b_7049_, 1);
                    v_isSharedCheck_7250_ = (!crate::leanh::lean_is_exclusive(v_b_7049_)) as u8;
                    if v_isSharedCheck_7250_ == 0 {
                        v_unused_7251_ = crate::leanh::lean_ctor_get(v_b_7049_, 0);
                        crate::leanh::lean_dec(v_unused_7251_);
                        v___x_7059_ = v_b_7049_;
                        v_isShared_7060_ = v_isSharedCheck_7250_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_7057_);
                        crate::leanh::lean_dec(v_b_7049_);
                        v___x_7059_ = crate::leanh::lean_box(0);
                        v_isShared_7060_ = v_isSharedCheck_7250_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7061_ = crate::leanh::lean_box(0);
                v_a_7084_ = lean_array_uget(v_as_7046_, v_i_7048_);
                if crate::leanh::lean_obj_tag(v_a_7084_) == 0 {
                    v_a_7063_ = v_snd_7057_;
                    state = 2;
                    continue;
                } else {
                    v_snd_7085_ = crate::leanh::lean_ctor_get(v_snd_7057_, 1);
                    crate::leanh::lean_inc(v_snd_7085_);
                    v_val_7086_ = crate::leanh::lean_ctor_get(v_a_7084_, 0);
                    v_isSharedCheck_7249_ = (!crate::leanh::lean_is_exclusive(v_a_7084_)) as u8;
                    if v_isSharedCheck_7249_ == 0 {
                        v___x_7088_ = v_a_7084_;
                        v_isShared_7089_ = v_isSharedCheck_7249_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_7086_);
                        crate::leanh::lean_dec(v_a_7084_);
                        v___x_7088_ = crate::leanh::lean_box(0);
                        v_isShared_7089_ = v_isSharedCheck_7249_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7060_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7059_, 1, v_a_7063_);
                    crate::leanh::lean_ctor_set(v___x_7059_, 0, v___x_7061_);
                    v___x_7065_ = v___x_7059_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7069_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7069_, 0, v___x_7061_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7069_, 1, v_a_7063_);
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
                v___x_7074_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7074_, 0, v___y_7071_);
                v___x_7075_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7075_, 0, v___x_7074_);
                crate::leanh::lean_ctor_set(v___x_7075_, 1, v_hyps_7073_);
                v___x_7076_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7076_, 0, v_varNames_7072_);
                crate::leanh::lean_ctor_set(v___x_7076_, 1, v___x_7075_);
                v_a_7063_ = v___x_7076_;
                state = 2;
                continue;
            }
            5 => {
                v___x_7081_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7081_, 0, v___y_7078_);
                v___x_7082_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7082_, 0, v___x_7081_);
                crate::leanh::lean_ctor_set(v___x_7082_, 1, v_hyps_7080_);
                v___x_7083_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7083_, 0, v_varNames_7079_);
                crate::leanh::lean_ctor_set(v___x_7083_, 1, v___x_7082_);
                v_a_7063_ = v___x_7083_;
                state = 2;
                continue;
            }
            6 => {
                v_fst_7090_ = crate::leanh::lean_ctor_get(v_snd_7057_, 0);
                v_isSharedCheck_7247_ = (!crate::leanh::lean_is_exclusive(v_snd_7057_)) as u8;
                if v_isSharedCheck_7247_ == 0 {
                    v_unused_7248_ = crate::leanh::lean_ctor_get(v_snd_7057_, 1);
                    crate::leanh::lean_dec(v_unused_7248_);
                    v___x_7092_ = v_snd_7057_;
                    v_isShared_7093_ = v_isSharedCheck_7247_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_7090_);
                    crate::leanh::lean_dec(v_snd_7057_);
                    v___x_7092_ = crate::leanh::lean_box(0);
                    v_isShared_7093_ = v_isSharedCheck_7247_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_fst_7094_ = crate::leanh::lean_ctor_get(v_snd_7085_, 0);
                v_snd_7095_ = crate::leanh::lean_ctor_get(v_snd_7085_, 1);
                v_isSharedCheck_7246_ = (!crate::leanh::lean_is_exclusive(v_snd_7085_)) as u8;
                if v_isSharedCheck_7246_ == 0 {
                    v___x_7097_ = v_snd_7085_;
                    v_isShared_7098_ = v_isSharedCheck_7246_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_7095_);
                    crate::leanh::lean_inc(v_fst_7094_);
                    crate::leanh::lean_dec(v_snd_7085_);
                    v___x_7097_ = crate::leanh::lean_box(0);
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
                        crate::leanh::lean_del_object(v___x_7088_);
                        crate::leanh::lean_dec(v_val_7086_);
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
                    v_reuseFailAlloc_7105_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7105_, 0, v_fst_7094_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7105_, 1, v_snd_7095_);
                    v___x_7101_ = v_reuseFailAlloc_7105_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_7093_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7092_, 1, v___x_7101_);
                    v___x_7103_ = v___x_7092_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7104_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7104_, 0, v_fst_7090_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7104_, 1, v___x_7101_);
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
                    if crate::leanh::lean_obj_tag(v___x_7111_) == 0 {
                        v_a_7112_ = crate::leanh::lean_ctor_get(v___x_7111_, 0);
                        crate::leanh::lean_inc(v_a_7112_);
                        crate::leanh::lean_dec_ref_known(v___x_7111_, 1);
                        v___x_7113_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7113_, 0, v___y_7108_);
                        crate::leanh::lean_ctor_set(v___x_7113_, 1, v___y_7107_);
                        v___x_7114_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_7115_ = lean_mk_empty_array_with_capacity(v___x_7114_);
                        v___x_7116_ = lean_array_push(v___x_7115_, v___x_7113_);
                        v___y_7071_ = v___y_7109_;
                        v_varNames_7072_ = v___x_7116_;
                        v_hyps_7073_ = v_a_7112_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_7109_);
                        crate::leanh::lean_dec_ref(v___y_7108_);
                        crate::leanh::lean_dec(v___y_7107_);
                        crate::leanh::lean_del_object(v___x_7059_);
                        v_a_7117_ = crate::leanh::lean_ctor_get(v___x_7111_, 0);
                        v_isSharedCheck_7124_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7111_)) as u8;
                        if v_isSharedCheck_7124_ == 0 {
                            v___x_7119_ = v___x_7111_;
                            v_isShared_7120_ = v_isSharedCheck_7124_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7117_);
                            crate::leanh::lean_dec(v___x_7111_);
                            v___x_7119_ = crate::leanh::lean_box(0);
                            v_isShared_7120_ = v_isSharedCheck_7124_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_7094_);
                    v___x_7125_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7125_, 0, v___y_7108_);
                    crate::leanh::lean_ctor_set(v___x_7125_, 1, v___y_7107_);
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
                    v_reuseFailAlloc_7123_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7123_, 0, v_a_7117_);
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
                    if crate::leanh::lean_obj_tag(v___x_7132_) == 0 {
                        v_a_7133_ = crate::leanh::lean_ctor_get(v___x_7132_, 0);
                        crate::leanh::lean_inc(v_a_7133_);
                        crate::leanh::lean_dec_ref_known(v___x_7132_, 1);
                        v___x_7134_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7134_, 0, v___y_7130_);
                        crate::leanh::lean_ctor_set(v___x_7134_, 1, v___y_7128_);
                        v___x_7135_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_7136_ = lean_mk_empty_array_with_capacity(v___x_7135_);
                        v___x_7137_ = lean_array_push(v___x_7136_, v___x_7134_);
                        v___y_7078_ = v___y_7129_;
                        v_varNames_7079_ = v___x_7137_;
                        v_hyps_7080_ = v_a_7133_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_7130_);
                        crate::leanh::lean_dec_ref(v___y_7129_);
                        crate::leanh::lean_dec(v___y_7128_);
                        crate::leanh::lean_del_object(v___x_7059_);
                        v_a_7138_ = crate::leanh::lean_ctor_get(v___x_7132_, 0);
                        v_isSharedCheck_7145_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7132_)) as u8;
                        if v_isSharedCheck_7145_ == 0 {
                            v___x_7140_ = v___x_7132_;
                            v_isShared_7141_ = v_isSharedCheck_7145_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7138_);
                            crate::leanh::lean_dec(v___x_7132_);
                            v___x_7140_ = crate::leanh::lean_box(0);
                            v_isShared_7141_ = v_isSharedCheck_7145_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_7094_);
                    v___x_7146_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7146_, 0, v___y_7130_);
                    crate::leanh::lean_ctor_set(v___x_7146_, 1, v___y_7128_);
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
                    v_reuseFailAlloc_7144_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7144_, 0, v_a_7138_);
                    v___x_7143_ = v_reuseFailAlloc_7144_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_7143_;
            }
            18 => {
                if crate::leanh::lean_obj_tag(v_val_7086_) == 0 {
                    v_fvarId_7150_ = crate::leanh::lean_ctor_get(v_val_7086_, 1);
                    crate::leanh::lean_inc(v_fvarId_7150_);
                    v_userName_7151_ = crate::leanh::lean_ctor_get(v_val_7086_, 2);
                    crate::leanh::lean_inc(v_userName_7151_);
                    v_type_7152_ = crate::leanh::lean_ctor_get(v_val_7086_, 3);
                    crate::leanh::lean_inc_ref(v_type_7152_);
                    crate::leanh::lean_dec_ref_known(v_val_7086_, 4);
                    v___x_7153_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_7152_, v___y_7051_);
                    if crate::leanh::lean_obj_tag(v___x_7153_) == 0 {
                        v_a_7154_ = crate::leanh::lean_ctor_get(v___x_7153_, 0);
                        crate::leanh::lean_inc(v_a_7154_);
                        crate::leanh::lean_dec_ref_known(v___x_7153_, 1);
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
                            crate::leanh::lean_inc(v_a_7154_);
                            if v_isShared_7089_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_7088_, 0, v_a_7154_);
                                v___x_7158_ = v___x_7088_;
                                state = 19;
                                continue;
                            } else {
                                v_reuseFailAlloc_7160_ =
                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7160_, 0, v_a_7154_);
                                v___x_7158_ = v_reuseFailAlloc_7160_;
                                state = 19;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_7088_);
                            v___y_7107_ = v_fvarId_7150_;
                            v___y_7108_ = v___x_7155_;
                            v___y_7109_ = v_a_7154_;
                            v___y_7110_ = v___x_7156_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_userName_7151_);
                        crate::leanh::lean_dec(v_fvarId_7150_);
                        crate::leanh::lean_dec(v_snd_7095_);
                        crate::leanh::lean_dec(v_fst_7094_);
                        crate::leanh::lean_dec(v_fst_7090_);
                        crate::leanh::lean_del_object(v___x_7088_);
                        crate::leanh::lean_del_object(v___x_7059_);
                        v_a_7161_ = crate::leanh::lean_ctor_get(v___x_7153_, 0);
                        v_isSharedCheck_7168_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7153_)) as u8;
                        if v_isSharedCheck_7168_ == 0 {
                            v___x_7163_ = v___x_7153_;
                            v_isShared_7164_ = v_isSharedCheck_7168_;
                            state = 20;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7161_);
                            crate::leanh::lean_dec(v___x_7153_);
                            v___x_7163_ = crate::leanh::lean_box(0);
                            v_isShared_7164_ = v_isSharedCheck_7168_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    v_nondep_7169_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_7086_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    );
                    if v_nondep_7169_ == 0 {
                        v_fvarId_7170_ = crate::leanh::lean_ctor_get(v_val_7086_, 1);
                        crate::leanh::lean_inc(v_fvarId_7170_);
                        v_userName_7171_ = crate::leanh::lean_ctor_get(v_val_7086_, 2);
                        crate::leanh::lean_inc(v_userName_7171_);
                        v_type_7172_ = crate::leanh::lean_ctor_get(v_val_7086_, 3);
                        crate::leanh::lean_inc_ref(v_type_7172_);
                        v_value_7173_ = crate::leanh::lean_ctor_get(v_val_7086_, 4);
                        crate::leanh::lean_inc_ref(v_value_7173_);
                        crate::leanh::lean_dec_ref_known(v_val_7086_, 5);
                        v___x_7174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3___lam__0(v_fst_7090_, v_fst_7094_, v_snd_7095_, v___y_7050_, v___y_7051_, v___y_7052_, v___y_7053_);
                        if crate::leanh::lean_obj_tag(v___x_7174_) == 0 {
                            v_a_7175_ = crate::leanh::lean_ctor_get(v___x_7174_, 0);
                            crate::leanh::lean_inc(v_a_7175_);
                            crate::leanh::lean_dec_ref_known(v___x_7174_, 1);
                            v___x_7176_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_7172_, v___y_7051_);
                            if crate::leanh::lean_obj_tag(v___x_7176_) == 0 {
                                v_a_7177_ = crate::leanh::lean_ctor_get(v___x_7176_, 0);
                                crate::leanh::lean_inc(v_a_7177_);
                                crate::leanh::lean_dec_ref_known(v___x_7176_, 1);
                                v___x_7178_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_value_7173_, v___y_7051_);
                                if crate::leanh::lean_obj_tag(v___x_7178_) == 0 {
                                    v_a_7179_ = crate::leanh::lean_ctor_get(v___x_7178_, 0);
                                    crate::leanh::lean_inc(v_a_7179_);
                                    crate::leanh::lean_dec_ref_known(v___x_7178_, 1);
                                    v___x_7180_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_7171_, v___x_7055_);
                                    v___x_7181_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_7181_, 0, v___x_7180_);
                                    crate::leanh::lean_ctor_set(v___x_7181_, 1, v_fvarId_7170_);
                                    v___x_7182_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_7183_ = lean_mk_empty_array_with_capacity(v___x_7182_);
                                    v___x_7184_ = lean_array_push(v___x_7183_, v___x_7181_);
                                    if v_isShared_7089_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_7088_, 0, v_a_7179_);
                                        v___x_7186_ = v___x_7088_;
                                        state = 22;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_7199_ =
                                            crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7199_,
                                            0,
                                            v_a_7179_,
                                        );
                                        v___x_7186_ = v_reuseFailAlloc_7199_;
                                        state = 22;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_7177_);
                                    crate::leanh::lean_dec(v_a_7175_);
                                    crate::leanh::lean_dec(v_userName_7171_);
                                    crate::leanh::lean_dec(v_fvarId_7170_);
                                    crate::leanh::lean_del_object(v___x_7088_);
                                    crate::leanh::lean_del_object(v___x_7059_);
                                    v_a_7200_ = crate::leanh::lean_ctor_get(v___x_7178_, 0);
                                    v_isSharedCheck_7207_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_7178_)) as u8;
                                    if v_isSharedCheck_7207_ == 0 {
                                        v___x_7202_ = v___x_7178_;
                                        v_isShared_7203_ = v_isSharedCheck_7207_;
                                        state = 25;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_7200_);
                                        crate::leanh::lean_dec(v___x_7178_);
                                        v___x_7202_ = crate::leanh::lean_box(0);
                                        v_isShared_7203_ = v_isSharedCheck_7207_;
                                        state = 25;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_7175_);
                                crate::leanh::lean_dec_ref(v_value_7173_);
                                crate::leanh::lean_dec(v_userName_7171_);
                                crate::leanh::lean_dec(v_fvarId_7170_);
                                crate::leanh::lean_del_object(v___x_7088_);
                                crate::leanh::lean_del_object(v___x_7059_);
                                v_a_7208_ = crate::leanh::lean_ctor_get(v___x_7176_, 0);
                                v_isSharedCheck_7215_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7176_)) as u8;
                                if v_isSharedCheck_7215_ == 0 {
                                    v___x_7210_ = v___x_7176_;
                                    v_isShared_7211_ = v_isSharedCheck_7215_;
                                    state = 27;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_7208_);
                                    crate::leanh::lean_dec(v___x_7176_);
                                    v___x_7210_ = crate::leanh::lean_box(0);
                                    v_isShared_7211_ = v_isSharedCheck_7215_;
                                    state = 27;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_value_7173_);
                            crate::leanh::lean_dec_ref(v_type_7172_);
                            crate::leanh::lean_dec(v_userName_7171_);
                            crate::leanh::lean_dec(v_fvarId_7170_);
                            crate::leanh::lean_del_object(v___x_7088_);
                            crate::leanh::lean_del_object(v___x_7059_);
                            v_a_7216_ = crate::leanh::lean_ctor_get(v___x_7174_, 0);
                            v_isSharedCheck_7223_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7174_)) as u8;
                            if v_isSharedCheck_7223_ == 0 {
                                v___x_7218_ = v___x_7174_;
                                v_isShared_7219_ = v_isSharedCheck_7223_;
                                state = 29;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7216_);
                                crate::leanh::lean_dec(v___x_7174_);
                                v___x_7218_ = crate::leanh::lean_box(0);
                                v_isShared_7219_ = v_isSharedCheck_7223_;
                                state = 29;
                                continue;
                            }
                        }
                    } else {
                        v_fvarId_7224_ = crate::leanh::lean_ctor_get(v_val_7086_, 1);
                        crate::leanh::lean_inc(v_fvarId_7224_);
                        v_userName_7225_ = crate::leanh::lean_ctor_get(v_val_7086_, 2);
                        crate::leanh::lean_inc(v_userName_7225_);
                        v_type_7226_ = crate::leanh::lean_ctor_get(v_val_7086_, 3);
                        crate::leanh::lean_inc_ref(v_type_7226_);
                        crate::leanh::lean_dec_ref_known(v_val_7086_, 5);
                        v___x_7227_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_7226_, v___y_7051_);
                        if crate::leanh::lean_obj_tag(v___x_7227_) == 0 {
                            v_a_7228_ = crate::leanh::lean_ctor_get(v___x_7227_, 0);
                            crate::leanh::lean_inc(v_a_7228_);
                            crate::leanh::lean_dec_ref_known(v___x_7227_, 1);
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
                                crate::leanh::lean_inc(v_a_7228_);
                                if v_isShared_7089_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_7088_, 0, v_a_7228_);
                                    v___x_7232_ = v___x_7088_;
                                    state = 31;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_7234_ =
                                        crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7234_,
                                        0,
                                        v_a_7228_,
                                    );
                                    v___x_7232_ = v_reuseFailAlloc_7234_;
                                    state = 31;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_7088_);
                                v___y_7128_ = v_fvarId_7224_;
                                v___y_7129_ = v_a_7228_;
                                v___y_7130_ = v___x_7229_;
                                v___y_7131_ = v___x_7230_;
                                state = 15;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_userName_7225_);
                            crate::leanh::lean_dec(v_fvarId_7224_);
                            crate::leanh::lean_dec(v_snd_7095_);
                            crate::leanh::lean_dec(v_fst_7094_);
                            crate::leanh::lean_dec(v_fst_7090_);
                            crate::leanh::lean_del_object(v___x_7088_);
                            crate::leanh::lean_del_object(v___x_7059_);
                            v_a_7235_ = crate::leanh::lean_ctor_get(v___x_7227_, 0);
                            v_isSharedCheck_7242_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7227_)) as u8;
                            if v_isSharedCheck_7242_ == 0 {
                                v___x_7237_ = v___x_7227_;
                                v_isShared_7238_ = v_isSharedCheck_7242_;
                                state = 32;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7235_);
                                crate::leanh::lean_dec(v___x_7227_);
                                v___x_7237_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_dec_ref(v___x_7158_);
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
                    v_reuseFailAlloc_7167_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7167_, 0, v_a_7161_);
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
                if crate::leanh::lean_obj_tag(v___x_7187_) == 0 {
                    v_a_7188_ = crate::leanh::lean_ctor_get(v___x_7187_, 0);
                    crate::leanh::lean_inc(v_a_7188_);
                    crate::leanh::lean_dec_ref_known(v___x_7187_, 1);
                    v___x_7189_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7189_, 0, v___x_7061_);
                    crate::leanh::lean_ctor_set(v___x_7189_, 1, v_a_7188_);
                    v___x_7190_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7190_, 0, v___x_7148_);
                    crate::leanh::lean_ctor_set(v___x_7190_, 1, v___x_7189_);
                    v_a_7063_ = v___x_7190_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_7059_);
                    v_a_7191_ = crate::leanh::lean_ctor_get(v___x_7187_, 0);
                    v_isSharedCheck_7198_ = (!crate::leanh::lean_is_exclusive(v___x_7187_)) as u8;
                    if v_isSharedCheck_7198_ == 0 {
                        v___x_7193_ = v___x_7187_;
                        v_isShared_7194_ = v_isSharedCheck_7198_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7191_);
                        crate::leanh::lean_dec(v___x_7187_);
                        v___x_7193_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_7197_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7197_, 0, v_a_7191_);
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
                    v_reuseFailAlloc_7206_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7206_, 0, v_a_7200_);
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
                    v_reuseFailAlloc_7214_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7214_, 0, v_a_7208_);
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
                    v_reuseFailAlloc_7222_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7222_, 0, v_a_7216_);
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
                crate::leanh::lean_dec_ref(v___x_7232_);
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
                    v_reuseFailAlloc_7241_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7241_, 0, v_a_7235_);
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
                        crate::leanh::lean_del_object(v___x_7097_);
                        crate::leanh::lean_del_object(v___x_7092_);
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_7088_);
                        crate::leanh::lean_dec(v_val_7086_);
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7097_);
                    crate::leanh::lean_del_object(v___x_7092_);
                    state = 18;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3_spec__6___boxed(
    mut v___x_7252_: *mut crate::leanh::LeanObject,
    mut v___x_7253_: *mut crate::leanh::LeanObject,
    mut v___x_7254_: *mut crate::leanh::LeanObject,
    mut v_as_7255_: *mut crate::leanh::LeanObject,
    mut v_sz_7256_: *mut crate::leanh::LeanObject,
    mut v_i_7257_: *mut crate::leanh::LeanObject,
    mut v_b_7258_: *mut crate::leanh::LeanObject,
    mut v___y_7259_: *mut crate::leanh::LeanObject,
    mut v___y_7260_: *mut crate::leanh::LeanObject,
    mut v___y_7261_: *mut crate::leanh::LeanObject,
    mut v___y_7262_: *mut crate::leanh::LeanObject,
    mut v___y_7263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_12716__boxed_7264_: u8 = 0;
    let mut v___x_12717__boxed_7265_: u8 = 0;
    let mut v___x_12718__boxed_7266_: u8 = 0;
    let mut v_sz_boxed_7267_: usize = 0;
    let mut v_i_boxed_7268_: usize = 0;
    let mut v_res_7269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_12716__boxed_7264_ = (crate::leanh::lean_unbox(v___x_7252_) as u8);
    v___x_12717__boxed_7265_ = (crate::leanh::lean_unbox(v___x_7253_) as u8);
    v___x_12718__boxed_7266_ = (crate::leanh::lean_unbox(v___x_7254_) as u8);
    v_sz_boxed_7267_ = crate::leanh::lean_unbox_usize(v_sz_7256_);
    crate::leanh::lean_dec(v_sz_7256_);
    v_i_boxed_7268_ = crate::leanh::lean_unbox_usize(v_i_7257_);
    crate::leanh::lean_dec(v_i_7257_);
    v_res_7269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3_spec__6(v___x_12716__boxed_7264_, v___x_12717__boxed_7265_, v___x_12718__boxed_7266_, v_as_7255_, v_sz_boxed_7267_, v_i_boxed_7268_, v_b_7258_, v___y_7259_, v___y_7260_, v___y_7261_, v___y_7262_);
    crate::leanh::lean_dec(v___y_7262_);
    crate::leanh::lean_dec_ref(v___y_7261_);
    crate::leanh::lean_dec(v___y_7260_);
    crate::leanh::lean_dec_ref(v___y_7259_);
    crate::leanh::lean_dec_ref(v_as_7255_);
    return v_res_7269_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3(
    mut v___x_7270_: u8,
    mut v___x_7271_: u8,
    mut v___x_7272_: u8,
    mut v_as_7273_: *mut crate::leanh::LeanObject,
    mut v_sz_7274_: usize,
    mut v_i_7275_: usize,
    mut v_b_7276_: *mut crate::leanh::LeanObject,
    mut v___y_7277_: *mut crate::leanh::LeanObject,
    mut v___y_7278_: *mut crate::leanh::LeanObject,
    mut v___y_7279_: *mut crate::leanh::LeanObject,
    mut v___y_7280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7282_: u8 = 0;
    let mut v___x_7283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7287_: u8 = 0;
    let mut v___x_7288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7293_: usize = 0;
    let mut v___x_7294_: usize = 0;
    let mut v___x_7295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varNames_7299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_7300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varNames_7306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_7307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7316_: u8 = 0;
    let mut v_fst_7317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7320_: u8 = 0;
    let mut v_fst_7321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7325_: u8 = 0;
    let mut v___x_7328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7337_: u8 = 0;
    let mut v___x_7338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7347_: u8 = 0;
    let mut v___x_7349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7351_: u8 = 0;
    let mut v___x_7352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7358_: u8 = 0;
    let mut v___x_7359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7368_: u8 = 0;
    let mut v___x_7370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7372_: u8 = 0;
    let mut v___x_7373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_7377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_7378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7383_: u8 = 0;
    let mut v___x_7385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7386_: u8 = 0;
    let mut v_reuseFailAlloc_7387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7391_: u8 = 0;
    let mut v___x_7393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7395_: u8 = 0;
    let mut v_nondep_7396_: u8 = 0;
    let mut v_fvarId_7397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_7398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7421_: u8 = 0;
    let mut v___x_7423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7425_: u8 = 0;
    let mut v_reuseFailAlloc_7426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7430_: u8 = 0;
    let mut v___x_7432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7434_: u8 = 0;
    let mut v_a_7435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7438_: u8 = 0;
    let mut v___x_7440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7442_: u8 = 0;
    let mut v_a_7443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7446_: u8 = 0;
    let mut v___x_7448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7450_: u8 = 0;
    let mut v_fvarId_7451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_7452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7457_: u8 = 0;
    let mut v___x_7459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7460_: u8 = 0;
    let mut v_reuseFailAlloc_7461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7465_: u8 = 0;
    let mut v___x_7467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7469_: u8 = 0;
    let mut v___x_7471_: u8 = 0;
    let mut v___x_7472_: u8 = 0;
    let mut v_isSharedCheck_7473_: u8 = 0;
    let mut v_isSharedCheck_7474_: u8 = 0;
    let mut v_unused_7475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7476_: u8 = 0;
    let mut v_isSharedCheck_7477_: u8 = 0;
    let mut v_unused_7478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7282_ = lean_usize_dec_lt(v_i_7275_, v_sz_7274_);
                if v___x_7282_ == 0 {
                    v___x_7283_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7283_, 0, v_b_7276_);
                    return v___x_7283_;
                } else {
                    v_snd_7284_ = crate::leanh::lean_ctor_get(v_b_7276_, 1);
                    v_isSharedCheck_7477_ = (!crate::leanh::lean_is_exclusive(v_b_7276_)) as u8;
                    if v_isSharedCheck_7477_ == 0 {
                        v_unused_7478_ = crate::leanh::lean_ctor_get(v_b_7276_, 0);
                        crate::leanh::lean_dec(v_unused_7478_);
                        v___x_7286_ = v_b_7276_;
                        v_isShared_7287_ = v_isSharedCheck_7477_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_7284_);
                        crate::leanh::lean_dec(v_b_7276_);
                        v___x_7286_ = crate::leanh::lean_box(0);
                        v_isShared_7287_ = v_isSharedCheck_7477_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7288_ = crate::leanh::lean_box(0);
                v_a_7311_ = lean_array_uget(v_as_7273_, v_i_7275_);
                if crate::leanh::lean_obj_tag(v_a_7311_) == 0 {
                    v_a_7290_ = v_snd_7284_;
                    state = 2;
                    continue;
                } else {
                    v_snd_7312_ = crate::leanh::lean_ctor_get(v_snd_7284_, 1);
                    crate::leanh::lean_inc(v_snd_7312_);
                    v_val_7313_ = crate::leanh::lean_ctor_get(v_a_7311_, 0);
                    v_isSharedCheck_7476_ = (!crate::leanh::lean_is_exclusive(v_a_7311_)) as u8;
                    if v_isSharedCheck_7476_ == 0 {
                        v___x_7315_ = v_a_7311_;
                        v_isShared_7316_ = v_isSharedCheck_7476_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_7313_);
                        crate::leanh::lean_dec(v_a_7311_);
                        v___x_7315_ = crate::leanh::lean_box(0);
                        v_isShared_7316_ = v_isSharedCheck_7476_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7287_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7286_, 1, v_a_7290_);
                    crate::leanh::lean_ctor_set(v___x_7286_, 0, v___x_7288_);
                    v___x_7292_ = v___x_7286_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7296_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7296_, 0, v___x_7288_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7296_, 1, v_a_7290_);
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
                v___x_7301_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7301_, 0, v___y_7298_);
                v___x_7302_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7302_, 0, v___x_7301_);
                crate::leanh::lean_ctor_set(v___x_7302_, 1, v_hyps_7300_);
                v___x_7303_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7303_, 0, v_varNames_7299_);
                crate::leanh::lean_ctor_set(v___x_7303_, 1, v___x_7302_);
                v_a_7290_ = v___x_7303_;
                state = 2;
                continue;
            }
            5 => {
                v___x_7308_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7308_, 0, v___y_7305_);
                v___x_7309_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7309_, 0, v___x_7308_);
                crate::leanh::lean_ctor_set(v___x_7309_, 1, v_hyps_7307_);
                v___x_7310_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7310_, 0, v_varNames_7306_);
                crate::leanh::lean_ctor_set(v___x_7310_, 1, v___x_7309_);
                v_a_7290_ = v___x_7310_;
                state = 2;
                continue;
            }
            6 => {
                v_fst_7317_ = crate::leanh::lean_ctor_get(v_snd_7284_, 0);
                v_isSharedCheck_7474_ = (!crate::leanh::lean_is_exclusive(v_snd_7284_)) as u8;
                if v_isSharedCheck_7474_ == 0 {
                    v_unused_7475_ = crate::leanh::lean_ctor_get(v_snd_7284_, 1);
                    crate::leanh::lean_dec(v_unused_7475_);
                    v___x_7319_ = v_snd_7284_;
                    v_isShared_7320_ = v_isSharedCheck_7474_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_7317_);
                    crate::leanh::lean_dec(v_snd_7284_);
                    v___x_7319_ = crate::leanh::lean_box(0);
                    v_isShared_7320_ = v_isSharedCheck_7474_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_fst_7321_ = crate::leanh::lean_ctor_get(v_snd_7312_, 0);
                v_snd_7322_ = crate::leanh::lean_ctor_get(v_snd_7312_, 1);
                v_isSharedCheck_7473_ = (!crate::leanh::lean_is_exclusive(v_snd_7312_)) as u8;
                if v_isSharedCheck_7473_ == 0 {
                    v___x_7324_ = v_snd_7312_;
                    v_isShared_7325_ = v_isSharedCheck_7473_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_7322_);
                    crate::leanh::lean_inc(v_fst_7321_);
                    crate::leanh::lean_dec(v_snd_7312_);
                    v___x_7324_ = crate::leanh::lean_box(0);
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
                        crate::leanh::lean_del_object(v___x_7315_);
                        crate::leanh::lean_dec(v_val_7313_);
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
                    v_reuseFailAlloc_7332_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7332_, 0, v_fst_7321_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7332_, 1, v_snd_7322_);
                    v___x_7328_ = v_reuseFailAlloc_7332_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_7320_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7319_, 1, v___x_7328_);
                    v___x_7330_ = v___x_7319_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7331_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7331_, 0, v_fst_7317_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7331_, 1, v___x_7328_);
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
                    if crate::leanh::lean_obj_tag(v___x_7338_) == 0 {
                        v_a_7339_ = crate::leanh::lean_ctor_get(v___x_7338_, 0);
                        crate::leanh::lean_inc(v_a_7339_);
                        crate::leanh::lean_dec_ref_known(v___x_7338_, 1);
                        v___x_7340_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7340_, 0, v___y_7335_);
                        crate::leanh::lean_ctor_set(v___x_7340_, 1, v___y_7334_);
                        v___x_7341_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_7342_ = lean_mk_empty_array_with_capacity(v___x_7341_);
                        v___x_7343_ = lean_array_push(v___x_7342_, v___x_7340_);
                        v___y_7298_ = v___y_7336_;
                        v_varNames_7299_ = v___x_7343_;
                        v_hyps_7300_ = v_a_7339_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_7336_);
                        crate::leanh::lean_dec_ref(v___y_7335_);
                        crate::leanh::lean_dec(v___y_7334_);
                        crate::leanh::lean_del_object(v___x_7286_);
                        v_a_7344_ = crate::leanh::lean_ctor_get(v___x_7338_, 0);
                        v_isSharedCheck_7351_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7338_)) as u8;
                        if v_isSharedCheck_7351_ == 0 {
                            v___x_7346_ = v___x_7338_;
                            v_isShared_7347_ = v_isSharedCheck_7351_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7344_);
                            crate::leanh::lean_dec(v___x_7338_);
                            v___x_7346_ = crate::leanh::lean_box(0);
                            v_isShared_7347_ = v_isSharedCheck_7351_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_7321_);
                    v___x_7352_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7352_, 0, v___y_7335_);
                    crate::leanh::lean_ctor_set(v___x_7352_, 1, v___y_7334_);
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
                    v_reuseFailAlloc_7350_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7350_, 0, v_a_7344_);
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
                    if crate::leanh::lean_obj_tag(v___x_7359_) == 0 {
                        v_a_7360_ = crate::leanh::lean_ctor_get(v___x_7359_, 0);
                        crate::leanh::lean_inc(v_a_7360_);
                        crate::leanh::lean_dec_ref_known(v___x_7359_, 1);
                        v___x_7361_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7361_, 0, v___y_7357_);
                        crate::leanh::lean_ctor_set(v___x_7361_, 1, v___y_7355_);
                        v___x_7362_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_7363_ = lean_mk_empty_array_with_capacity(v___x_7362_);
                        v___x_7364_ = lean_array_push(v___x_7363_, v___x_7361_);
                        v___y_7305_ = v___y_7356_;
                        v_varNames_7306_ = v___x_7364_;
                        v_hyps_7307_ = v_a_7360_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_7357_);
                        crate::leanh::lean_dec_ref(v___y_7356_);
                        crate::leanh::lean_dec(v___y_7355_);
                        crate::leanh::lean_del_object(v___x_7286_);
                        v_a_7365_ = crate::leanh::lean_ctor_get(v___x_7359_, 0);
                        v_isSharedCheck_7372_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7359_)) as u8;
                        if v_isSharedCheck_7372_ == 0 {
                            v___x_7367_ = v___x_7359_;
                            v_isShared_7368_ = v_isSharedCheck_7372_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7365_);
                            crate::leanh::lean_dec(v___x_7359_);
                            v___x_7367_ = crate::leanh::lean_box(0);
                            v_isShared_7368_ = v_isSharedCheck_7372_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_7321_);
                    v___x_7373_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7373_, 0, v___y_7357_);
                    crate::leanh::lean_ctor_set(v___x_7373_, 1, v___y_7355_);
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
                    v_reuseFailAlloc_7371_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7371_, 0, v_a_7365_);
                    v___x_7370_ = v_reuseFailAlloc_7371_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_7370_;
            }
            18 => {
                if crate::leanh::lean_obj_tag(v_val_7313_) == 0 {
                    v_fvarId_7377_ = crate::leanh::lean_ctor_get(v_val_7313_, 1);
                    crate::leanh::lean_inc(v_fvarId_7377_);
                    v_userName_7378_ = crate::leanh::lean_ctor_get(v_val_7313_, 2);
                    crate::leanh::lean_inc(v_userName_7378_);
                    v_type_7379_ = crate::leanh::lean_ctor_get(v_val_7313_, 3);
                    crate::leanh::lean_inc_ref(v_type_7379_);
                    crate::leanh::lean_dec_ref_known(v_val_7313_, 4);
                    v___x_7380_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_7379_, v___y_7278_);
                    if crate::leanh::lean_obj_tag(v___x_7380_) == 0 {
                        v_a_7381_ = crate::leanh::lean_ctor_get(v___x_7380_, 0);
                        crate::leanh::lean_inc(v_a_7381_);
                        crate::leanh::lean_dec_ref_known(v___x_7380_, 1);
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
                            crate::leanh::lean_inc(v_a_7381_);
                            if v_isShared_7316_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_7315_, 0, v_a_7381_);
                                v___x_7385_ = v___x_7315_;
                                state = 19;
                                continue;
                            } else {
                                v_reuseFailAlloc_7387_ =
                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_7387_, 0, v_a_7381_);
                                v___x_7385_ = v_reuseFailAlloc_7387_;
                                state = 19;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_7315_);
                            v___y_7334_ = v_fvarId_7377_;
                            v___y_7335_ = v___x_7382_;
                            v___y_7336_ = v_a_7381_;
                            v___y_7337_ = v___x_7383_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_userName_7378_);
                        crate::leanh::lean_dec(v_fvarId_7377_);
                        crate::leanh::lean_dec(v_snd_7322_);
                        crate::leanh::lean_dec(v_fst_7321_);
                        crate::leanh::lean_dec(v_fst_7317_);
                        crate::leanh::lean_del_object(v___x_7315_);
                        crate::leanh::lean_del_object(v___x_7286_);
                        v_a_7388_ = crate::leanh::lean_ctor_get(v___x_7380_, 0);
                        v_isSharedCheck_7395_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7380_)) as u8;
                        if v_isSharedCheck_7395_ == 0 {
                            v___x_7390_ = v___x_7380_;
                            v_isShared_7391_ = v_isSharedCheck_7395_;
                            state = 20;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7388_);
                            crate::leanh::lean_dec(v___x_7380_);
                            v___x_7390_ = crate::leanh::lean_box(0);
                            v_isShared_7391_ = v_isSharedCheck_7395_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    v_nondep_7396_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_7313_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    );
                    if v_nondep_7396_ == 0 {
                        v_fvarId_7397_ = crate::leanh::lean_ctor_get(v_val_7313_, 1);
                        crate::leanh::lean_inc(v_fvarId_7397_);
                        v_userName_7398_ = crate::leanh::lean_ctor_get(v_val_7313_, 2);
                        crate::leanh::lean_inc(v_userName_7398_);
                        v_type_7399_ = crate::leanh::lean_ctor_get(v_val_7313_, 3);
                        crate::leanh::lean_inc_ref(v_type_7399_);
                        v_value_7400_ = crate::leanh::lean_ctor_get(v_val_7313_, 4);
                        crate::leanh::lean_inc_ref(v_value_7400_);
                        crate::leanh::lean_dec_ref_known(v_val_7313_, 5);
                        v___x_7401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3___lam__0(v_fst_7317_, v_fst_7321_, v_snd_7322_, v___y_7277_, v___y_7278_, v___y_7279_, v___y_7280_);
                        if crate::leanh::lean_obj_tag(v___x_7401_) == 0 {
                            v_a_7402_ = crate::leanh::lean_ctor_get(v___x_7401_, 0);
                            crate::leanh::lean_inc(v_a_7402_);
                            crate::leanh::lean_dec_ref_known(v___x_7401_, 1);
                            v___x_7403_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_7399_, v___y_7278_);
                            if crate::leanh::lean_obj_tag(v___x_7403_) == 0 {
                                v_a_7404_ = crate::leanh::lean_ctor_get(v___x_7403_, 0);
                                crate::leanh::lean_inc(v_a_7404_);
                                crate::leanh::lean_dec_ref_known(v___x_7403_, 1);
                                v___x_7405_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_value_7400_, v___y_7278_);
                                if crate::leanh::lean_obj_tag(v___x_7405_) == 0 {
                                    v_a_7406_ = crate::leanh::lean_ctor_get(v___x_7405_, 0);
                                    crate::leanh::lean_inc(v_a_7406_);
                                    crate::leanh::lean_dec_ref_known(v___x_7405_, 1);
                                    v___x_7407_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_userName_7398_, v___x_7282_);
                                    v___x_7408_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_7408_, 0, v___x_7407_);
                                    crate::leanh::lean_ctor_set(v___x_7408_, 1, v_fvarId_7397_);
                                    v___x_7409_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_7410_ = lean_mk_empty_array_with_capacity(v___x_7409_);
                                    v___x_7411_ = lean_array_push(v___x_7410_, v___x_7408_);
                                    if v_isShared_7316_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_7315_, 0, v_a_7406_);
                                        v___x_7413_ = v___x_7315_;
                                        state = 22;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_7426_ =
                                            crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7426_,
                                            0,
                                            v_a_7406_,
                                        );
                                        v___x_7413_ = v_reuseFailAlloc_7426_;
                                        state = 22;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_7404_);
                                    crate::leanh::lean_dec(v_a_7402_);
                                    crate::leanh::lean_dec(v_userName_7398_);
                                    crate::leanh::lean_dec(v_fvarId_7397_);
                                    crate::leanh::lean_del_object(v___x_7315_);
                                    crate::leanh::lean_del_object(v___x_7286_);
                                    v_a_7427_ = crate::leanh::lean_ctor_get(v___x_7405_, 0);
                                    v_isSharedCheck_7434_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_7405_)) as u8;
                                    if v_isSharedCheck_7434_ == 0 {
                                        v___x_7429_ = v___x_7405_;
                                        v_isShared_7430_ = v_isSharedCheck_7434_;
                                        state = 25;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_7427_);
                                        crate::leanh::lean_dec(v___x_7405_);
                                        v___x_7429_ = crate::leanh::lean_box(0);
                                        v_isShared_7430_ = v_isSharedCheck_7434_;
                                        state = 25;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_7402_);
                                crate::leanh::lean_dec_ref(v_value_7400_);
                                crate::leanh::lean_dec(v_userName_7398_);
                                crate::leanh::lean_dec(v_fvarId_7397_);
                                crate::leanh::lean_del_object(v___x_7315_);
                                crate::leanh::lean_del_object(v___x_7286_);
                                v_a_7435_ = crate::leanh::lean_ctor_get(v___x_7403_, 0);
                                v_isSharedCheck_7442_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7403_)) as u8;
                                if v_isSharedCheck_7442_ == 0 {
                                    v___x_7437_ = v___x_7403_;
                                    v_isShared_7438_ = v_isSharedCheck_7442_;
                                    state = 27;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_7435_);
                                    crate::leanh::lean_dec(v___x_7403_);
                                    v___x_7437_ = crate::leanh::lean_box(0);
                                    v_isShared_7438_ = v_isSharedCheck_7442_;
                                    state = 27;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_value_7400_);
                            crate::leanh::lean_dec_ref(v_type_7399_);
                            crate::leanh::lean_dec(v_userName_7398_);
                            crate::leanh::lean_dec(v_fvarId_7397_);
                            crate::leanh::lean_del_object(v___x_7315_);
                            crate::leanh::lean_del_object(v___x_7286_);
                            v_a_7443_ = crate::leanh::lean_ctor_get(v___x_7401_, 0);
                            v_isSharedCheck_7450_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7401_)) as u8;
                            if v_isSharedCheck_7450_ == 0 {
                                v___x_7445_ = v___x_7401_;
                                v_isShared_7446_ = v_isSharedCheck_7450_;
                                state = 29;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7443_);
                                crate::leanh::lean_dec(v___x_7401_);
                                v___x_7445_ = crate::leanh::lean_box(0);
                                v_isShared_7446_ = v_isSharedCheck_7450_;
                                state = 29;
                                continue;
                            }
                        }
                    } else {
                        v_fvarId_7451_ = crate::leanh::lean_ctor_get(v_val_7313_, 1);
                        crate::leanh::lean_inc(v_fvarId_7451_);
                        v_userName_7452_ = crate::leanh::lean_ctor_get(v_val_7313_, 2);
                        crate::leanh::lean_inc(v_userName_7452_);
                        v_type_7453_ = crate::leanh::lean_ctor_get(v_val_7313_, 3);
                        crate::leanh::lean_inc_ref(v_type_7453_);
                        crate::leanh::lean_dec_ref_known(v_val_7313_, 5);
                        v___x_7454_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_7453_, v___y_7278_);
                        if crate::leanh::lean_obj_tag(v___x_7454_) == 0 {
                            v_a_7455_ = crate::leanh::lean_ctor_get(v___x_7454_, 0);
                            crate::leanh::lean_inc(v_a_7455_);
                            crate::leanh::lean_dec_ref_known(v___x_7454_, 1);
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
                                crate::leanh::lean_inc(v_a_7455_);
                                if v_isShared_7316_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_7315_, 0, v_a_7455_);
                                    v___x_7459_ = v___x_7315_;
                                    state = 31;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_7461_ =
                                        crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_7461_,
                                        0,
                                        v_a_7455_,
                                    );
                                    v___x_7459_ = v_reuseFailAlloc_7461_;
                                    state = 31;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_7315_);
                                v___y_7355_ = v_fvarId_7451_;
                                v___y_7356_ = v_a_7455_;
                                v___y_7357_ = v___x_7456_;
                                v___y_7358_ = v___x_7457_;
                                state = 15;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_userName_7452_);
                            crate::leanh::lean_dec(v_fvarId_7451_);
                            crate::leanh::lean_dec(v_snd_7322_);
                            crate::leanh::lean_dec(v_fst_7321_);
                            crate::leanh::lean_dec(v_fst_7317_);
                            crate::leanh::lean_del_object(v___x_7315_);
                            crate::leanh::lean_del_object(v___x_7286_);
                            v_a_7462_ = crate::leanh::lean_ctor_get(v___x_7454_, 0);
                            v_isSharedCheck_7469_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7454_)) as u8;
                            if v_isSharedCheck_7469_ == 0 {
                                v___x_7464_ = v___x_7454_;
                                v_isShared_7465_ = v_isSharedCheck_7469_;
                                state = 32;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7462_);
                                crate::leanh::lean_dec(v___x_7454_);
                                v___x_7464_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_dec_ref(v___x_7385_);
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
                    v_reuseFailAlloc_7394_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7394_, 0, v_a_7388_);
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
                if crate::leanh::lean_obj_tag(v___x_7414_) == 0 {
                    v_a_7415_ = crate::leanh::lean_ctor_get(v___x_7414_, 0);
                    crate::leanh::lean_inc(v_a_7415_);
                    crate::leanh::lean_dec_ref_known(v___x_7414_, 1);
                    v___x_7416_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7416_, 0, v___x_7288_);
                    crate::leanh::lean_ctor_set(v___x_7416_, 1, v_a_7415_);
                    v___x_7417_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7417_, 0, v___x_7375_);
                    crate::leanh::lean_ctor_set(v___x_7417_, 1, v___x_7416_);
                    v_a_7290_ = v___x_7417_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_7286_);
                    v_a_7418_ = crate::leanh::lean_ctor_get(v___x_7414_, 0);
                    v_isSharedCheck_7425_ = (!crate::leanh::lean_is_exclusive(v___x_7414_)) as u8;
                    if v_isSharedCheck_7425_ == 0 {
                        v___x_7420_ = v___x_7414_;
                        v_isShared_7421_ = v_isSharedCheck_7425_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7418_);
                        crate::leanh::lean_dec(v___x_7414_);
                        v___x_7420_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_7424_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7424_, 0, v_a_7418_);
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
                    v_reuseFailAlloc_7433_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7433_, 0, v_a_7427_);
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
                    v_reuseFailAlloc_7441_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7441_, 0, v_a_7435_);
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
                    v_reuseFailAlloc_7449_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7449_, 0, v_a_7443_);
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
                crate::leanh::lean_dec_ref(v___x_7459_);
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
                    v_reuseFailAlloc_7468_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7468_, 0, v_a_7462_);
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
                        crate::leanh::lean_del_object(v___x_7324_);
                        crate::leanh::lean_del_object(v___x_7319_);
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_7315_);
                        crate::leanh::lean_dec(v_val_7313_);
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7324_);
                    crate::leanh::lean_del_object(v___x_7319_);
                    state = 18;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3___boxed(
    mut v___x_7479_: *mut crate::leanh::LeanObject,
    mut v___x_7480_: *mut crate::leanh::LeanObject,
    mut v___x_7481_: *mut crate::leanh::LeanObject,
    mut v_as_7482_: *mut crate::leanh::LeanObject,
    mut v_sz_7483_: *mut crate::leanh::LeanObject,
    mut v_i_7484_: *mut crate::leanh::LeanObject,
    mut v_b_7485_: *mut crate::leanh::LeanObject,
    mut v___y_7486_: *mut crate::leanh::LeanObject,
    mut v___y_7487_: *mut crate::leanh::LeanObject,
    mut v___y_7488_: *mut crate::leanh::LeanObject,
    mut v___y_7489_: *mut crate::leanh::LeanObject,
    mut v___y_7490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_13120__boxed_7491_: u8 = 0;
    let mut v___x_13121__boxed_7492_: u8 = 0;
    let mut v___x_13122__boxed_7493_: u8 = 0;
    let mut v_sz_boxed_7494_: usize = 0;
    let mut v_i_boxed_7495_: usize = 0;
    let mut v_res_7496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_13120__boxed_7491_ = (crate::leanh::lean_unbox(v___x_7479_) as u8);
    v___x_13121__boxed_7492_ = (crate::leanh::lean_unbox(v___x_7480_) as u8);
    v___x_13122__boxed_7493_ = (crate::leanh::lean_unbox(v___x_7481_) as u8);
    v_sz_boxed_7494_ = crate::leanh::lean_unbox_usize(v_sz_7483_);
    crate::leanh::lean_dec(v_sz_7483_);
    v_i_boxed_7495_ = crate::leanh::lean_unbox_usize(v_i_7484_);
    crate::leanh::lean_dec(v_i_7484_);
    v_res_7496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3(v___x_13120__boxed_7491_, v___x_13121__boxed_7492_, v___x_13122__boxed_7493_, v_as_7482_, v_sz_boxed_7494_, v_i_boxed_7495_, v_b_7485_, v___y_7486_, v___y_7487_, v___y_7488_, v___y_7489_);
    crate::leanh::lean_dec(v___y_7489_);
    crate::leanh::lean_dec_ref(v___y_7488_);
    crate::leanh::lean_dec(v___y_7487_);
    crate::leanh::lean_dec_ref(v___y_7486_);
    crate::leanh::lean_dec_ref(v_as_7482_);
    return v_res_7496_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2(
    mut v___x_7497_: u8,
    mut v___x_7498_: u8,
    mut v___x_7499_: u8,
    mut v_t_7500_: *mut crate::leanh::LeanObject,
    mut v_init_7501_: *mut crate::leanh::LeanObject,
    mut v___y_7502_: *mut crate::leanh::LeanObject,
    mut v___y_7503_: *mut crate::leanh::LeanObject,
    mut v___y_7504_: *mut crate::leanh::LeanObject,
    mut v___y_7505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_7507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7513_: u8 = 0;
    let mut v_a_7514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7521_: usize = 0;
    let mut v___x_7522_: usize = 0;
    let mut v___x_7523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7527_: u8 = 0;
    let mut v_fst_7528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7537_: u8 = 0;
    let mut v_a_7538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7541_: u8 = 0;
    let mut v___x_7543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7545_: u8 = 0;
    let mut v_isSharedCheck_7546_: u8 = 0;
    let mut v_a_7547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7550_: u8 = 0;
    let mut v___x_7552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7554_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_7507_ = crate::leanh::lean_ctor_get(v_t_7500_, 0);
                v_tail_7508_ = crate::leanh::lean_ctor_get(v_t_7500_, 1);
                crate::leanh::lean_inc_ref(v_init_7501_);
                v___x_7509_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__2(v_init_7501_, v___x_7497_, v___x_7498_, v___x_7499_, v_root_7507_, v_init_7501_, v___y_7502_, v___y_7503_, v___y_7504_, v___y_7505_);
                crate::leanh::lean_dec_ref(v_init_7501_);
                if crate::leanh::lean_obj_tag(v___x_7509_) == 0 {
                    v_a_7510_ = crate::leanh::lean_ctor_get(v___x_7509_, 0);
                    v_isSharedCheck_7546_ = (!crate::leanh::lean_is_exclusive(v___x_7509_)) as u8;
                    if v_isSharedCheck_7546_ == 0 {
                        v___x_7512_ = v___x_7509_;
                        v_isShared_7513_ = v_isSharedCheck_7546_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7510_);
                        crate::leanh::lean_dec(v___x_7509_);
                        v___x_7512_ = crate::leanh::lean_box(0);
                        v_isShared_7513_ = v_isSharedCheck_7546_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7547_ = crate::leanh::lean_ctor_get(v___x_7509_, 0);
                    v_isSharedCheck_7554_ = (!crate::leanh::lean_is_exclusive(v___x_7509_)) as u8;
                    if v_isSharedCheck_7554_ == 0 {
                        v___x_7549_ = v___x_7509_;
                        v_isShared_7550_ = v_isSharedCheck_7554_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7547_);
                        crate::leanh::lean_dec(v___x_7509_);
                        v___x_7549_ = crate::leanh::lean_box(0);
                        v_isShared_7550_ = v_isSharedCheck_7554_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_7510_) == 0 {
                    v_a_7514_ = crate::leanh::lean_ctor_get(v_a_7510_, 0);
                    crate::leanh::lean_inc(v_a_7514_);
                    crate::leanh::lean_dec_ref_known(v_a_7510_, 1);
                    if v_isShared_7513_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7512_, 0, v_a_7514_);
                        v___x_7516_ = v___x_7512_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7517_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7517_, 0, v_a_7514_);
                        v___x_7516_ = v_reuseFailAlloc_7517_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7512_);
                    v_a_7518_ = crate::leanh::lean_ctor_get(v_a_7510_, 0);
                    crate::leanh::lean_inc(v_a_7518_);
                    crate::leanh::lean_dec_ref_known(v_a_7510_, 1);
                    v___x_7519_ = crate::leanh::lean_box(0);
                    v___x_7520_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7520_, 0, v___x_7519_);
                    crate::leanh::lean_ctor_set(v___x_7520_, 1, v_a_7518_);
                    v_sz_7521_ = lean_array_size(v_tail_7508_);
                    v___x_7522_ = 0usize;
                    v___x_7523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Widget_goalToInteractive_spec__2_spec__3(v___x_7497_, v___x_7498_, v___x_7499_, v_tail_7508_, v_sz_7521_, v___x_7522_, v___x_7520_, v___y_7502_, v___y_7503_, v___y_7504_, v___y_7505_);
                    if crate::leanh::lean_obj_tag(v___x_7523_) == 0 {
                        v_a_7524_ = crate::leanh::lean_ctor_get(v___x_7523_, 0);
                        v_isSharedCheck_7537_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7523_)) as u8;
                        if v_isSharedCheck_7537_ == 0 {
                            v___x_7526_ = v___x_7523_;
                            v_isShared_7527_ = v_isSharedCheck_7537_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7524_);
                            crate::leanh::lean_dec(v___x_7523_);
                            v___x_7526_ = crate::leanh::lean_box(0);
                            v_isShared_7527_ = v_isSharedCheck_7537_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_7538_ = crate::leanh::lean_ctor_get(v___x_7523_, 0);
                        v_isSharedCheck_7545_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7523_)) as u8;
                        if v_isSharedCheck_7545_ == 0 {
                            v___x_7540_ = v___x_7523_;
                            v_isShared_7541_ = v_isSharedCheck_7545_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7538_);
                            crate::leanh::lean_dec(v___x_7523_);
                            v___x_7540_ = crate::leanh::lean_box(0);
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
                v_fst_7528_ = crate::leanh::lean_ctor_get(v_a_7524_, 0);
                if crate::leanh::lean_obj_tag(v_fst_7528_) == 0 {
                    v_snd_7529_ = crate::leanh::lean_ctor_get(v_a_7524_, 1);
                    crate::leanh::lean_inc(v_snd_7529_);
                    crate::leanh::lean_dec(v_a_7524_);
                    if v_isShared_7527_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7526_, 0, v_snd_7529_);
                        v___x_7531_ = v___x_7526_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_7532_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7532_, 0, v_snd_7529_);
                        v___x_7531_ = v_reuseFailAlloc_7532_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_7528_);
                    crate::leanh::lean_dec(v_a_7524_);
                    v_val_7533_ = crate::leanh::lean_ctor_get(v_fst_7528_, 0);
                    crate::leanh::lean_inc(v_val_7533_);
                    crate::leanh::lean_dec_ref_known(v_fst_7528_, 1);
                    if v_isShared_7527_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7526_, 0, v_val_7533_);
                        v___x_7535_ = v___x_7526_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_7536_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7536_, 0, v_val_7533_);
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
                    v_reuseFailAlloc_7544_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7544_, 0, v_a_7538_);
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
                    v_reuseFailAlloc_7553_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7553_, 0, v_a_7547_);
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
    mut v___x_7555_: *mut crate::leanh::LeanObject,
    mut v___x_7556_: *mut crate::leanh::LeanObject,
    mut v___x_7557_: *mut crate::leanh::LeanObject,
    mut v_t_7558_: *mut crate::leanh::LeanObject,
    mut v_init_7559_: *mut crate::leanh::LeanObject,
    mut v___y_7560_: *mut crate::leanh::LeanObject,
    mut v___y_7561_: *mut crate::leanh::LeanObject,
    mut v___y_7562_: *mut crate::leanh::LeanObject,
    mut v___y_7563_: *mut crate::leanh::LeanObject,
    mut v___y_7564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_13522__boxed_7565_: u8 = 0;
    let mut v___x_13523__boxed_7566_: u8 = 0;
    let mut v___x_13524__boxed_7567_: u8 = 0;
    let mut v_res_7568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_13522__boxed_7565_ = (crate::leanh::lean_unbox(v___x_7555_) as u8);
    v___x_13523__boxed_7566_ = (crate::leanh::lean_unbox(v___x_7556_) as u8);
    v___x_13524__boxed_7567_ = (crate::leanh::lean_unbox(v___x_7557_) as u8);
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
    crate::leanh::lean_dec(v___y_7563_);
    crate::leanh::lean_dec_ref(v___y_7562_);
    crate::leanh::lean_dec(v___y_7561_);
    crate::leanh::lean_dec_ref(v___y_7560_);
    crate::leanh::lean_dec_ref(v_t_7558_);
    return v_res_7568_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Widget_goalToInteractive_spec__3_spec__5___redArg(
    mut v___y_7569_: *mut crate::leanh::LeanObject,
    mut v___y_7570_: *mut crate::leanh::LeanObject,
    mut v___y_7571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_7576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_7577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_7581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7573_ = lean_st_ref_get(v___y_7571_);
    v_env_7574_ = crate::leanh::lean_ctor_get(v___x_7573_, 0);
    crate::leanh::lean_inc_ref(v_env_7574_);
    crate::leanh::lean_dec(v___x_7573_);
    v___x_7575_ = lean_st_ref_get(v___y_7569_);
    v_mctx_7576_ = crate::leanh::lean_ctor_get(v___x_7575_, 0);
    crate::leanh::lean_inc_ref(v_mctx_7576_);
    crate::leanh::lean_dec(v___x_7575_);
    v_options_7577_ = crate::leanh::lean_ctor_get(v___y_7570_, 2);
    v_currNamespace_7578_ = crate::leanh::lean_ctor_get(v___y_7570_, 6);
    v_openDecls_7579_ = crate::leanh::lean_ctor_get(v___y_7570_, 7);
    v___x_7580_ = lean_st_ref_get(v___y_7571_);
    v_ngen_7581_ = crate::leanh::lean_ctor_get(v___x_7580_, 2);
    crate::leanh::lean_inc_ref(v_ngen_7581_);
    crate::leanh::lean_dec(v___x_7580_);
    v___x_7582_ = crate::leanh::lean_box(0);
    v___x_7583_ = l_Lean_instInhabitedFileMap_default;
    crate::leanh::lean_inc(v_openDecls_7579_);
    crate::leanh::lean_inc(v_currNamespace_7578_);
    crate::leanh::lean_inc_ref(v_options_7577_);
    v___x_7584_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7584_, 0, v_env_7574_);
    crate::leanh::lean_ctor_set(v___x_7584_, 1, v___x_7582_);
    crate::leanh::lean_ctor_set(v___x_7584_, 2, v___x_7583_);
    crate::leanh::lean_ctor_set(v___x_7584_, 3, v_mctx_7576_);
    crate::leanh::lean_ctor_set(v___x_7584_, 4, v_options_7577_);
    crate::leanh::lean_ctor_set(v___x_7584_, 5, v_currNamespace_7578_);
    crate::leanh::lean_ctor_set(v___x_7584_, 6, v_openDecls_7579_);
    crate::leanh::lean_ctor_set(v___x_7584_, 7, v_ngen_7581_);
    v___x_7585_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7585_, 0, v___x_7584_);
    return v___x_7585_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Widget_goalToInteractive_spec__3_spec__5___redArg___boxed(
    mut v___y_7586_: *mut crate::leanh::LeanObject,
    mut v___y_7587_: *mut crate::leanh::LeanObject,
    mut v___y_7588_: *mut crate::leanh::LeanObject,
    mut v___y_7589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7590_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Widget_goalToInteractive_spec__3_spec__5___redArg(v___y_7586_, v___y_7587_, v___y_7588_);
    crate::leanh::lean_dec(v___y_7588_);
    crate::leanh::lean_dec_ref(v___y_7587_);
    crate::leanh::lean_dec(v___y_7586_);
    return v_res_7590_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_save___at___00Lean_Widget_goalToInteractive_spec__3(
    mut v___y_7591_: *mut crate::leanh::LeanObject,
    mut v___y_7592_: *mut crate::leanh::LeanObject,
    mut v___y_7593_: *mut crate::leanh::LeanObject,
    mut v___y_7594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7600_: u8 = 0;
    let mut v_fileMap_7601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_7603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_7604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_7607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7610_: u8 = 0;
    let mut v___x_7611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7618_: u8 = 0;
    let mut v_unused_7619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7621_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7596_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Widget_goalToInteractive_spec__3_spec__5___redArg(v___y_7592_, v___y_7593_, v___y_7594_);
                v_a_7597_ = crate::leanh::lean_ctor_get(v___x_7596_, 0);
                v_isSharedCheck_7621_ = (!crate::leanh::lean_is_exclusive(v___x_7596_)) as u8;
                if v_isSharedCheck_7621_ == 0 {
                    v___x_7599_ = v___x_7596_;
                    v_isShared_7600_ = v_isSharedCheck_7621_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_7597_);
                    crate::leanh::lean_dec(v___x_7596_);
                    v___x_7599_ = crate::leanh::lean_box(0);
                    v_isShared_7600_ = v_isSharedCheck_7621_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fileMap_7601_ = crate::leanh::lean_ctor_get(v___y_7593_, 1);
                v_env_7602_ = crate::leanh::lean_ctor_get(v_a_7597_, 0);
                v_mctx_7603_ = crate::leanh::lean_ctor_get(v_a_7597_, 3);
                v_options_7604_ = crate::leanh::lean_ctor_get(v_a_7597_, 4);
                v_currNamespace_7605_ = crate::leanh::lean_ctor_get(v_a_7597_, 5);
                v_openDecls_7606_ = crate::leanh::lean_ctor_get(v_a_7597_, 6);
                v_ngen_7607_ = crate::leanh::lean_ctor_get(v_a_7597_, 7);
                v_isSharedCheck_7618_ = (!crate::leanh::lean_is_exclusive(v_a_7597_)) as u8;
                if v_isSharedCheck_7618_ == 0 {
                    v_unused_7619_ = crate::leanh::lean_ctor_get(v_a_7597_, 2);
                    crate::leanh::lean_dec(v_unused_7619_);
                    v_unused_7620_ = crate::leanh::lean_ctor_get(v_a_7597_, 1);
                    crate::leanh::lean_dec(v_unused_7620_);
                    v___x_7609_ = v_a_7597_;
                    v_isShared_7610_ = v_isSharedCheck_7618_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ngen_7607_);
                    crate::leanh::lean_inc(v_openDecls_7606_);
                    crate::leanh::lean_inc(v_currNamespace_7605_);
                    crate::leanh::lean_inc(v_options_7604_);
                    crate::leanh::lean_inc(v_mctx_7603_);
                    crate::leanh::lean_inc(v_env_7602_);
                    crate::leanh::lean_dec(v_a_7597_);
                    v___x_7609_ = crate::leanh::lean_box(0);
                    v_isShared_7610_ = v_isSharedCheck_7618_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7611_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_fileMap_7601_);
                if v_isShared_7610_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7609_, 2, v_fileMap_7601_);
                    crate::leanh::lean_ctor_set(v___x_7609_, 1, v___x_7611_);
                    v___x_7613_ = v___x_7609_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7617_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7617_, 0, v_env_7602_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7617_, 1, v___x_7611_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7617_, 2, v_fileMap_7601_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7617_, 3, v_mctx_7603_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7617_, 4, v_options_7604_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7617_, 5, v_currNamespace_7605_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7617_, 6, v_openDecls_7606_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7617_, 7, v_ngen_7607_);
                    v___x_7613_ = v_reuseFailAlloc_7617_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_7600_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7599_, 0, v___x_7613_);
                    v___x_7615_ = v___x_7599_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7616_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7616_, 0, v___x_7613_);
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
    mut v___y_7622_: *mut crate::leanh::LeanObject,
    mut v___y_7623_: *mut crate::leanh::LeanObject,
    mut v___y_7624_: *mut crate::leanh::LeanObject,
    mut v___y_7625_: *mut crate::leanh::LeanObject,
    mut v___y_7626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7627_ =
        l_Lean_Elab_CommandContextInfo_save___at___00Lean_Widget_goalToInteractive_spec__3(
            v___y_7622_,
            v___y_7623_,
            v___y_7624_,
            v___y_7625_,
        );
    crate::leanh::lean_dec(v___y_7625_);
    crate::leanh::lean_dec_ref(v___y_7624_);
    crate::leanh::lean_dec(v___y_7623_);
    crate::leanh::lean_dec_ref(v___y_7622_);
    return v_res_7627_;
}
pub unsafe fn l_Lean_Widget_goalToInteractive___lam__0(
    mut v___x_7636_: u8,
    mut v___x_7637_: u8,
    mut v_mvarId_7638_: *mut crate::leanh::LeanObject,
    mut v_lctx_7639_: *mut crate::leanh::LeanObject,
    mut v_mvarDecl_7640_: *mut crate::leanh::LeanObject,
    mut v___y_7641_: *mut crate::leanh::LeanObject,
    mut v___y_7642_: *mut crate::leanh::LeanObject,
    mut v___y_7643_: *mut crate::leanh::LeanObject,
    mut v___y_7644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_userName_7646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_7648_: u8 = 0;
    let mut v_decls_7649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7652_: u8 = 0;
    let mut v___x_7653_: u8 = 0;
    let mut v___x_7654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7663_: u8 = 0;
    let mut v___x_7664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7676_: u8 = 0;
    let mut v_a_7678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7683_: u8 = 0;
    let mut v___x_7684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7690_: u8 = 0;
    let mut v___x_7691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7698_: u8 = 0;
    let mut v___x_7700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7702_: u8 = 0;
    let mut v_isSharedCheck_7703_: u8 = 0;
    let mut v___x_7704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7713_: u8 = 0;
    let mut v_val_7714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7720_: u8 = 0;
    let mut v___x_7722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7724_: u8 = 0;
    let mut v_a_7725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7728_: u8 = 0;
    let mut v___x_7730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7732_: u8 = 0;
    let mut v_isSharedCheck_7733_: u8 = 0;
    let mut v_unused_7734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_userName_7646_ = crate::leanh::lean_ctor_get(v_mvarDecl_7640_, 0);
                v_type_7647_ = crate::leanh::lean_ctor_get(v_mvarDecl_7640_, 2);
                v_kind_7648_ = crate::leanh::lean_ctor_get_uint8(
                    v_mvarDecl_7640_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_decls_7649_ = crate::leanh::lean_ctor_get(v_lctx_7639_, 1);
                v_isSharedCheck_7733_ = (!crate::leanh::lean_is_exclusive(v_lctx_7639_)) as u8;
                if v_isSharedCheck_7733_ == 0 {
                    v_unused_7734_ = crate::leanh::lean_ctor_get(v_lctx_7639_, 2);
                    crate::leanh::lean_dec(v_unused_7734_);
                    v_unused_7735_ = crate::leanh::lean_ctor_get(v_lctx_7639_, 0);
                    crate::leanh::lean_dec(v_unused_7735_);
                    v___x_7651_ = v_lctx_7639_;
                    v_isShared_7652_ = v_isSharedCheck_7733_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_decls_7649_);
                    crate::leanh::lean_dec(v_lctx_7639_);
                    v___x_7651_ = crate::leanh::lean_box(0);
                    v_isShared_7652_ = v_isSharedCheck_7733_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7653_ = l_Lean_MetavarKind_isSyntheticOpaque(v_kind_7648_);
                v___x_7654_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_7704_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_dec_ref(v_decls_7649_);
                if crate::leanh::lean_obj_tag(v___x_7706_) == 0 {
                    v_a_7707_ = crate::leanh::lean_ctor_get(v___x_7706_, 0);
                    crate::leanh::lean_inc(v_a_7707_);
                    crate::leanh::lean_dec_ref_known(v___x_7706_, 1);
                    v_snd_7708_ = crate::leanh::lean_ctor_get(v_a_7707_, 1);
                    crate::leanh::lean_inc(v_snd_7708_);
                    v_fst_7709_ = crate::leanh::lean_ctor_get(v_a_7707_, 0);
                    crate::leanh::lean_inc(v_fst_7709_);
                    crate::leanh::lean_dec(v_a_7707_);
                    v_fst_7710_ = crate::leanh::lean_ctor_get(v_snd_7708_, 0);
                    crate::leanh::lean_inc(v_fst_7710_);
                    v_snd_7711_ = crate::leanh::lean_ctor_get(v_snd_7708_, 1);
                    crate::leanh::lean_inc(v_snd_7711_);
                    crate::leanh::lean_dec(v_snd_7708_);
                    v___x_7712_ = lean_array_get_size(v_fst_7709_);
                    v___x_7713_ = lean_nat_dec_eq(v___x_7712_, v___x_7654_);
                    if v___x_7713_ == 0 {
                        if crate::leanh::lean_obj_tag(v_fst_7710_) == 0 {
                            crate::leanh::lean_dec(v_fst_7709_);
                            v_a_7678_ = v_snd_7711_;
                            state = 6;
                            continue;
                        } else {
                            v_val_7714_ = crate::leanh::lean_ctor_get(v_fst_7710_, 0);
                            crate::leanh::lean_inc(v_val_7714_);
                            crate::leanh::lean_dec_ref_known(v_fst_7710_, 1);
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
                            if crate::leanh::lean_obj_tag(v___x_7715_) == 0 {
                                v_a_7716_ = crate::leanh::lean_ctor_get(v___x_7715_, 0);
                                crate::leanh::lean_inc(v_a_7716_);
                                crate::leanh::lean_dec_ref_known(v___x_7715_, 1);
                                v_a_7678_ = v_a_7716_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_7651_);
                                crate::leanh::lean_dec_ref(v_mvarDecl_7640_);
                                crate::leanh::lean_dec(v_mvarId_7638_);
                                v_a_7717_ = crate::leanh::lean_ctor_get(v___x_7715_, 0);
                                v_isSharedCheck_7724_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7715_)) as u8;
                                if v_isSharedCheck_7724_ == 0 {
                                    v___x_7719_ = v___x_7715_;
                                    v_isShared_7720_ = v_isSharedCheck_7724_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_7717_);
                                    crate::leanh::lean_dec(v___x_7715_);
                                    v___x_7719_ = crate::leanh::lean_box(0);
                                    v_isShared_7720_ = v_isSharedCheck_7724_;
                                    state = 11;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_7710_);
                        crate::leanh::lean_dec(v_fst_7709_);
                        v_a_7678_ = v_snd_7711_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7651_);
                    crate::leanh::lean_dec_ref(v_mvarDecl_7640_);
                    crate::leanh::lean_dec(v_mvarId_7638_);
                    v_a_7725_ = crate::leanh::lean_ctor_get(v___x_7706_, 0);
                    v_isSharedCheck_7732_ = (!crate::leanh::lean_is_exclusive(v___x_7706_)) as u8;
                    if v_isSharedCheck_7732_ == 0 {
                        v___x_7727_ = v___x_7706_;
                        v_isShared_7728_ = v_isSharedCheck_7732_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7725_);
                        crate::leanh::lean_dec(v___x_7706_);
                        v___x_7727_ = crate::leanh::lean_box(0);
                        v_isShared_7728_ = v_isSharedCheck_7732_;
                        state = 13;
                        continue;
                    }
                }
            }
            2 => {
                v___x_7659_ = l_Lean_Elab_CommandContextInfo_save___at___00Lean_Widget_goalToInteractive_spec__3(v___y_7641_, v___y_7642_, v___y_7643_, v___y_7644_);
                v_a_7660_ = crate::leanh::lean_ctor_get(v___x_7659_, 0);
                v_isSharedCheck_7676_ = (!crate::leanh::lean_is_exclusive(v___x_7659_)) as u8;
                if v_isSharedCheck_7676_ == 0 {
                    v___x_7662_ = v___x_7659_;
                    v_isShared_7663_ = v_isSharedCheck_7676_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_7660_);
                    crate::leanh::lean_dec(v___x_7659_);
                    v___x_7662_ = crate::leanh::lean_box(0);
                    v_isShared_7663_ = v_isSharedCheck_7676_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7664_ = crate::leanh::lean_box(0);
                v___x_7665_ = l_Lean_Widget_goalToInteractive___lam__0___closed__0;
                if v_isShared_7652_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7651_, 2, v___x_7665_);
                    crate::leanh::lean_ctor_set(v___x_7651_, 1, v___x_7664_);
                    crate::leanh::lean_ctor_set(v___x_7651_, 0, v_a_7660_);
                    v___x_7667_ = v___x_7651_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7675_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7675_, 0, v_a_7660_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7675_, 1, v___x_7664_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7675_, 2, v___x_7665_);
                    v___x_7667_ = v_reuseFailAlloc_7675_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7668_ = l_Lean_Server_WithRpcRef_mk___redArg(v___x_7667_);
                v___x_7669_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7669_, 0, v___y_7656_);
                crate::leanh::lean_ctor_set(v___x_7669_, 1, v___y_7657_);
                crate::leanh::lean_ctor_set(v___x_7669_, 2, v___x_7668_);
                v___x_7670_ = l_Lean_Meta_getGoalPrefix(v_mvarDecl_7640_);
                crate::leanh::lean_dec_ref(v_mvarDecl_7640_);
                v___x_7671_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7671_, 0, v___x_7669_);
                crate::leanh::lean_ctor_set(v___x_7671_, 1, v___y_7658_);
                crate::leanh::lean_ctor_set(v___x_7671_, 2, v___x_7670_);
                crate::leanh::lean_ctor_set(v___x_7671_, 3, v_mvarId_7638_);
                crate::leanh::lean_ctor_set(v___x_7671_, 4, v___x_7664_);
                crate::leanh::lean_ctor_set(v___x_7671_, 5, v___x_7664_);
                if v_isShared_7663_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7662_, 0, v___x_7671_);
                    v___x_7673_ = v___x_7662_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7674_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7674_, 0, v___x_7671_);
                    v___x_7673_ = v_reuseFailAlloc_7674_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7673_;
            }
            6 => {
                crate::leanh::lean_inc_ref(v_type_7647_);
                v___x_7679_ = l_Lean_instantiateMVars___at___00Lean_Widget_addInteractiveHypothesisBundle_spec__2___redArg(v_type_7647_, v___y_7642_);
                v_a_7680_ = crate::leanh::lean_ctor_get(v___x_7679_, 0);
                v_isSharedCheck_7703_ = (!crate::leanh::lean_is_exclusive(v___x_7679_)) as u8;
                if v_isSharedCheck_7703_ == 0 {
                    v___x_7682_ = v___x_7679_;
                    v_isShared_7683_ = v_isSharedCheck_7703_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_7680_);
                    crate::leanh::lean_dec(v___x_7679_);
                    v___x_7682_ = crate::leanh::lean_box(0);
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
                if crate::leanh::lean_obj_tag(v___x_7685_) == 0 {
                    if crate::leanh::lean_obj_tag(v_userName_7646_) == 0 {
                        crate::leanh::lean_del_object(v___x_7682_);
                        v_a_7686_ = crate::leanh::lean_ctor_get(v___x_7685_, 0);
                        crate::leanh::lean_inc(v_a_7686_);
                        crate::leanh::lean_dec_ref_known(v___x_7685_, 1);
                        v___x_7687_ = crate::leanh::lean_box(0);
                        v___y_7656_ = v_a_7678_;
                        v___y_7657_ = v_a_7686_;
                        v___y_7658_ = v___x_7687_;
                        state = 2;
                        continue;
                    } else {
                        v_a_7688_ = crate::leanh::lean_ctor_get(v___x_7685_, 0);
                        crate::leanh::lean_inc(v_a_7688_);
                        crate::leanh::lean_dec_ref_known(v___x_7685_, 1);
                        crate::leanh::lean_inc(v_userName_7646_);
                        v___x_7689_ = lean_erase_macro_scopes(v_userName_7646_);
                        v___x_7690_ = 1;
                        v___x_7691_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v___x_7689_,
                                v___x_7690_,
                            );
                        if v_isShared_7683_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_7682_, 1);
                            crate::leanh::lean_ctor_set(v___x_7682_, 0, v___x_7691_);
                            v___x_7693_ = v___x_7682_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_7694_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7694_, 0, v___x_7691_);
                            v___x_7693_ = v_reuseFailAlloc_7694_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7682_);
                    crate::leanh::lean_dec_ref(v_a_7678_);
                    crate::leanh::lean_del_object(v___x_7651_);
                    crate::leanh::lean_dec_ref(v_mvarDecl_7640_);
                    crate::leanh::lean_dec(v_mvarId_7638_);
                    v_a_7695_ = crate::leanh::lean_ctor_get(v___x_7685_, 0);
                    v_isSharedCheck_7702_ = (!crate::leanh::lean_is_exclusive(v___x_7685_)) as u8;
                    if v_isSharedCheck_7702_ == 0 {
                        v___x_7697_ = v___x_7685_;
                        v_isShared_7698_ = v_isSharedCheck_7702_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7695_);
                        crate::leanh::lean_dec(v___x_7685_);
                        v___x_7697_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_7701_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7701_, 0, v_a_7695_);
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
                    v_reuseFailAlloc_7723_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7723_, 0, v_a_7717_);
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
                    v_reuseFailAlloc_7731_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7731_, 0, v_a_7725_);
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
    mut v___x_7736_: *mut crate::leanh::LeanObject,
    mut v___x_7737_: *mut crate::leanh::LeanObject,
    mut v_mvarId_7738_: *mut crate::leanh::LeanObject,
    mut v_lctx_7739_: *mut crate::leanh::LeanObject,
    mut v_mvarDecl_7740_: *mut crate::leanh::LeanObject,
    mut v___y_7741_: *mut crate::leanh::LeanObject,
    mut v___y_7742_: *mut crate::leanh::LeanObject,
    mut v___y_7743_: *mut crate::leanh::LeanObject,
    mut v___y_7744_: *mut crate::leanh::LeanObject,
    mut v___y_7745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_13732__boxed_7746_: u8 = 0;
    let mut v___x_13733__boxed_7747_: u8 = 0;
    let mut v_res_7748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_13732__boxed_7746_ = (crate::leanh::lean_unbox(v___x_7736_) as u8);
    v___x_13733__boxed_7747_ = (crate::leanh::lean_unbox(v___x_7737_) as u8);
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
    crate::leanh::lean_dec(v___y_7744_);
    crate::leanh::lean_dec_ref(v___y_7743_);
    crate::leanh::lean_dec(v___y_7742_);
    crate::leanh::lean_dec_ref(v___y_7741_);
    return v_res_7748_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4_spec__7___redArg(
    mut v_lctx_7749_: *mut crate::leanh::LeanObject,
    mut v_localInsts_7750_: *mut crate::leanh::LeanObject,
    mut v_x_7751_: *mut crate::leanh::LeanObject,
    mut v___y_7752_: *mut crate::leanh::LeanObject,
    mut v___y_7753_: *mut crate::leanh::LeanObject,
    mut v___y_7754_: *mut crate::leanh::LeanObject,
    mut v___y_7755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7761_: u8 = 0;
    let mut v___x_7763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7765_: u8 = 0;
    let mut v_a_7766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7769_: u8 = 0;
    let mut v___x_7771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7773_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7757_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(
                    crate::leanh::lean_box(0),
                    v_lctx_7749_,
                    v_localInsts_7750_,
                    v_x_7751_,
                    v___y_7752_,
                    v___y_7753_,
                    v___y_7754_,
                    v___y_7755_,
                );
                if crate::leanh::lean_obj_tag(v___x_7757_) == 0 {
                    v_a_7758_ = crate::leanh::lean_ctor_get(v___x_7757_, 0);
                    v_isSharedCheck_7765_ = (!crate::leanh::lean_is_exclusive(v___x_7757_)) as u8;
                    if v_isSharedCheck_7765_ == 0 {
                        v___x_7760_ = v___x_7757_;
                        v_isShared_7761_ = v_isSharedCheck_7765_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7758_);
                        crate::leanh::lean_dec(v___x_7757_);
                        v___x_7760_ = crate::leanh::lean_box(0);
                        v_isShared_7761_ = v_isSharedCheck_7765_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7766_ = crate::leanh::lean_ctor_get(v___x_7757_, 0);
                    v_isSharedCheck_7773_ = (!crate::leanh::lean_is_exclusive(v___x_7757_)) as u8;
                    if v_isSharedCheck_7773_ == 0 {
                        v___x_7768_ = v___x_7757_;
                        v_isShared_7769_ = v_isSharedCheck_7773_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7766_);
                        crate::leanh::lean_dec(v___x_7757_);
                        v___x_7768_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_7764_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7764_, 0, v_a_7758_);
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
                    v_reuseFailAlloc_7772_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7772_, 0, v_a_7766_);
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
    mut v_lctx_7774_: *mut crate::leanh::LeanObject,
    mut v_localInsts_7775_: *mut crate::leanh::LeanObject,
    mut v_x_7776_: *mut crate::leanh::LeanObject,
    mut v___y_7777_: *mut crate::leanh::LeanObject,
    mut v___y_7778_: *mut crate::leanh::LeanObject,
    mut v___y_7779_: *mut crate::leanh::LeanObject,
    mut v___y_7780_: *mut crate::leanh::LeanObject,
    mut v___y_7781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7782_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4_spec__7___redArg(v_lctx_7774_, v_localInsts_7775_, v_x_7776_, v___y_7777_, v___y_7778_, v___y_7779_, v___y_7780_);
    crate::leanh::lean_dec(v___y_7780_);
    crate::leanh::lean_dec_ref(v___y_7779_);
    crate::leanh::lean_dec(v___y_7778_);
    crate::leanh::lean_dec_ref(v___y_7777_);
    return v_res_7782_;
}
pub unsafe fn l_Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4___redArg(
    mut v_goal_7783_: *mut crate::leanh::LeanObject,
    mut v_action_7784_: *mut crate::leanh::LeanObject,
    mut v___y_7785_: *mut crate::leanh::LeanObject,
    mut v___y_7786_: *mut crate::leanh::LeanObject,
    mut v___y_7787_: *mut crate::leanh::LeanObject,
    mut v___y_7788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_7791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7790_ = lean_st_ref_get(v___y_7786_);
    v_mctx_7791_ = crate::leanh::lean_ctor_get(v___x_7790_, 0);
    crate::leanh::lean_inc_ref(v_mctx_7791_);
    crate::leanh::lean_dec(v___x_7790_);
    v___x_7792_ = l_Lean_MetavarContext_findDecl_x3f(v_mctx_7791_, v_goal_7783_);
    crate::leanh::lean_dec_ref(v_mctx_7791_);
    if crate::leanh::lean_obj_tag(v___x_7792_) == 1 {
        let mut v_val_7793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_options_7794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_lctx_7795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_localInstances_7796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_7800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_goal_7783_);
        v_val_7793_ = crate::leanh::lean_ctor_get(v___x_7792_, 0);
        crate::leanh::lean_inc(v_val_7793_);
        crate::leanh::lean_dec_ref_known(v___x_7792_, 1);
        v_options_7794_ = crate::leanh::lean_ctor_get(v___y_7787_, 2);
        v_lctx_7795_ = crate::leanh::lean_ctor_get(v_val_7793_, 1);
        v_localInstances_7796_ = crate::leanh::lean_ctor_get(v_val_7793_, 4);
        crate::leanh::lean_inc_ref(v_localInstances_7796_);
        v___x_7797_ = crate::leanh::lean_box(1);
        crate::leanh::lean_inc_ref(v_options_7794_);
        v___x_7798_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_7798_, 0, v_options_7794_);
        crate::leanh::lean_ctor_set(v___x_7798_, 1, v___x_7797_);
        crate::leanh::lean_ctor_set(v___x_7798_, 2, v___x_7797_);
        crate::leanh::lean_inc_ref(v_lctx_7795_);
        v___x_7799_ = l_Lean_LocalContext_sanitizeNames(v_lctx_7795_, v___x_7798_);
        v_fst_7800_ = crate::leanh::lean_ctor_get(v___x_7799_, 0);
        crate::leanh::lean_inc_n(v_fst_7800_, 2);
        crate::leanh::lean_dec_ref(v___x_7799_);
        v___x_7801_ = crate::leanh::lean_apply_2(v_action_7784_, v_fst_7800_, v_val_7793_);
        v___x_7802_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4_spec__7___redArg(v_fst_7800_, v_localInstances_7796_, v___x_7801_, v___y_7785_, v___y_7786_, v___y_7787_, v___y_7788_);
        return v___x_7802_;
    } else {
        let mut v___x_7803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_7792_);
        crate::leanh::lean_dec_ref(v_action_7784_);
        v___x_7803_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Widget_withGoalCtx___redArg___lam__1___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Widget_withGoalCtx___redArg___lam__1___closed__1_once),
            _init_l_Lean_Widget_withGoalCtx___redArg___lam__1___closed__1,
        );
        v___x_7804_ = l_Lean_MessageData_ofName(v_goal_7783_);
        v___x_7805_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_7805_, 0, v___x_7803_);
        crate::leanh::lean_ctor_set(v___x_7805_, 1, v___x_7804_);
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
    mut v_goal_7807_: *mut crate::leanh::LeanObject,
    mut v_action_7808_: *mut crate::leanh::LeanObject,
    mut v___y_7809_: *mut crate::leanh::LeanObject,
    mut v___y_7810_: *mut crate::leanh::LeanObject,
    mut v___y_7811_: *mut crate::leanh::LeanObject,
    mut v___y_7812_: *mut crate::leanh::LeanObject,
    mut v___y_7813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7814_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4___redArg(
        v_goal_7807_,
        v_action_7808_,
        v___y_7809_,
        v___y_7810_,
        v___y_7811_,
        v___y_7812_,
    );
    crate::leanh::lean_dec(v___y_7812_);
    crate::leanh::lean_dec_ref(v___y_7811_);
    crate::leanh::lean_dec(v___y_7810_);
    crate::leanh::lean_dec_ref(v___y_7809_);
    return v_res_7814_;
}
pub unsafe fn l_Lean_Widget_goalToInteractive(
    mut v_mvarId_7815_: *mut crate::leanh::LeanObject,
    mut v_a_7816_: *mut crate::leanh::LeanObject,
    mut v_a_7817_: *mut crate::leanh::LeanObject,
    mut v_a_7818_: *mut crate::leanh::LeanObject,
    mut v_a_7819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_7821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7823_: u8 = 0;
    let mut v___x_7824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7825_: u8 = 0;
    let mut v___x_7826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_options_7821_ = crate::leanh::lean_ctor_get(v_a_7818_, 2);
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
    v___x_7826_ = crate::leanh::lean_box((v___x_7825_) as usize);
    v___x_7827_ = crate::leanh::lean_box((v___x_7823_) as usize);
    crate::leanh::lean_inc(v_mvarId_7815_);
    v___f_7828_ = crate::leanh::lean_alloc_closure(
        l_Lean_Widget_goalToInteractive___lam__0___boxed as *mut core::ffi::c_void,
        10,
        3,
    );
    crate::leanh::lean_closure_set(v___f_7828_, 0, v___x_7826_);
    crate::leanh::lean_closure_set(v___f_7828_, 1, v___x_7827_);
    crate::leanh::lean_closure_set(v___f_7828_, 2, v_mvarId_7815_);
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
    mut v_mvarId_7830_: *mut crate::leanh::LeanObject,
    mut v_a_7831_: *mut crate::leanh::LeanObject,
    mut v_a_7832_: *mut crate::leanh::LeanObject,
    mut v_a_7833_: *mut crate::leanh::LeanObject,
    mut v_a_7834_: *mut crate::leanh::LeanObject,
    mut v_a_7835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7836_ =
        l_Lean_Widget_goalToInteractive(v_mvarId_7830_, v_a_7831_, v_a_7832_, v_a_7833_, v_a_7834_);
    crate::leanh::lean_dec(v_a_7834_);
    crate::leanh::lean_dec_ref(v_a_7833_);
    crate::leanh::lean_dec(v_a_7832_);
    crate::leanh::lean_dec_ref(v_a_7831_);
    return v_res_7836_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Widget_goalToInteractive_spec__3_spec__5(
    mut v___y_7837_: *mut crate::leanh::LeanObject,
    mut v___y_7838_: *mut crate::leanh::LeanObject,
    mut v___y_7839_: *mut crate::leanh::LeanObject,
    mut v___y_7840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7842_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Widget_goalToInteractive_spec__3_spec__5___redArg(v___y_7838_, v___y_7839_, v___y_7840_);
    return v___x_7842_;
}
pub unsafe fn l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Widget_goalToInteractive_spec__3_spec__5___boxed(
    mut v___y_7843_: *mut crate::leanh::LeanObject,
    mut v___y_7844_: *mut crate::leanh::LeanObject,
    mut v___y_7845_: *mut crate::leanh::LeanObject,
    mut v___y_7846_: *mut crate::leanh::LeanObject,
    mut v___y_7847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7848_ = l_Lean_Elab_CommandContextInfo_saveNoFileMap___at___00Lean_Elab_CommandContextInfo_save___at___00Lean_Widget_goalToInteractive_spec__3_spec__5(v___y_7843_, v___y_7844_, v___y_7845_, v___y_7846_);
    crate::leanh::lean_dec(v___y_7846_);
    crate::leanh::lean_dec_ref(v___y_7845_);
    crate::leanh::lean_dec(v___y_7844_);
    crate::leanh::lean_dec_ref(v___y_7843_);
    return v_res_7848_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4_spec__7(
    mut v_00_u03b1_7849_: *mut crate::leanh::LeanObject,
    mut v_lctx_7850_: *mut crate::leanh::LeanObject,
    mut v_localInsts_7851_: *mut crate::leanh::LeanObject,
    mut v_x_7852_: *mut crate::leanh::LeanObject,
    mut v___y_7853_: *mut crate::leanh::LeanObject,
    mut v___y_7854_: *mut crate::leanh::LeanObject,
    mut v___y_7855_: *mut crate::leanh::LeanObject,
    mut v___y_7856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7858_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4_spec__7___redArg(v_lctx_7850_, v_localInsts_7851_, v_x_7852_, v___y_7853_, v___y_7854_, v___y_7855_, v___y_7856_);
    return v___x_7858_;
}
pub unsafe fn l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4_spec__7___boxed(
    mut v_00_u03b1_7859_: *mut crate::leanh::LeanObject,
    mut v_lctx_7860_: *mut crate::leanh::LeanObject,
    mut v_localInsts_7861_: *mut crate::leanh::LeanObject,
    mut v_x_7862_: *mut crate::leanh::LeanObject,
    mut v___y_7863_: *mut crate::leanh::LeanObject,
    mut v___y_7864_: *mut crate::leanh::LeanObject,
    mut v___y_7865_: *mut crate::leanh::LeanObject,
    mut v___y_7866_: *mut crate::leanh::LeanObject,
    mut v___y_7867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7868_ = l_Lean_Meta_withLCtx___at___00Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4_spec__7(v_00_u03b1_7859_, v_lctx_7860_, v_localInsts_7861_, v_x_7862_, v___y_7863_, v___y_7864_, v___y_7865_, v___y_7866_);
    crate::leanh::lean_dec(v___y_7866_);
    crate::leanh::lean_dec_ref(v___y_7865_);
    crate::leanh::lean_dec(v___y_7864_);
    crate::leanh::lean_dec_ref(v___y_7863_);
    return v_res_7868_;
}
pub unsafe fn l_Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4(
    mut v_00_u03b1_7869_: *mut crate::leanh::LeanObject,
    mut v_goal_7870_: *mut crate::leanh::LeanObject,
    mut v_action_7871_: *mut crate::leanh::LeanObject,
    mut v___y_7872_: *mut crate::leanh::LeanObject,
    mut v___y_7873_: *mut crate::leanh::LeanObject,
    mut v___y_7874_: *mut crate::leanh::LeanObject,
    mut v___y_7875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_7878_: *mut crate::leanh::LeanObject,
    mut v_goal_7879_: *mut crate::leanh::LeanObject,
    mut v_action_7880_: *mut crate::leanh::LeanObject,
    mut v___y_7881_: *mut crate::leanh::LeanObject,
    mut v___y_7882_: *mut crate::leanh::LeanObject,
    mut v___y_7883_: *mut crate::leanh::LeanObject,
    mut v___y_7884_: *mut crate::leanh::LeanObject,
    mut v___y_7885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7886_ = l_Lean_Widget_withGoalCtx___at___00Lean_Widget_goalToInteractive_spec__4(
        v_00_u03b1_7878_,
        v_goal_7879_,
        v_action_7880_,
        v___y_7881_,
        v___y_7882_,
        v___y_7883_,
        v___y_7884_,
    );
    crate::leanh::lean_dec(v___y_7884_);
    crate::leanh::lean_dec_ref(v___y_7883_);
    crate::leanh::lean_dec(v___y_7882_);
    crate::leanh::lean_dec_ref(v___y_7881_);
    return v_res_7886_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Widget_InteractiveGoal(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Widget_InteractiveCode(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Extra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default =
        _init_l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default();
    crate::leanh::lean_mark_persistent(
        l_Lean_Widget_instInhabitedInteractiveHypothesisBundle_default,
    );
    l_Lean_Widget_instInhabitedInteractiveHypothesisBundle =
        _init_l_Lean_Widget_instInhabitedInteractiveHypothesisBundle();
    crate::leanh::lean_mark_persistent(l_Lean_Widget_instInhabitedInteractiveHypothesisBundle);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Widget_InteractiveGoal(
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
pub unsafe fn initialize_Lean_Widget_InteractiveGoal(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Widget_InteractiveCode(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Lsp_Extra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Widget_InteractiveGoal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Widget_InteractiveGoal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Widget_InteractiveGoal(builtin);
}

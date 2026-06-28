// Lean compiler output
// Module: Lean.PrettyPrinter
// Imports: Lean.PrettyPrinter.Delaborator.Basic Lean.PrettyPrinter.Delaborator Lean.Parser.Module Lean.ParserCompiler Lean.Util.NumObjs Lean.Util.ShareCommon
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::lean_mk_syntax_ident;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_Name_num___override,
    l_Lean_Name_str___override, l_Lean_firstFrontendMacroScope, l_Lean_replaceRef,
};
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_getMaxHeartbeats, l_Lean_Exception_isRuntime, l_Lean_diagnostics,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_empty,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::{l_Lean_Options_empty, lean_register_option};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_instInhabitedFileMap_default;
use crate::r#gen::Lean::Declaration::{l_Lean_ConstantInfo_levelParams, l_Lean_ConstantInfo_type};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
    l_Lean_Kernel_enableDiag, l_Lean_Kernel_isDiagnosticsEnabled,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_isInterrupt, l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_const___override, l_Lean_Expr_isConst, l_Lean_Expr_sizeWithoutSharing,
};
use crate::r#gen::Lean::Hygiene::l_Lean_sanitizeSyntax;
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::LocalContext::l_Lean_LocalContext_sanitizeNames;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_lazy, l_Lean_MessageData_note, l_Lean_MessageData_ofConstName,
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_MessageData_toString, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey, l_Lean_PPContext_runCoreM___redArg,
    l_Lean_PPContext_runMetaM___redArg,
};
use crate::r#gen::Lean::Meta::PPGoal::l_Lean_Meta_ppGoal___boxed;
use crate::r#gen::Lean::Parser::Module::Syntax::{
    l_Lean_Parser_Module_module_formatter___boxed,
    l_Lean_Parser_Module_module_parenthesizer___boxed,
};
use crate::r#gen::Lean::Parser::Module::{
    initialize_Lean_Parser_Module, runtime_initialize_Lean_Parser_Module,
};
use crate::r#gen::Lean::ParserCompiler::{
    initialize_Lean_ParserCompiler, l_Lean_ParserCompiler_registerParserCompiler___redArg,
    runtime_initialize_Lean_ParserCompiler,
};
use crate::r#gen::Lean::PrettyPrinter::Delaborator::Basic::{
    initialize_Lean_PrettyPrinter_Delaborator_Basic,
    l_Lean_PrettyPrinter_Delaborator_delab___boxed,
    l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___boxed, l_Lean_PrettyPrinter_delab,
    l_Lean_PrettyPrinter_delabCore___redArg, l_Lean_PrettyPrinter_delabLevel,
    runtime_initialize_Lean_PrettyPrinter_Delaborator_Basic,
};
use crate::r#gen::Lean::PrettyPrinter::Delaborator::Builtins::{
    l_Lean_PrettyPrinter_Delaborator_delabConst___boxed,
    l_Lean_PrettyPrinter_Delaborator_delabConstWithSignature___boxed,
};
use crate::r#gen::Lean::PrettyPrinter::Delaborator::{
    initialize_Lean_PrettyPrinter_Delaborator, runtime_initialize_Lean_PrettyPrinter_Delaborator,
};
use crate::r#gen::Lean::PrettyPrinter::Formatter::{
    l_Lean_PrettyPrinter_combinatorFormatterAttribute, l_Lean_PrettyPrinter_format,
    l_Lean_PrettyPrinter_formatCategory, l_Lean_PrettyPrinter_formatterAttribute,
};
use crate::r#gen::Lean::PrettyPrinter::Parenthesizer::{
    l_Lean_PrettyPrinter_combinatorParenthesizerAttribute, l_Lean_PrettyPrinter_parenthesize,
    l_Lean_PrettyPrinter_parenthesizeCategory, l_Lean_PrettyPrinter_parenthesizerAttribute,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::Util::NumObjs::{
    initialize_Lean_Util_NumObjs, l_Lean_Expr_numObjs, runtime_initialize_Lean_Util_NumObjs,
};
use crate::r#gen::Lean::Util::PPExt::{l_Lean_pp_raw, l_Lean_ppFnsRef};
use crate::r#gen::Lean::Util::RecDepth::l_Lean_maxRecDepth;
use crate::r#gen::Lean::Util::ShareCommon::{
    initialize_Lean_Util_ShareCommon, runtime_initialize_Lean_Util_ShareCommon,
};
use crate::r#gen::Lean::Util::Trace::{l_Lean_inheritedTraceOptions, l_Lean_registerTraceClass};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_mk_empty_array_with_capacity, lean_nat_add, lean_panic_fn_borrowed,
};
use crate::lean_imports_rs::Init::ShareCommon::lean_sharecommon_quick;
use crate::lean_imports_rs::Init::System::IO::lean_io_get_num_heartbeats;
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_dbg_to_string;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_3, lean_apply_5, lean_apply_6, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_get_value,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_uint8_once, lean_uint64_once, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l_Lean_PrettyPrinter_ppTerm___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 101, 114, 109, 0],
};
static mut l_Lean_PrettyPrinter_ppTerm___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppTerm___closed__0_value) as *mut LeanObject;
pub static l_Lean_PrettyPrinter_ppTerm___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_PrettyPrinter_ppTerm___closed__0_value) as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_Lean_PrettyPrinter_ppTerm___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppTerm___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [112, 112, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 120, 112, 114, 83, 105, 122, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut LeanObject,14719458919086744478 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value: LeanStringObject<146> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 146, m_capacity: 146, m_length: 145, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 112, 114, 101, 102, 105, 120, 32, 101, 97, 99, 104, 32, 101, 109, 98, 101, 100, 100, 101, 100, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 119, 105, 116, 104, 32, 105, 116, 115, 32, 115, 105, 122, 101, 115, 32, 105, 110, 32, 116, 104, 101, 32, 102, 111, 114, 109, 97, 116, 32, 40, 115, 105, 122, 101, 32, 100, 105, 115, 114, 101, 103, 97, 114, 100, 105, 110, 103, 32, 115, 104, 97, 114, 105, 110, 103, 47, 115, 105, 122, 101, 32, 119, 105, 116, 104, 32, 115, 104, 97, 114, 105, 110, 103, 47, 115, 105, 122, 101, 32, 119, 105, 116, 104, 32, 109, 97, 120, 32, 115, 104, 97, 114, 105, 110, 103, 41, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut LeanObject,300274991653824376 as *mut LeanObject] };
static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut LeanObject,8668468711051311310 as *mut LeanObject] };
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut LeanObject,615934169399469925 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [91, 115, 105, 122, 101, 32, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [47, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__2_value) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__4_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [93, 32, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__5_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__4_value) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lean_PrettyPrinter_ppExpr___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PrettyPrinter_ppExpr___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_PrettyPrinter_ppExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppExpr___closed__0_value) as *mut LeanObject;
pub static l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__0_value: LeanStringObject<10> =
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
        m_data: [116, 97, 103, 65, 112, 112, 70, 110, 115, 0],
    };
static mut l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__0_value)
        as *mut LeanObject;
static l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut LeanObject,6746591144584426489 as *mut LeanObject] };
pub static l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__0_value)
                as *mut LeanObject,
            11389724230315925419 as *mut LeanObject,
        ],
    };
static mut l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__2_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 1,
        },
        m_objs: [1 as *mut LeanObject],
    };
static mut l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__3_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PrettyPrinter_Delaborator_delabConst___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__4_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___boxed
            as *const core::ffi::c_void,
        m_arity: 11,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_ppExprLegacy___closed__0_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 0
                + 24) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [
            282574488338432 as *mut LeanObject,
            72621647814721793 as *mut LeanObject,
            65793 as *mut LeanObject,
        ],
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppExprLegacy___closed__0_value) as *mut LeanObject;
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__1: u64 = 0;
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_ppExprLegacy___closed__3_value: LeanArrayObject<0> =
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
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppExprLegacy___closed__3_value) as *mut LeanObject;
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_ppExprLegacy___closed__13_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [95, 117, 110, 105, 113, 0],
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppExprLegacy___closed__13_value) as *mut LeanObject;
pub static l_Lean_PrettyPrinter_ppExprLegacy___closed__14_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_PrettyPrinter_ppExprLegacy___closed__13_value)
                as *mut LeanObject,
            3978731030111751661 as *mut LeanObject,
        ],
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppExprLegacy___closed__14_value) as *mut LeanObject;
pub static l_Lean_PrettyPrinter_ppExprLegacy___closed__15_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_PrettyPrinter_ppExprLegacy___closed__14_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppExprLegacy___closed__15_value) as *mut LeanObject;
pub static l_Lean_PrettyPrinter_ppExprLegacy___closed__16_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppExprLegacy___closed__16_value) as *mut LeanObject;
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__18: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_ppExprLegacy___closed__19_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 120, 99, 101, 112, 116, 105, 111, 110,
            32, 35, 0,
        ],
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppExprLegacy___closed__19_value) as *mut LeanObject;
pub static l_Lean_PrettyPrinter_ppExprLegacy___closed__20_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            60, 80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 62, 0,
        ],
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppExprLegacy___closed__20_value) as *mut LeanObject;
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__21: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__22: u8 = 0;
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__23: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_ppLevel___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [108, 101, 118, 101, 108, 0],
};
static mut l_Lean_PrettyPrinter_ppLevel___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppLevel___closed__0_value) as *mut LeanObject;
pub static l_Lean_PrettyPrinter_ppLevel___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_PrettyPrinter_ppLevel___closed__0_value) as *mut LeanObject,
        18250387975948097528 as *mut LeanObject,
    ],
};
static mut l_Lean_PrettyPrinter_ppLevel___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppLevel___closed__1_value) as *mut LeanObject;
pub static l_Lean_PrettyPrinter_ppTactic___closed__0_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [116, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lean_PrettyPrinter_ppTactic___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppTactic___closed__0_value) as *mut LeanObject;
pub static l_Lean_PrettyPrinter_ppTactic___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_PrettyPrinter_ppTactic___closed__0_value) as *mut LeanObject,
        16145843736367156323 as *mut LeanObject,
    ],
};
static mut l_Lean_PrettyPrinter_ppTactic___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppTactic___closed__1_value) as *mut LeanObject;
pub static l_Lean_PrettyPrinter_ppCommand___closed__0_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [99, 111, 109, 109, 97, 110, 100, 0],
    };
static mut l_Lean_PrettyPrinter_ppCommand___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppCommand___closed__0_value) as *mut LeanObject;
pub static l_Lean_PrettyPrinter_ppCommand___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_PrettyPrinter_ppCommand___closed__0_value) as *mut LeanObject,
        5063646790596052253 as *mut LeanObject,
    ],
};
static mut l_Lean_PrettyPrinter_ppCommand___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppCommand___closed__1_value) as *mut LeanObject;
pub static l_Lean_PrettyPrinter_ppModule___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_Module_module_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_PrettyPrinter_ppModule___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppModule___closed__0_value) as *mut LeanObject;
pub static l_Lean_PrettyPrinter_ppModule___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_Module_module_formatter___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_PrettyPrinter_ppModule___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppModule___closed__1_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_ppSignature___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PrettyPrinter_Delaborator_delabConstWithSignature___boxed
            as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 1,
        m_objs: [(((1 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_PrettyPrinter_ppSignature___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppSignature___closed__0_value) as *mut LeanObject;
pub static l_Lean_PrettyPrinter_ppSignature___closed__1_value: LeanStringObject<4> =
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
        m_data: [32, 58, 32, 0],
    };
static mut l_Lean_PrettyPrinter_ppSignature___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppSignature___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0___closed__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Delaborator_delab___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0___closed__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0___closed__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value: LeanCtorObject<5> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut LeanObject,61860673417901001 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut LeanObject,9744575919760971988 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,5398202083655750613 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut LeanObject,9389539652570169024 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut LeanObject,11976248792036758390 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject,10922233481441388379 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject,5240565782728729790 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut LeanObject,15235184053563701895 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut LeanObject,5863280441230316749 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject,((( 675687902 as usize) << 1) | 1) as *mut LeanObject,4673300960555192562 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject,1664012690685931901 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__17_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__17_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__17_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__18_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__17_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject,8299898913973098717 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__18_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__18_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__19_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__18_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,8491952124216464304 as *mut LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__19_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__19_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l_Lean_PrettyPrinter_registerParserCompilers___closed__0_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            112, 97, 114, 101, 110, 116, 104, 101, 115, 105, 122, 101, 114, 0,
        ],
    };
static mut l_Lean_PrettyPrinter_registerParserCompilers___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_registerParserCompilers___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_registerParserCompilers___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_PrettyPrinter_registerParserCompilers___closed__0_value)
                as *mut LeanObject,
            4356502393917455154 as *mut LeanObject,
        ],
    };
static mut l_Lean_PrettyPrinter_registerParserCompilers___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_registerParserCompilers___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_PrettyPrinter_registerParserCompilers___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PrettyPrinter_registerParserCompilers___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_registerParserCompilers___closed__3_value: LeanStringObject<10> =
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
        m_data: [102, 111, 114, 109, 97, 116, 116, 101, 114, 0],
    };
static mut l_Lean_PrettyPrinter_registerParserCompilers___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_registerParserCompilers___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_PrettyPrinter_registerParserCompilers___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_PrettyPrinter_registerParserCompilers___closed__3_value)
                as *mut LeanObject,
            7217738091093750654 as *mut LeanObject,
        ],
    };
static mut l_Lean_PrettyPrinter_registerParserCompilers___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_registerParserCompilers___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_PrettyPrinter_registerParserCompilers___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PrettyPrinter_registerParserCompilers___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__0_value: LeanStringObject<25> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            91, 69, 114, 114, 111, 114, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110,
            116, 105, 110, 103, 58, 32, 0,
        ],
    };
static mut l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__2_value: LeanStringObject<2> =
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
        m_data: [93, 0],
    };
static mut l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__0_value: LeanStringObject<44> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 44,
        m_capacity: 44,
        m_length: 43,
        m_data: [
            40, 105, 110, 118, 97, 108, 105, 100, 32, 77, 101, 115, 115, 97, 103, 101, 68, 97, 116,
            97, 46, 108, 97, 122, 121, 44, 32, 109, 105, 115, 115, 105, 110, 103, 32, 99, 111, 110,
            116, 101, 120, 116, 41, 0,
        ],
    };
static mut l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MessageData_ofFormatWithInfosM___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_MessageData_ofFormatWithInfosM___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_MessageData_ofFormatWithInfosM___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_ofFormatWithInfosM___closed__0_value) as *mut LeanObject;
pub static l_Lean_MessageData_ofFormatWithInfosM___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_MessageData_ofFormatWithInfosM___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_MessageData_ofFormatWithInfosM___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_ofFormatWithInfosM___closed__1_value) as *mut LeanObject;
pub static l_Lean_MessageData_ofConst___closed__0_value: LeanStringObject<51> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 51,
    m_capacity: 51,
    m_length: 50,
    m_data: [
        91, 69, 114, 114, 111, 114, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116,
        105, 110, 103, 58, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 110, 111, 116,
        32, 97, 32, 99, 111, 110, 115, 116, 97, 110, 116, 93, 0,
    ],
};
static mut l_Lean_MessageData_ofConst___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_ofConst___closed__0_value) as *mut LeanObject;
static mut l_Lean_MessageData_ofConst___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MessageData_ofConst___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_MessageData_ofConst___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MessageData_ofConst___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_MessageData_ofConst___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MessageData_ofConst___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MessageData_ofConst___closed__4_value: LeanStringObject<19> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        76, 101, 97, 110, 46, 80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 0,
    ],
};
static mut l_Lean_MessageData_ofConst___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_ofConst___closed__4_value) as *mut LeanObject;
pub static l_Lean_MessageData_ofConst___closed__5_value: LeanStringObject<25> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 115, 115, 97, 103, 101, 68, 97, 116, 97, 46, 111, 102, 67,
        111, 110, 115, 116, 0,
    ],
};
static mut l_Lean_MessageData_ofConst___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_ofConst___closed__5_value) as *mut LeanObject;
pub static l_Lean_MessageData_ofConst___closed__6_value: LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 97, 110, 116, 0,
    ],
};
static mut l_Lean_MessageData_ofConst___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_ofConst___closed__6_value) as *mut LeanObject;
static mut l_Lean_MessageData_ofConst___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MessageData_ofConst___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MessageData_signature___lam__0___closed__0_value: LeanStringObject<35> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 35,
        m_capacity: 35,
        m_length: 34,
        m_data: [
            91, 69, 114, 114, 111, 114, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110,
            116, 105, 110, 103, 32, 115, 105, 103, 110, 97, 116, 117, 114, 101, 58, 32, 0,
        ],
    };
static mut l_Lean_MessageData_signature___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_signature___lam__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_MessageData_signature___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MessageData_signature___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_PrettyPrinter_ppCategory(
    mut v_cat_1843_: *mut LeanObject,
    mut v_stx_1844_: *mut LeanObject,
    mut v_a_1845_: *mut LeanObject,
    mut v_a_1846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1859_: u8 = 0;
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1863_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_1848_ = lean_ctor_get(v_a_1845_, 2);
                v___x_1849_ = lean_box(1);
                lean_inc_ref(v_options_1848_);
                v___x_1850_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1850_, 0, v_options_1848_);
                lean_ctor_set(v___x_1850_, 1, v___x_1849_);
                lean_ctor_set(v___x_1850_, 2, v___x_1849_);
                v___x_1851_ = l_Lean_sanitizeSyntax(v_stx_1844_, v___x_1850_);
                v_fst_1852_ = lean_ctor_get(v___x_1851_, 0);
                lean_inc(v_fst_1852_);
                lean_dec_ref(v___x_1851_);
                lean_inc(v_cat_1843_);
                v___x_1853_ = l_Lean_PrettyPrinter_parenthesizeCategory(
                    v_cat_1843_,
                    v_fst_1852_,
                    v_a_1845_,
                    v_a_1846_,
                );
                if lean_obj_tag(v___x_1853_) == 0 {
                    v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
                    lean_inc(v_a_1854_);
                    lean_dec_ref_known(v___x_1853_, 1);
                    v___x_1855_ = l_Lean_PrettyPrinter_formatCategory(
                        v_cat_1843_,
                        v_a_1854_,
                        v_a_1845_,
                        v_a_1846_,
                    );
                    return v___x_1855_;
                } else {
                    lean_dec(v_cat_1843_);
                    v_a_1856_ = lean_ctor_get(v___x_1853_, 0);
                    v_isSharedCheck_1863_ = (!lean_is_exclusive(v___x_1853_)) as u8;
                    if v_isSharedCheck_1863_ == 0 {
                        v___x_1858_ = v___x_1853_;
                        v_isShared_1859_ = v_isSharedCheck_1863_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1856_);
                        lean_dec(v___x_1853_);
                        v___x_1858_ = lean_box(0);
                        v_isShared_1859_ = v_isSharedCheck_1863_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1859_ == 0 {
                    v___x_1861_ = v___x_1858_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
                    v___x_1861_ = v_reuseFailAlloc_1862_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1861_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PrettyPrinter_ppCategory___boxed(
    mut v_cat_1864_: *mut LeanObject,
    mut v_stx_1865_: *mut LeanObject,
    mut v_a_1866_: *mut LeanObject,
    mut v_a_1867_: *mut LeanObject,
    mut v_a_1868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1869_: *mut LeanObject = core::ptr::null_mut();
    v_res_1869_ = l_Lean_PrettyPrinter_ppCategory(v_cat_1864_, v_stx_1865_, v_a_1866_, v_a_1867_);
    lean_dec(v_a_1867_);
    lean_dec_ref(v_a_1866_);
    return v_res_1869_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppTerm(
    mut v_stx_1873_: *mut LeanObject,
    mut v_a_1874_: *mut LeanObject,
    mut v_a_1875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    v___x_1877_ = l_Lean_PrettyPrinter_ppTerm___closed__1;
    v___x_1878_ = l_Lean_PrettyPrinter_ppCategory(v___x_1877_, v_stx_1873_, v_a_1874_, v_a_1875_);
    return v___x_1878_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppTerm___boxed(
    mut v_stx_1879_: *mut LeanObject,
    mut v_a_1880_: *mut LeanObject,
    mut v_a_1881_: *mut LeanObject,
    mut v_a_1882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1883_: *mut LeanObject = core::ptr::null_mut();
    v_res_1883_ = l_Lean_PrettyPrinter_ppTerm(v_stx_1879_, v_a_1880_, v_a_1881_);
    lean_dec(v_a_1881_);
    lean_dec_ref(v_a_1880_);
    return v_res_1883_;
}
pub unsafe fn l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___redArg(
    mut v_lctx_1884_: *mut LeanObject,
    mut v_x_1885_: *mut LeanObject,
    mut v___y_1886_: *mut LeanObject,
    mut v___y_1887_: *mut LeanObject,
    mut v___y_1888_: *mut LeanObject,
    mut v___y_1889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_keyedConfig_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trackZetaDelta_1892_: u8 = 0;
    let mut v_zetaDeltaSet_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_1898_: u8 = 0;
    let mut v_inTypeClassResolution_1899_: u8 = 0;
    let mut v_cacheInferType_1900_: u8 = 0;
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    v_keyedConfig_1891_ = lean_ctor_get(v___y_1886_, 0);
    v_trackZetaDelta_1892_ = lean_ctor_get_uint8(
        v___y_1886_,
        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
    );
    v_zetaDeltaSet_1893_ = lean_ctor_get(v___y_1886_, 1);
    v_localInstances_1894_ = lean_ctor_get(v___y_1886_, 3);
    v_defEqCtx_x3f_1895_ = lean_ctor_get(v___y_1886_, 4);
    v_synthPendingDepth_1896_ = lean_ctor_get(v___y_1886_, 5);
    v_canUnfold_x3f_1897_ = lean_ctor_get(v___y_1886_, 6);
    v_univApprox_1898_ = lean_ctor_get_uint8(
        v___y_1886_,
        (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
    );
    v_inTypeClassResolution_1899_ = lean_ctor_get_uint8(
        v___y_1886_,
        (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
    );
    v_cacheInferType_1900_ = lean_ctor_get_uint8(
        v___y_1886_,
        (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
    );
    lean_inc(v_canUnfold_x3f_1897_);
    lean_inc(v_synthPendingDepth_1896_);
    lean_inc(v_defEqCtx_x3f_1895_);
    lean_inc_ref(v_localInstances_1894_);
    lean_inc(v_zetaDeltaSet_1893_);
    lean_inc_ref(v_keyedConfig_1891_);
    v___x_1901_ = lean_alloc_ctor(0, 7, (4) as u32);
    lean_ctor_set(v___x_1901_, 0, v_keyedConfig_1891_);
    lean_ctor_set(v___x_1901_, 1, v_zetaDeltaSet_1893_);
    lean_ctor_set(v___x_1901_, 2, v_lctx_1884_);
    lean_ctor_set(v___x_1901_, 3, v_localInstances_1894_);
    lean_ctor_set(v___x_1901_, 4, v_defEqCtx_x3f_1895_);
    lean_ctor_set(v___x_1901_, 5, v_synthPendingDepth_1896_);
    lean_ctor_set(v___x_1901_, 6, v_canUnfold_x3f_1897_);
    lean_ctor_set_uint8(
        v___x_1901_,
        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
        v_trackZetaDelta_1892_,
    );
    lean_ctor_set_uint8(
        v___x_1901_,
        (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
        v_univApprox_1898_,
    );
    lean_ctor_set_uint8(
        v___x_1901_,
        (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
        v_inTypeClassResolution_1899_,
    );
    lean_ctor_set_uint8(
        v___x_1901_,
        (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
        v_cacheInferType_1900_,
    );
    lean_inc(v___y_1889_);
    lean_inc_ref(v___y_1888_);
    lean_inc(v___y_1887_);
    v___x_1902_ = lean_apply_5(
        v_x_1885_,
        v___x_1901_,
        v___y_1887_,
        v___y_1888_,
        v___y_1889_,
        lean_box(0),
    );
    return v___x_1902_;
}
pub unsafe fn l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___redArg___boxed(
    mut v_lctx_1903_: *mut LeanObject,
    mut v_x_1904_: *mut LeanObject,
    mut v___y_1905_: *mut LeanObject,
    mut v___y_1906_: *mut LeanObject,
    mut v___y_1907_: *mut LeanObject,
    mut v___y_1908_: *mut LeanObject,
    mut v___y_1909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1910_: *mut LeanObject = core::ptr::null_mut();
    v_res_1910_ = l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___redArg(
        v_lctx_1903_,
        v_x_1904_,
        v___y_1905_,
        v___y_1906_,
        v___y_1907_,
        v___y_1908_,
    );
    lean_dec(v___y_1908_);
    lean_dec_ref(v___y_1907_);
    lean_dec(v___y_1906_);
    lean_dec_ref(v___y_1905_);
    return v_res_1910_;
}
pub unsafe fn l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0(
    mut v_00_u03b1_1911_: *mut LeanObject,
    mut v_lctx_1912_: *mut LeanObject,
    mut v_x_1913_: *mut LeanObject,
    mut v___y_1914_: *mut LeanObject,
    mut v___y_1915_: *mut LeanObject,
    mut v___y_1916_: *mut LeanObject,
    mut v___y_1917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    v___x_1919_ = l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___redArg(
        v_lctx_1912_,
        v_x_1913_,
        v___y_1914_,
        v___y_1915_,
        v___y_1916_,
        v___y_1917_,
    );
    return v___x_1919_;
}
pub unsafe fn l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___boxed(
    mut v_00_u03b1_1920_: *mut LeanObject,
    mut v_lctx_1921_: *mut LeanObject,
    mut v_x_1922_: *mut LeanObject,
    mut v___y_1923_: *mut LeanObject,
    mut v___y_1924_: *mut LeanObject,
    mut v___y_1925_: *mut LeanObject,
    mut v___y_1926_: *mut LeanObject,
    mut v___y_1927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1928_: *mut LeanObject = core::ptr::null_mut();
    v_res_1928_ = l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0(
        v_00_u03b1_1920_,
        v_lctx_1921_,
        v_x_1922_,
        v___y_1923_,
        v___y_1924_,
        v___y_1925_,
        v___y_1926_,
    );
    lean_dec(v___y_1926_);
    lean_dec_ref(v___y_1925_);
    lean_dec(v___y_1924_);
    lean_dec_ref(v___y_1923_);
    return v_res_1928_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppUsing___lam__0(
    mut v_delab_1929_: *mut LeanObject,
    mut v_e_1930_: *mut LeanObject,
    mut v___y_1931_: *mut LeanObject,
    mut v___y_1932_: *mut LeanObject,
    mut v___y_1933_: *mut LeanObject,
    mut v___y_1934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1942_: u8 = 0;
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1946_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_1934_);
                lean_inc_ref(v___y_1933_);
                v___x_1936_ = lean_apply_6(
                    v_delab_1929_,
                    v_e_1930_,
                    v___y_1931_,
                    v___y_1932_,
                    v___y_1933_,
                    v___y_1934_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1936_) == 0 {
                    v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
                    lean_inc(v_a_1937_);
                    lean_dec_ref_known(v___x_1936_, 1);
                    v___x_1938_ = l_Lean_PrettyPrinter_ppTerm(v_a_1937_, v___y_1933_, v___y_1934_);
                    lean_dec(v___y_1934_);
                    lean_dec_ref(v___y_1933_);
                    return v___x_1938_;
                } else {
                    lean_dec(v___y_1934_);
                    lean_dec_ref(v___y_1933_);
                    v_a_1939_ = lean_ctor_get(v___x_1936_, 0);
                    v_isSharedCheck_1946_ = (!lean_is_exclusive(v___x_1936_)) as u8;
                    if v_isSharedCheck_1946_ == 0 {
                        v___x_1941_ = v___x_1936_;
                        v_isShared_1942_ = v_isSharedCheck_1946_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1939_);
                        lean_dec(v___x_1936_);
                        v___x_1941_ = lean_box(0);
                        v_isShared_1942_ = v_isSharedCheck_1946_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1942_ == 0 {
                    v___x_1944_ = v___x_1941_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
                    v___x_1944_ = v_reuseFailAlloc_1945_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1944_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PrettyPrinter_ppUsing___lam__0___boxed(
    mut v_delab_1947_: *mut LeanObject,
    mut v_e_1948_: *mut LeanObject,
    mut v___y_1949_: *mut LeanObject,
    mut v___y_1950_: *mut LeanObject,
    mut v___y_1951_: *mut LeanObject,
    mut v___y_1952_: *mut LeanObject,
    mut v___y_1953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1954_: *mut LeanObject = core::ptr::null_mut();
    v_res_1954_ = l_Lean_PrettyPrinter_ppUsing___lam__0(
        v_delab_1947_,
        v_e_1948_,
        v___y_1949_,
        v___y_1950_,
        v___y_1951_,
        v___y_1952_,
    );
    return v_res_1954_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppUsing(
    mut v_e_1955_: *mut LeanObject,
    mut v_delab_1956_: *mut LeanObject,
    mut v_a_1957_: *mut LeanObject,
    mut v_a_1958_: *mut LeanObject,
    mut v_a_1959_: *mut LeanObject,
    mut v_a_1960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lctx_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    v_lctx_1962_ = lean_ctor_get(v_a_1957_, 2);
    v_options_1963_ = lean_ctor_get(v_a_1959_, 2);
    v___x_1964_ = lean_box(1);
    lean_inc_ref(v_options_1963_);
    v___x_1965_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1965_, 0, v_options_1963_);
    lean_ctor_set(v___x_1965_, 1, v___x_1964_);
    lean_ctor_set(v___x_1965_, 2, v___x_1964_);
    lean_inc_ref(v_lctx_1962_);
    v___x_1966_ = l_Lean_LocalContext_sanitizeNames(v_lctx_1962_, v___x_1965_);
    v_fst_1967_ = lean_ctor_get(v___x_1966_, 0);
    lean_inc(v_fst_1967_);
    lean_dec_ref(v___x_1966_);
    v___f_1968_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_ppUsing___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___f_1968_, 0, v_delab_1956_);
    lean_closure_set(v___f_1968_, 1, v_e_1955_);
    v___x_1969_ = l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___redArg(
        v_fst_1967_,
        v___f_1968_,
        v_a_1957_,
        v_a_1958_,
        v_a_1959_,
        v_a_1960_,
    );
    return v___x_1969_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppUsing___boxed(
    mut v_e_1970_: *mut LeanObject,
    mut v_delab_1971_: *mut LeanObject,
    mut v_a_1972_: *mut LeanObject,
    mut v_a_1973_: *mut LeanObject,
    mut v_a_1974_: *mut LeanObject,
    mut v_a_1975_: *mut LeanObject,
    mut v_a_1976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1977_: *mut LeanObject = core::ptr::null_mut();
    v_res_1977_ = l_Lean_PrettyPrinter_ppUsing(
        v_e_1970_,
        v_delab_1971_,
        v_a_1972_,
        v_a_1973_,
        v_a_1974_,
        v_a_1975_,
    );
    lean_dec(v_a_1975_);
    lean_dec_ref(v_a_1974_);
    lean_dec(v_a_1973_);
    lean_dec_ref(v_a_1972_);
    return v_res_1977_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__spec__0(
    mut v_name_1978_: *mut LeanObject,
    mut v_decl_1979_: *mut LeanObject,
    mut v_ref_1980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: u8 = 0;
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1991_: u8 = 0;
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1996_: u8 = 0;
    let mut v_unused_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2001_: u8 = 0;
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2005_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_1982_ = lean_ctor_get(v_decl_1979_, 0);
                v_descr_1983_ = lean_ctor_get(v_decl_1979_, 1);
                v_deprecation_x3f_1984_ = lean_ctor_get(v_decl_1979_, 2);
                v___x_1985_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_1986_ = (lean_unbox(v_defValue_1982_) as u8);
                lean_ctor_set_uint8(v___x_1985_, 0 as u32, v___x_1986_);
                lean_inc(v_deprecation_x3f_1984_);
                lean_inc_ref(v_descr_1983_);
                lean_inc_n(v_name_1978_, 2);
                v___x_1987_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_1987_, 0, v_name_1978_);
                lean_ctor_set(v___x_1987_, 1, v_ref_1980_);
                lean_ctor_set(v___x_1987_, 2, v___x_1985_);
                lean_ctor_set(v___x_1987_, 3, v_descr_1983_);
                lean_ctor_set(v___x_1987_, 4, v_deprecation_x3f_1984_);
                v___x_1988_ = lean_register_option(v_name_1978_, v___x_1987_);
                if lean_obj_tag(v___x_1988_) == 0 {
                    v_isSharedCheck_1996_ = (!lean_is_exclusive(v___x_1988_)) as u8;
                    if v_isSharedCheck_1996_ == 0 {
                        v_unused_1997_ = lean_ctor_get(v___x_1988_, 0);
                        lean_dec(v_unused_1997_);
                        v___x_1990_ = v___x_1988_;
                        v_isShared_1991_ = v_isSharedCheck_1996_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1988_);
                        v___x_1990_ = lean_box(0);
                        v_isShared_1991_ = v_isSharedCheck_1996_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_1978_);
                    v_a_1998_ = lean_ctor_get(v___x_1988_, 0);
                    v_isSharedCheck_2005_ = (!lean_is_exclusive(v___x_1988_)) as u8;
                    if v_isSharedCheck_2005_ == 0 {
                        v___x_2000_ = v___x_1988_;
                        v_isShared_2001_ = v_isSharedCheck_2005_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1998_);
                        lean_dec(v___x_1988_);
                        v___x_2000_ = lean_box(0);
                        v_isShared_2001_ = v_isSharedCheck_2005_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_1982_);
                v___x_1992_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1992_, 0, v_name_1978_);
                lean_ctor_set(v___x_1992_, 1, v_defValue_1982_);
                if v_isShared_1991_ == 0 {
                    lean_ctor_set(v___x_1990_, 0, v___x_1992_);
                    v___x_1994_ = v___x_1990_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1992_);
                    v___x_1994_ = v_reuseFailAlloc_1995_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1994_;
            }
            3 => {
                if v_isShared_2001_ == 0 {
                    v___x_2003_ = v___x_2000_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1998_);
                    v___x_2003_ = v_reuseFailAlloc_2004_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2003_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_2006_: *mut LeanObject,
    mut v_decl_2007_: *mut LeanObject,
    mut v_ref_2008_: *mut LeanObject,
    mut v_a_2009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2010_: *mut LeanObject = core::ptr::null_mut();
    v_res_2010_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__spec__0(v_name_2006_, v_decl_2007_, v_ref_2008_);
    lean_dec_ref(v_decl_2007_);
    return v_res_2010_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    v___x_2030_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_;
    v___x_2031_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_;
    v___x_2032_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_;
    v___x_2033_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__spec__0(v___x_2030_, v___x_2031_, v___x_2032_);
    return v___x_2033_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4____boxed(
    mut v_a_2034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2035_: *mut LeanObject = core::ptr::null_mut();
    v_res_2035_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_();
    return v_res_2035_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(
    mut v_opts_2036_: *mut LeanObject,
    mut v_opt_2037_: *mut LeanObject,
) -> u8 {
    let mut v_name_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    v_name_2038_ = lean_ctor_get(v_opt_2037_, 0);
    v_defValue_2039_ = lean_ctor_get(v_opt_2037_, 1);
    v_map_2040_ = lean_ctor_get(v_opts_2036_, 0);
    v___x_2041_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2040_,
            v_name_2038_,
        );
    if lean_obj_tag(v___x_2041_) == 0 {
        let mut v___x_2042_: u8 = 0;
        v___x_2042_ = (lean_unbox(v_defValue_2039_) as u8);
        return v___x_2042_;
    } else {
        let mut v_val_2043_: *mut LeanObject = core::ptr::null_mut();
        v_val_2043_ = lean_ctor_get(v___x_2041_, 0);
        lean_inc(v_val_2043_);
        lean_dec_ref_known(v___x_2041_, 1);
        if lean_obj_tag(v_val_2043_) == 1 {
            let mut v_v_2044_: u8 = 0;
            v_v_2044_ = lean_ctor_get_uint8(v_val_2043_, 0 as u32);
            lean_dec_ref_known(v_val_2043_, 0);
            return v_v_2044_;
        } else {
            let mut v___x_2045_: u8 = 0;
            lean_dec(v_val_2043_);
            v___x_2045_ = (lean_unbox(v_defValue_2039_) as u8);
            return v___x_2045_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0___boxed(
    mut v_opts_2046_: *mut LeanObject,
    mut v_opt_2047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2048_: u8 = 0;
    let mut v_r_2049_: *mut LeanObject = core::ptr::null_mut();
    v_res_2048_ = l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(v_opts_2046_, v_opt_2047_);
    lean_dec_ref(v_opt_2047_);
    lean_dec_ref(v_opts_2046_);
    v_r_2049_ = lean_box((v_res_2048_) as usize);
    return v_r_2049_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(
    mut v_e_2059_: *mut LeanObject,
    mut v_f_2060_: *mut LeanObject,
    mut v_a_2061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: u8 = 0;
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2075_: u8 = 0;
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2096_: u8 = 0;
    let mut v_a_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2100_: u8 = 0;
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2108_: u8 = 0;
    let mut v_a_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2112_: u8 = 0;
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2120_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_2063_ = lean_ctor_get(v_a_2061_, 2);
                v_ref_2064_ = lean_ctor_get(v_a_2061_, 5);
                v___x_2065_ = l_Lean_PrettyPrinter_pp_exprSizes;
                v___x_2066_ = l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(v_options_2063_, v___x_2065_);
                if v___x_2066_ == 0 {
                    lean_dec_ref(v_e_2059_);
                    v___x_2067_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2067_, 0, v_f_2060_);
                    return v___x_2067_;
                } else {
                    lean_inc_ref(v_e_2059_);
                    v___x_2068_ = l_Lean_Expr_numObjs(v_e_2059_);
                    if lean_obj_tag(v___x_2068_) == 0 {
                        v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
                        lean_inc(v_a_2069_);
                        lean_dec_ref_known(v___x_2068_, 1);
                        v___x_2070_ = lean_sharecommon_quick(v_e_2059_);
                        v___x_2071_ = l_Lean_Expr_numObjs(v___x_2070_);
                        if lean_obj_tag(v___x_2071_) == 0 {
                            v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
                            v_isSharedCheck_2096_ = (!lean_is_exclusive(v___x_2071_)) as u8;
                            if v_isSharedCheck_2096_ == 0 {
                                v___x_2074_ = v___x_2071_;
                                v_isShared_2075_ = v_isSharedCheck_2096_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_2072_);
                                lean_dec(v___x_2071_);
                                v___x_2074_ = lean_box(0);
                                v_isShared_2075_ = v_isSharedCheck_2096_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2069_);
                            lean_dec(v_f_2060_);
                            lean_dec_ref(v_e_2059_);
                            v_a_2097_ = lean_ctor_get(v___x_2071_, 0);
                            v_isSharedCheck_2108_ = (!lean_is_exclusive(v___x_2071_)) as u8;
                            if v_isSharedCheck_2108_ == 0 {
                                v___x_2099_ = v___x_2071_;
                                v_isShared_2100_ = v_isSharedCheck_2108_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_2097_);
                                lean_dec(v___x_2071_);
                                v___x_2099_ = lean_box(0);
                                v_isShared_2100_ = v_isSharedCheck_2108_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_f_2060_);
                        lean_dec_ref(v_e_2059_);
                        v_a_2109_ = lean_ctor_get(v___x_2068_, 0);
                        v_isSharedCheck_2120_ = (!lean_is_exclusive(v___x_2068_)) as u8;
                        if v_isSharedCheck_2120_ == 0 {
                            v___x_2111_ = v___x_2068_;
                            v_isShared_2112_ = v_isSharedCheck_2120_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_2109_);
                            lean_dec(v___x_2068_);
                            v___x_2111_ = lean_box(0);
                            v_isShared_2112_ = v_isSharedCheck_2120_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2076_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__1;
                v___x_2077_ = l_Lean_Expr_sizeWithoutSharing(v_e_2059_);
                lean_dec_ref(v_e_2059_);
                v___x_2078_ = l_Nat_reprFast(v___x_2077_);
                v___x_2079_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2079_, 0, v___x_2078_);
                v___x_2080_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2080_, 0, v___x_2076_);
                lean_ctor_set(v___x_2080_, 1, v___x_2079_);
                v___x_2081_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__3;
                v___x_2082_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2082_, 0, v___x_2080_);
                lean_ctor_set(v___x_2082_, 1, v___x_2081_);
                v___x_2083_ = l_Nat_reprFast(v_a_2069_);
                v___x_2084_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2084_, 0, v___x_2083_);
                v___x_2085_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2085_, 0, v___x_2082_);
                lean_ctor_set(v___x_2085_, 1, v___x_2084_);
                v___x_2086_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2086_, 0, v___x_2085_);
                lean_ctor_set(v___x_2086_, 1, v___x_2081_);
                v___x_2087_ = l_Nat_reprFast(v_a_2072_);
                v___x_2088_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2088_, 0, v___x_2087_);
                v___x_2089_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2089_, 0, v___x_2086_);
                lean_ctor_set(v___x_2089_, 1, v___x_2088_);
                v___x_2090_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__5;
                v___x_2091_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2091_, 0, v___x_2089_);
                lean_ctor_set(v___x_2091_, 1, v___x_2090_);
                v___x_2092_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2092_, 0, v___x_2091_);
                lean_ctor_set(v___x_2092_, 1, v_f_2060_);
                if v_isShared_2075_ == 0 {
                    lean_ctor_set(v___x_2074_, 0, v___x_2092_);
                    v___x_2094_ = v___x_2074_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2092_);
                    v___x_2094_ = v_reuseFailAlloc_2095_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2094_;
            }
            3 => {
                v___x_2101_ = lean_io_error_to_string(v_a_2097_);
                v___x_2102_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2102_, 0, v___x_2101_);
                v___x_2103_ = l_Lean_MessageData_ofFormat(v___x_2102_);
                lean_inc(v_ref_2064_);
                v___x_2104_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2104_, 0, v_ref_2064_);
                lean_ctor_set(v___x_2104_, 1, v___x_2103_);
                if v_isShared_2100_ == 0 {
                    lean_ctor_set(v___x_2099_, 0, v___x_2104_);
                    v___x_2106_ = v___x_2099_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
                    v___x_2106_ = v_reuseFailAlloc_2107_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2106_;
            }
            5 => {
                v___x_2113_ = lean_io_error_to_string(v_a_2109_);
                v___x_2114_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2114_, 0, v___x_2113_);
                v___x_2115_ = l_Lean_MessageData_ofFormat(v___x_2114_);
                lean_inc(v_ref_2064_);
                v___x_2116_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2116_, 0, v_ref_2064_);
                lean_ctor_set(v___x_2116_, 1, v___x_2115_);
                if v_isShared_2112_ == 0 {
                    lean_ctor_set(v___x_2111_, 0, v___x_2116_);
                    v___x_2118_ = v___x_2111_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2116_);
                    v___x_2118_ = v_reuseFailAlloc_2119_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2118_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___boxed(
    mut v_e_2121_: *mut LeanObject,
    mut v_f_2122_: *mut LeanObject,
    mut v_a_2123_: *mut LeanObject,
    mut v_a_2124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2125_: *mut LeanObject = core::ptr::null_mut();
    v_res_2125_ =
        l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(
            v_e_2121_, v_f_2122_, v_a_2123_,
        );
    lean_dec_ref(v_a_2123_);
    return v_res_2125_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes(
    mut v_e_2126_: *mut LeanObject,
    mut v_f_2127_: *mut LeanObject,
    mut v_a_2128_: *mut LeanObject,
    mut v_a_2129_: *mut LeanObject,
    mut v_a_2130_: *mut LeanObject,
    mut v_a_2131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    v___x_2133_ =
        l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(
            v_e_2126_, v_f_2127_, v_a_2130_,
        );
    return v___x_2133_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___boxed(
    mut v_e_2134_: *mut LeanObject,
    mut v_f_2135_: *mut LeanObject,
    mut v_a_2136_: *mut LeanObject,
    mut v_a_2137_: *mut LeanObject,
    mut v_a_2138_: *mut LeanObject,
    mut v_a_2139_: *mut LeanObject,
    mut v_a_2140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2141_: *mut LeanObject = core::ptr::null_mut();
    v_res_2141_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes(
        v_e_2134_, v_f_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_,
    );
    lean_dec(v_a_2139_);
    lean_dec_ref(v_a_2138_);
    lean_dec(v_a_2137_);
    lean_dec_ref(v_a_2136_);
    return v_res_2141_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppExpr___lam__0(
    mut v_e_2142_: *mut LeanObject,
    mut v___y_2143_: *mut LeanObject,
    mut v___y_2144_: *mut LeanObject,
    mut v___y_2145_: *mut LeanObject,
    mut v___y_2146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    v___x_2148_ = lean_box(1);
    v___x_2149_ = l_Lean_PrettyPrinter_delab(
        v_e_2142_,
        v___x_2148_,
        v___y_2143_,
        v___y_2144_,
        v___y_2145_,
        v___y_2146_,
    );
    return v___x_2149_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppExpr___lam__0___boxed(
    mut v_e_2150_: *mut LeanObject,
    mut v___y_2151_: *mut LeanObject,
    mut v___y_2152_: *mut LeanObject,
    mut v___y_2153_: *mut LeanObject,
    mut v___y_2154_: *mut LeanObject,
    mut v___y_2155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2156_: *mut LeanObject = core::ptr::null_mut();
    v_res_2156_ = l_Lean_PrettyPrinter_ppExpr___lam__0(
        v_e_2150_,
        v___y_2151_,
        v___y_2152_,
        v___y_2153_,
        v___y_2154_,
    );
    lean_dec(v___y_2154_);
    lean_dec_ref(v___y_2153_);
    lean_dec(v___y_2152_);
    lean_dec_ref(v___y_2151_);
    return v_res_2156_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppExpr(
    mut v_e_2158_: *mut LeanObject,
    mut v_a_2159_: *mut LeanObject,
    mut v_a_2160_: *mut LeanObject,
    mut v_a_2161_: *mut LeanObject,
    mut v_a_2162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    v___f_2164_ = l_Lean_PrettyPrinter_ppExpr___closed__0;
    lean_inc_ref(v_e_2158_);
    v___x_2165_ = l_Lean_PrettyPrinter_ppUsing(
        v_e_2158_,
        v___f_2164_,
        v_a_2159_,
        v_a_2160_,
        v_a_2161_,
        v_a_2162_,
    );
    if lean_obj_tag(v___x_2165_) == 0 {
        let mut v_a_2166_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
        v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
        lean_inc(v_a_2166_);
        lean_dec_ref_known(v___x_2165_, 1);
        v___x_2167_ =
            l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(
                v_e_2158_, v_a_2166_, v_a_2161_,
            );
        return v___x_2167_;
    } else {
        lean_dec_ref(v_e_2158_);
        return v___x_2165_;
    }
}
pub unsafe fn l_Lean_PrettyPrinter_ppExpr___boxed(
    mut v_e_2168_: *mut LeanObject,
    mut v_a_2169_: *mut LeanObject,
    mut v_a_2170_: *mut LeanObject,
    mut v_a_2171_: *mut LeanObject,
    mut v_a_2172_: *mut LeanObject,
    mut v_a_2173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2174_: *mut LeanObject = core::ptr::null_mut();
    v_res_2174_ =
        l_Lean_PrettyPrinter_ppExpr(v_e_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
    lean_dec(v_a_2172_);
    lean_dec_ref(v_a_2171_);
    lean_dec(v_a_2170_);
    lean_dec_ref(v_a_2169_);
    return v_res_2174_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppExprWithInfos___lam__0(
    mut v_e_2175_: *mut LeanObject,
    mut v_optsPerPos_2176_: *mut LeanObject,
    mut v_delab_2177_: *mut LeanObject,
    mut v___y_2178_: *mut LeanObject,
    mut v___y_2179_: *mut LeanObject,
    mut v___y_2180_: *mut LeanObject,
    mut v___y_2181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2189_: u8 = 0;
    let mut v___y_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2195_: u8 = 0;
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2202_: u8 = 0;
    let mut v_a_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2206_: u8 = 0;
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2210_: u8 = 0;
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2214_: u8 = 0;
    let mut v_a_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2218_: u8 = 0;
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2222_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_2175_);
                v___x_2183_ = l_Lean_PrettyPrinter_delabCore___redArg(
                    v_e_2175_,
                    v_optsPerPos_2176_,
                    v_delab_2177_,
                    v___y_2178_,
                    v___y_2179_,
                    v___y_2180_,
                    v___y_2181_,
                );
                if lean_obj_tag(v___x_2183_) == 0 {
                    v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
                    lean_inc(v_a_2184_);
                    lean_dec_ref_known(v___x_2183_, 1);
                    v_fst_2185_ = lean_ctor_get(v_a_2184_, 0);
                    v_snd_2186_ = lean_ctor_get(v_a_2184_, 1);
                    v_isSharedCheck_2214_ = (!lean_is_exclusive(v_a_2184_)) as u8;
                    if v_isSharedCheck_2214_ == 0 {
                        v___x_2188_ = v_a_2184_;
                        v_isShared_2189_ = v_isSharedCheck_2214_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2186_);
                        lean_inc(v_fst_2185_);
                        lean_dec(v_a_2184_);
                        v___x_2188_ = lean_box(0);
                        v_isShared_2189_ = v_isSharedCheck_2214_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_2175_);
                    v_a_2215_ = lean_ctor_get(v___x_2183_, 0);
                    v_isSharedCheck_2222_ = (!lean_is_exclusive(v___x_2183_)) as u8;
                    if v_isSharedCheck_2222_ == 0 {
                        v___x_2217_ = v___x_2183_;
                        v_isShared_2218_ = v_isSharedCheck_2222_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2215_);
                        lean_dec(v___x_2183_);
                        v___x_2217_ = lean_box(0);
                        v_isShared_2218_ = v_isSharedCheck_2222_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2211_ = l_Lean_PrettyPrinter_ppTerm(v_fst_2185_, v___y_2180_, v___y_2181_);
                if lean_obj_tag(v___x_2211_) == 0 {
                    v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
                    lean_inc(v_a_2212_);
                    lean_dec_ref_known(v___x_2211_, 1);
                    v___x_2213_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(v_e_2175_, v_a_2212_, v___y_2180_);
                    v___y_2191_ = v___x_2213_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref(v_e_2175_);
                    v___y_2191_ = v___x_2211_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if lean_obj_tag(v___y_2191_) == 0 {
                    v_a_2192_ = lean_ctor_get(v___y_2191_, 0);
                    v_isSharedCheck_2202_ = (!lean_is_exclusive(v___y_2191_)) as u8;
                    if v_isSharedCheck_2202_ == 0 {
                        v___x_2194_ = v___y_2191_;
                        v_isShared_2195_ = v_isSharedCheck_2202_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2192_);
                        lean_dec(v___y_2191_);
                        v___x_2194_ = lean_box(0);
                        v_isShared_2195_ = v_isSharedCheck_2202_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2188_);
                    lean_dec(v_snd_2186_);
                    v_a_2203_ = lean_ctor_get(v___y_2191_, 0);
                    v_isSharedCheck_2210_ = (!lean_is_exclusive(v___y_2191_)) as u8;
                    if v_isSharedCheck_2210_ == 0 {
                        v___x_2205_ = v___y_2191_;
                        v_isShared_2206_ = v_isSharedCheck_2210_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2203_);
                        lean_dec(v___y_2191_);
                        v___x_2205_ = lean_box(0);
                        v_isShared_2206_ = v_isSharedCheck_2210_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2189_ == 0 {
                    lean_ctor_set(v___x_2188_, 0, v_a_2192_);
                    v___x_2197_ = v___x_2188_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2192_);
                    lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_snd_2186_);
                    v___x_2197_ = v_reuseFailAlloc_2201_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2195_ == 0 {
                    lean_ctor_set(v___x_2194_, 0, v___x_2197_);
                    v___x_2199_ = v___x_2194_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
                    v___x_2199_ = v_reuseFailAlloc_2200_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2199_;
            }
            6 => {
                if v_isShared_2206_ == 0 {
                    v___x_2208_ = v___x_2205_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2203_);
                    v___x_2208_ = v_reuseFailAlloc_2209_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2208_;
            }
            8 => {
                if v_isShared_2218_ == 0 {
                    v___x_2220_ = v___x_2217_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
                    v___x_2220_ = v_reuseFailAlloc_2221_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2220_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PrettyPrinter_ppExprWithInfos___lam__0___boxed(
    mut v_e_2223_: *mut LeanObject,
    mut v_optsPerPos_2224_: *mut LeanObject,
    mut v_delab_2225_: *mut LeanObject,
    mut v___y_2226_: *mut LeanObject,
    mut v___y_2227_: *mut LeanObject,
    mut v___y_2228_: *mut LeanObject,
    mut v___y_2229_: *mut LeanObject,
    mut v___y_2230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2231_: *mut LeanObject = core::ptr::null_mut();
    v_res_2231_ = l_Lean_PrettyPrinter_ppExprWithInfos___lam__0(
        v_e_2223_,
        v_optsPerPos_2224_,
        v_delab_2225_,
        v___y_2226_,
        v___y_2227_,
        v___y_2228_,
        v___y_2229_,
    );
    lean_dec(v___y_2229_);
    lean_dec_ref(v___y_2228_);
    lean_dec(v___y_2227_);
    lean_dec_ref(v___y_2226_);
    return v_res_2231_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppExprWithInfos(
    mut v_e_2232_: *mut LeanObject,
    mut v_optsPerPos_2233_: *mut LeanObject,
    mut v_delab_2234_: *mut LeanObject,
    mut v_a_2235_: *mut LeanObject,
    mut v_a_2236_: *mut LeanObject,
    mut v_a_2237_: *mut LeanObject,
    mut v_a_2238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lctx_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    v_lctx_2240_ = lean_ctor_get(v_a_2235_, 2);
    v_options_2241_ = lean_ctor_get(v_a_2237_, 2);
    v___x_2242_ = lean_box(1);
    lean_inc_ref(v_options_2241_);
    v___x_2243_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2243_, 0, v_options_2241_);
    lean_ctor_set(v___x_2243_, 1, v___x_2242_);
    lean_ctor_set(v___x_2243_, 2, v___x_2242_);
    lean_inc_ref(v_lctx_2240_);
    v___x_2244_ = l_Lean_LocalContext_sanitizeNames(v_lctx_2240_, v___x_2243_);
    v_fst_2245_ = lean_ctor_get(v___x_2244_, 0);
    lean_inc(v_fst_2245_);
    lean_dec_ref(v___x_2244_);
    v___f_2246_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_ppExprWithInfos___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___f_2246_, 0, v_e_2232_);
    lean_closure_set(v___f_2246_, 1, v_optsPerPos_2233_);
    lean_closure_set(v___f_2246_, 2, v_delab_2234_);
    v___x_2247_ = l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___redArg(
        v_fst_2245_,
        v___f_2246_,
        v_a_2235_,
        v_a_2236_,
        v_a_2237_,
        v_a_2238_,
    );
    return v___x_2247_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppExprWithInfos___boxed(
    mut v_e_2248_: *mut LeanObject,
    mut v_optsPerPos_2249_: *mut LeanObject,
    mut v_delab_2250_: *mut LeanObject,
    mut v_a_2251_: *mut LeanObject,
    mut v_a_2252_: *mut LeanObject,
    mut v_a_2253_: *mut LeanObject,
    mut v_a_2254_: *mut LeanObject,
    mut v_a_2255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2256_: *mut LeanObject = core::ptr::null_mut();
    v_res_2256_ = l_Lean_PrettyPrinter_ppExprWithInfos(
        v_e_2248_,
        v_optsPerPos_2249_,
        v_delab_2250_,
        v_a_2251_,
        v_a_2252_,
        v_a_2253_,
        v_a_2254_,
    );
    lean_dec(v_a_2254_);
    lean_dec_ref(v_a_2253_);
    lean_dec(v_a_2252_);
    lean_dec_ref(v_a_2251_);
    return v_res_2256_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_PrettyPrinter_ppConstNameWithInfos_spec__0(
    mut v_a_2257_: *mut LeanObject,
    mut v_a_2258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2264_: u8 = 0;
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2270_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2257_) == 0 {
                    v___x_2259_ = l_List_reverse___redArg(v_a_2258_);
                    return v___x_2259_;
                } else {
                    v_head_2260_ = lean_ctor_get(v_a_2257_, 0);
                    v_tail_2261_ = lean_ctor_get(v_a_2257_, 1);
                    v_isSharedCheck_2270_ = (!lean_is_exclusive(v_a_2257_)) as u8;
                    if v_isSharedCheck_2270_ == 0 {
                        v___x_2263_ = v_a_2257_;
                        v_isShared_2264_ = v_isSharedCheck_2270_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2261_);
                        lean_inc(v_head_2260_);
                        lean_dec(v_a_2257_);
                        v___x_2263_ = lean_box(0);
                        v_isShared_2264_ = v_isSharedCheck_2270_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2265_ = l_Lean_mkLevelParam(v_head_2260_);
                if v_isShared_2264_ == 0 {
                    lean_ctor_set(v___x_2263_, 1, v_a_2258_);
                    lean_ctor_set(v___x_2263_, 0, v___x_2265_);
                    v___x_2267_ = v___x_2263_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2265_);
                    lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_a_2258_);
                    v___x_2267_ = v_reuseFailAlloc_2269_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2257_ = v_tail_2261_;
                v_a_2258_ = v___x_2267_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PrettyPrinter_ppConstNameWithInfos(
    mut v_constName_2282_: *mut LeanObject,
    mut v_a_2283_: *mut LeanObject,
    mut v_a_2284_: *mut LeanObject,
    mut v_a_2285_: *mut LeanObject,
    mut v_a_2286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: u8 = 0;
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2308_: u8 = 0;
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2314_: u8 = 0;
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2321_: u8 = 0;
    let mut v_a_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2325_: u8 = 0;
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2329_: u8 = 0;
    let mut v_isSharedCheck_2330_: u8 = 0;
    let mut v_unused_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2288_ = lean_st_ref_get(v_a_2286_);
                v_env_2289_ = lean_ctor_get(v___x_2288_, 0);
                lean_inc_ref(v_env_2289_);
                lean_dec(v___x_2288_);
                v___x_2290_ = 0;
                lean_inc(v_constName_2282_);
                v___x_2291_ =
                    l_Lean_Environment_find_x3f(v_env_2289_, v_constName_2282_, v___x_2290_);
                if lean_obj_tag(v___x_2291_) == 1 {
                    v_val_2292_ = lean_ctor_get(v___x_2291_, 0);
                    lean_inc(v_val_2292_);
                    lean_dec_ref_known(v___x_2291_, 1);
                    v___x_2293_ = l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__4;
                    v___x_2294_ = l_Lean_ConstantInfo_levelParams(v_val_2292_);
                    lean_dec(v_val_2292_);
                    v___x_2295_ = lean_box(0);
                    v___x_2296_ =
                        l_List_mapTR_loop___at___00Lean_PrettyPrinter_ppConstNameWithInfos_spec__0(
                            v___x_2294_,
                            v___x_2295_,
                        );
                    v___x_2297_ = l_Lean_Expr_const___override(v_constName_2282_, v___x_2296_);
                    v___x_2298_ = lean_box(1);
                    v___x_2299_ = l_Lean_PrettyPrinter_ppExprWithInfos(
                        v___x_2297_,
                        v___x_2298_,
                        v___x_2293_,
                        v_a_2283_,
                        v_a_2284_,
                        v_a_2285_,
                        v_a_2286_,
                    );
                    return v___x_2299_;
                } else {
                    lean_dec(v___x_2291_);
                    v_options_2300_ = lean_ctor_get(v_a_2285_, 2);
                    v___x_2301_ = lean_mk_syntax_ident(v_constName_2282_);
                    v___x_2302_ = lean_box(1);
                    lean_inc_ref(v_options_2300_);
                    v___x_2303_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_2303_, 0, v_options_2300_);
                    lean_ctor_set(v___x_2303_, 1, v___x_2302_);
                    lean_ctor_set(v___x_2303_, 2, v___x_2302_);
                    v___x_2304_ = l_Lean_sanitizeSyntax(v___x_2301_, v___x_2303_);
                    v_fst_2305_ = lean_ctor_get(v___x_2304_, 0);
                    v_isSharedCheck_2330_ = (!lean_is_exclusive(v___x_2304_)) as u8;
                    if v_isSharedCheck_2330_ == 0 {
                        v_unused_2331_ = lean_ctor_get(v___x_2304_, 1);
                        lean_dec(v_unused_2331_);
                        v___x_2307_ = v___x_2304_;
                        v_isShared_2308_ = v_isSharedCheck_2330_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_fst_2305_);
                        lean_dec(v___x_2304_);
                        v___x_2307_ = lean_box(0);
                        v_isShared_2308_ = v_isSharedCheck_2330_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2309_ = l_Lean_PrettyPrinter_ppTerm___closed__1;
                v___x_2310_ = l_Lean_PrettyPrinter_formatCategory(
                    v___x_2309_,
                    v_fst_2305_,
                    v_a_2285_,
                    v_a_2286_,
                );
                if lean_obj_tag(v___x_2310_) == 0 {
                    v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
                    v_isSharedCheck_2321_ = (!lean_is_exclusive(v___x_2310_)) as u8;
                    if v_isSharedCheck_2321_ == 0 {
                        v___x_2313_ = v___x_2310_;
                        v_isShared_2314_ = v_isSharedCheck_2321_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2311_);
                        lean_dec(v___x_2310_);
                        v___x_2313_ = lean_box(0);
                        v_isShared_2314_ = v_isSharedCheck_2321_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2307_);
                    v_a_2322_ = lean_ctor_get(v___x_2310_, 0);
                    v_isSharedCheck_2329_ = (!lean_is_exclusive(v___x_2310_)) as u8;
                    if v_isSharedCheck_2329_ == 0 {
                        v___x_2324_ = v___x_2310_;
                        v_isShared_2325_ = v_isSharedCheck_2329_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2322_);
                        lean_dec(v___x_2310_);
                        v___x_2324_ = lean_box(0);
                        v_isShared_2325_ = v_isSharedCheck_2329_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2308_ == 0 {
                    lean_ctor_set(v___x_2307_, 1, v___x_2302_);
                    lean_ctor_set(v___x_2307_, 0, v_a_2311_);
                    v___x_2316_ = v___x_2307_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2311_);
                    lean_ctor_set(v_reuseFailAlloc_2320_, 1, v___x_2302_);
                    v___x_2316_ = v_reuseFailAlloc_2320_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2314_ == 0 {
                    lean_ctor_set(v___x_2313_, 0, v___x_2316_);
                    v___x_2318_ = v___x_2313_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2316_);
                    v___x_2318_ = v_reuseFailAlloc_2319_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2318_;
            }
            5 => {
                if v_isShared_2325_ == 0 {
                    v___x_2327_ = v___x_2324_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
                    v___x_2327_ = v_reuseFailAlloc_2328_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2327_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PrettyPrinter_ppConstNameWithInfos___boxed(
    mut v_constName_2332_: *mut LeanObject,
    mut v_a_2333_: *mut LeanObject,
    mut v_a_2334_: *mut LeanObject,
    mut v_a_2335_: *mut LeanObject,
    mut v_a_2336_: *mut LeanObject,
    mut v_a_2337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2338_: *mut LeanObject = core::ptr::null_mut();
    v_res_2338_ = l_Lean_PrettyPrinter_ppConstNameWithInfos(
        v_constName_2332_,
        v_a_2333_,
        v_a_2334_,
        v_a_2335_,
        v_a_2336_,
    );
    lean_dec(v_a_2336_);
    lean_dec_ref(v_a_2335_);
    lean_dec(v_a_2334_);
    lean_dec_ref(v_a_2333_);
    return v_res_2338_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_PrettyPrinter_ppExprLegacy_spec__0(
    mut v_opts_2339_: *mut LeanObject,
    mut v_opt_2340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    v_name_2341_ = lean_ctor_get(v_opt_2340_, 0);
    v_defValue_2342_ = lean_ctor_get(v_opt_2340_, 1);
    v_map_2343_ = lean_ctor_get(v_opts_2339_, 0);
    v___x_2344_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2343_,
            v_name_2341_,
        );
    if lean_obj_tag(v___x_2344_) == 0 {
        lean_inc(v_defValue_2342_);
        return v_defValue_2342_;
    } else {
        let mut v_val_2345_: *mut LeanObject = core::ptr::null_mut();
        v_val_2345_ = lean_ctor_get(v___x_2344_, 0);
        lean_inc(v_val_2345_);
        lean_dec_ref_known(v___x_2344_, 1);
        if lean_obj_tag(v_val_2345_) == 3 {
            let mut v_v_2346_: *mut LeanObject = core::ptr::null_mut();
            v_v_2346_ = lean_ctor_get(v_val_2345_, 0);
            lean_inc(v_v_2346_);
            lean_dec_ref_known(v_val_2345_, 1);
            return v_v_2346_;
        } else {
            lean_dec(v_val_2345_);
            lean_inc(v_defValue_2342_);
            return v_defValue_2342_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_PrettyPrinter_ppExprLegacy_spec__0___boxed(
    mut v_opts_2347_: *mut LeanObject,
    mut v_opt_2348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2349_: *mut LeanObject = core::ptr::null_mut();
    v_res_2349_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_ppExprLegacy_spec__0(
        v_opts_2347_,
        v_opt_2348_,
    );
    lean_dec_ref(v_opt_2348_);
    lean_dec_ref(v_opts_2347_);
    return v_res_2349_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__1() -> u64 {
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: u64 = 0;
    v___x_2356_ = l_Lean_PrettyPrinter_ppExprLegacy___closed__0;
    v___x_2357_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2356_);
    return v___x_2357_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__2() -> *mut LeanObject {
    let mut v___x_2358_: u64 = 0;
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    v___x_2358_ = lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__1),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__1_once),
        _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__1,
    );
    v___x_2359_ = l_Lean_PrettyPrinter_ppExprLegacy___closed__0;
    v___x_2360_ = lean_alloc_ctor(0, 1, (8) as u32);
    lean_ctor_set(v___x_2360_, 0, v___x_2359_);
    lean_ctor_set_uint64(
        v___x_2360_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2358_,
    );
    return v___x_2360_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__4() -> *mut LeanObject {
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    v___x_2363_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2363_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__5() -> *mut LeanObject {
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    v___x_2364_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__4),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__4_once),
        _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__4,
    );
    v___x_2365_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2365_, 0, v___x_2364_);
    return v___x_2365_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__6() -> *mut LeanObject {
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    v___x_2366_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__5),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__5_once),
        _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__5,
    );
    v___x_2367_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_2367_, 0, v___x_2366_);
    lean_ctor_set(v___x_2367_, 1, v___x_2366_);
    lean_ctor_set(v___x_2367_, 2, v___x_2366_);
    lean_ctor_set(v___x_2367_, 3, v___x_2366_);
    lean_ctor_set(v___x_2367_, 4, v___x_2366_);
    lean_ctor_set(v___x_2367_, 5, v___x_2366_);
    return v___x_2367_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__7() -> *mut LeanObject {
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    v___x_2368_ = lean_unsigned_to_nat(32);
    v___x_2369_ = lean_mk_empty_array_with_capacity(v___x_2368_);
    v___x_2370_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2370_, 0, v___x_2369_);
    return v___x_2370_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__8() -> *mut LeanObject {
    let mut v___x_2371_: usize = 0;
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    v___x_2371_ = 5usize;
    v___x_2372_ = lean_unsigned_to_nat(0);
    v___x_2373_ = lean_unsigned_to_nat(32);
    v___x_2374_ = lean_mk_empty_array_with_capacity(v___x_2373_);
    v___x_2375_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__7),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__7_once),
        _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__7,
    );
    v___x_2376_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_2376_, 0, v___x_2375_);
    lean_ctor_set(v___x_2376_, 1, v___x_2374_);
    lean_ctor_set(v___x_2376_, 2, v___x_2372_);
    lean_ctor_set(v___x_2376_, 3, v___x_2372_);
    lean_ctor_set_usize(v___x_2376_, 4, v___x_2371_);
    return v___x_2376_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__9() -> *mut LeanObject {
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    v___x_2377_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__5),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__5_once),
        _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__5,
    );
    v___x_2378_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_2378_, 0, v___x_2377_);
    lean_ctor_set(v___x_2378_, 1, v___x_2377_);
    lean_ctor_set(v___x_2378_, 2, v___x_2377_);
    lean_ctor_set(v___x_2378_, 3, v___x_2377_);
    lean_ctor_set(v___x_2378_, 4, v___x_2377_);
    return v___x_2378_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__10() -> *mut LeanObject {
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    v___x_2379_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__5),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__5_once),
        _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__5,
    );
    v___x_2380_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2380_, 0, v___x_2379_);
    lean_ctor_set(v___x_2380_, 1, v___x_2379_);
    return v___x_2380_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__11() -> *mut LeanObject {
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    v___x_2381_ = l_Lean_NameSet_empty;
    v___x_2382_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__8),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__8_once),
        _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__8,
    );
    v___x_2383_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2383_, 0, v___x_2382_);
    lean_ctor_set(v___x_2383_, 1, v___x_2382_);
    lean_ctor_set(v___x_2383_, 2, v___x_2381_);
    return v___x_2383_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__12() -> *mut LeanObject {
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    v___x_2384_ = lean_unsigned_to_nat(1);
    v___x_2385_ = l_Lean_firstFrontendMacroScope;
    v___x_2386_ = lean_nat_add(v___x_2385_, v___x_2384_);
    return v___x_2386_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__17() -> *mut LeanObject {
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: u64 = 0;
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    v___x_2397_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__8),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__8_once),
        _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__8,
    );
    v___x_2398_ = 0u64;
    v___x_2399_ = lean_alloc_ctor(0, 1, (8) as u32);
    lean_ctor_set(v___x_2399_, 0, v___x_2397_);
    lean_ctor_set_uint64(
        v___x_2399_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2398_,
    );
    return v___x_2399_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__18() -> *mut LeanObject {
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: u8 = 0;
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    v___x_2400_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__8),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__8_once),
        _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__8,
    );
    v___x_2401_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__5),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__5_once),
        _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__5,
    );
    v___x_2402_ = 1;
    v___x_2403_ = lean_alloc_ctor(0, 3, (1) as u32);
    lean_ctor_set(v___x_2403_, 0, v___x_2401_);
    lean_ctor_set(v___x_2403_, 1, v___x_2401_);
    lean_ctor_set(v___x_2403_, 2, v___x_2400_);
    lean_ctor_set_uint8(
        v___x_2403_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_2402_,
    );
    return v___x_2403_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__21() -> *mut LeanObject {
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    v___x_2406_ = l_Lean_Options_empty;
    v___x_2407_ = l_Lean_Core_getMaxHeartbeats(v___x_2406_);
    return v___x_2407_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__22() -> u8 {
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: u8 = 0;
    v___x_2408_ = l_Lean_diagnostics;
    v___x_2409_ = l_Lean_Options_empty;
    v___x_2410_ = l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(v___x_2409_, v___x_2408_);
    return v___x_2410_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__23() -> *mut LeanObject {
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    v___x_2411_ = l_Lean_maxRecDepth;
    v___x_2412_ = l_Lean_Options_empty;
    v___x_2413_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_ppExprLegacy_spec__0(
        v___x_2412_,
        v___x_2411_,
    );
    return v___x_2413_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppExprLegacy(
    mut v_env_2414_: *mut LeanObject,
    mut v_mctx_2415_: *mut LeanObject,
    mut v_lctx_2416_: *mut LeanObject,
    mut v_opts_2417_: *mut LeanObject,
    mut v_e_2418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: u8 = 0;
    let mut v___x_2422_: u8 = 0;
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2446_: u8 = 0;
    let mut v___y_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2459_: u8 = 0;
    let mut v_inheritedTraceOptions_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2468_: u8 = 0;
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2474_: u8 = 0;
    let mut v_a_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2478_: u8 = 0;
    let mut v_msg_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2493_: u8 = 0;
    let mut v___y_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2496_: u8 = 0;
    let mut v___y_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2511_: u8 = 0;
    let mut v_inheritedTraceOptions_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2515_: u8 = 0;
    let mut v___y_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2519_: u8 = 0;
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2531_: u8 = 0;
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2537_: u8 = 0;
    let mut v_unused_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: u8 = 0;
    let mut v___y_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2569_: u8 = 0;
    let mut v_inheritedTraceOptions_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2573_: u8 = 0;
    let mut v_env_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: u8 = 0;
    let mut v___x_2580_: u8 = 0;
    let mut v_reuseFailAlloc_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2582_: u8 = 0;
    let mut v_unused_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2586_: u8 = 0;
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2598_: u8 = 0;
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2604_: u8 = 0;
    let mut v_unused_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2420_ = lean_box(1);
                v___x_2421_ = 0;
                v___x_2422_ = 1;
                v___x_2423_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__2_once),
                    _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__2,
                );
                v___x_2424_ = lean_unsigned_to_nat(0);
                v___x_2425_ = l_Lean_PrettyPrinter_ppExprLegacy___closed__3;
                v___x_2426_ = lean_box(0);
                v___x_2427_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_2427_, 0, v___x_2423_);
                lean_ctor_set(v___x_2427_, 1, v___x_2420_);
                lean_ctor_set(v___x_2427_, 2, v_lctx_2416_);
                lean_ctor_set(v___x_2427_, 3, v___x_2425_);
                lean_ctor_set(v___x_2427_, 4, v___x_2426_);
                lean_ctor_set(v___x_2427_, 5, v___x_2424_);
                lean_ctor_set(v___x_2427_, 6, v___x_2426_);
                lean_ctor_set_uint8(
                    v___x_2427_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v___x_2421_,
                );
                lean_ctor_set_uint8(
                    v___x_2427_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v___x_2421_,
                );
                lean_ctor_set_uint8(
                    v___x_2427_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v___x_2421_,
                );
                lean_ctor_set_uint8(
                    v___x_2427_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v___x_2422_,
                );
                v___x_2428_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__6),
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__6_once),
                    _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__6,
                );
                v___x_2429_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__8),
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__8_once),
                    _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__8,
                );
                v___x_2430_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__9),
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__9_once),
                    _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__9,
                );
                v___x_2431_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__10),
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__10_once),
                    _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__10,
                );
                v___x_2432_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__11),
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__11_once),
                    _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__11,
                );
                v___x_2433_ = lean_io_get_num_heartbeats();
                v___x_2434_ = l_Lean_firstFrontendMacroScope;
                v___x_2435_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__12),
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__12_once),
                    _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__12,
                );
                v___x_2436_ = l_Lean_PrettyPrinter_ppExprLegacy___closed__15;
                v___x_2437_ = lean_box(0);
                v___x_2438_ = lean_box(0);
                v___x_2439_ = l_Lean_PrettyPrinter_ppExprLegacy___closed__16;
                v___x_2440_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__17),
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__17_once),
                    _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__17,
                );
                v___x_2441_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__18),
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__18_once),
                    _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__18,
                );
                v___x_2442_ = lean_alloc_ctor(0, 9, (0) as u32);
                lean_ctor_set(v___x_2442_, 0, v_env_2414_);
                lean_ctor_set(v___x_2442_, 1, v___x_2435_);
                lean_ctor_set(v___x_2442_, 2, v___x_2436_);
                lean_ctor_set(v___x_2442_, 3, v___x_2439_);
                lean_ctor_set(v___x_2442_, 4, v___x_2440_);
                lean_ctor_set(v___x_2442_, 5, v___x_2431_);
                lean_ctor_set(v___x_2442_, 6, v___x_2432_);
                lean_ctor_set(v___x_2442_, 7, v___x_2441_);
                lean_ctor_set(v___x_2442_, 8, v___x_2425_);
                v___x_2443_ = lean_st_mk_ref(v___x_2442_);
                v___x_2539_ = l_Lean_inheritedTraceOptions;
                v___x_2540_ = lean_st_ref_get(v___x_2539_);
                v___x_2541_ = lean_st_ref_get(v___x_2443_);
                v___x_2542_ = l_Lean_PrettyPrinter_ppExprLegacy___closed__20;
                v___x_2543_ = l_Lean_instInhabitedFileMap_default;
                v___x_2544_ = l_Lean_Options_empty;
                v___x_2545_ = lean_unsigned_to_nat(1000);
                v___x_2546_ = lean_box(0);
                v___x_2547_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__21),
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__21_once),
                    _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__21,
                );
                v___x_2548_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_2548_, 0, v___x_2542_);
                lean_ctor_set(v___x_2548_, 1, v___x_2543_);
                lean_ctor_set(v___x_2548_, 2, v___x_2544_);
                lean_ctor_set(v___x_2548_, 3, v___x_2424_);
                lean_ctor_set(v___x_2548_, 4, v___x_2545_);
                lean_ctor_set(v___x_2548_, 5, v___x_2546_);
                lean_ctor_set(v___x_2548_, 6, v___x_2437_);
                lean_ctor_set(v___x_2548_, 7, v___x_2438_);
                lean_ctor_set(v___x_2548_, 8, v___x_2433_);
                lean_ctor_set(v___x_2548_, 9, v___x_2547_);
                lean_ctor_set(v___x_2548_, 10, v___x_2437_);
                lean_ctor_set(v___x_2548_, 11, v___x_2434_);
                lean_ctor_set(v___x_2548_, 12, v___x_2426_);
                lean_ctor_set(v___x_2548_, 13, v___x_2540_);
                lean_ctor_set_uint8(
                    v___x_2548_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v___x_2421_,
                );
                lean_ctor_set_uint8(
                    v___x_2548_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v___x_2421_,
                );
                v_env_2549_ = lean_ctor_get(v___x_2541_, 0);
                lean_inc_ref(v_env_2549_);
                lean_dec(v___x_2541_);
                v___x_2550_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_2550_, 0, v_mctx_2415_);
                lean_ctor_set(v___x_2550_, 1, v___x_2428_);
                lean_ctor_set(v___x_2550_, 2, v___x_2420_);
                lean_ctor_set(v___x_2550_, 3, v___x_2429_);
                lean_ctor_set(v___x_2550_, 4, v___x_2430_);
                v___x_2551_ = l_Lean_diagnostics;
                v___x_2552_ = lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__22),
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__22_once),
                    _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__22,
                );
                v___x_2606_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2549_);
                lean_dec_ref(v_env_2549_);
                if v___x_2606_ == 0 {
                    if v___x_2552_ == 0 {
                        lean_inc(v___x_2443_);
                        v___y_2554_ = v___x_2548_;
                        v___y_2555_ = v___x_2443_;
                        state = 11;
                        continue;
                    } else {
                        v___y_2586_ = v___x_2606_;
                        state = 14;
                        continue;
                    }
                } else {
                    v___y_2586_ = v___x_2552_;
                    state = 14;
                    continue;
                }
            }
            1 => {
                v___x_2462_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_ppExprLegacy_spec__0(
                    v_opts_2417_,
                    v___y_2447_,
                );
                v___x_2463_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_2463_, 0, v_fileName_2448_);
                lean_ctor_set(v___x_2463_, 1, v_fileMap_2449_);
                lean_ctor_set(v___x_2463_, 2, v_opts_2417_);
                lean_ctor_set(v___x_2463_, 3, v_currRecDepth_2450_);
                lean_ctor_set(v___x_2463_, 4, v___x_2462_);
                lean_ctor_set(v___x_2463_, 5, v_ref_2451_);
                lean_ctor_set(v___x_2463_, 6, v_currNamespace_2452_);
                lean_ctor_set(v___x_2463_, 7, v_openDecls_2453_);
                lean_ctor_set(v___x_2463_, 8, v_initHeartbeats_2454_);
                lean_ctor_set(v___x_2463_, 9, v_maxHeartbeats_2455_);
                lean_ctor_set(v___x_2463_, 10, v_quotContext_2456_);
                lean_ctor_set(v___x_2463_, 11, v_currMacroScope_2457_);
                lean_ctor_set(v___x_2463_, 12, v_cancelTk_x3f_2458_);
                lean_ctor_set(v___x_2463_, 13, v_inheritedTraceOptions_2460_);
                lean_ctor_set_uint8(
                    v___x_2463_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v___y_2446_,
                );
                lean_ctor_set_uint8(
                    v___x_2463_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_2459_,
                );
                v___x_2464_ = l_Lean_PrettyPrinter_ppExpr(
                    v_e_2418_,
                    v___x_2427_,
                    v___y_2445_,
                    v___x_2463_,
                    v___y_2461_,
                );
                lean_dec(v___y_2461_);
                lean_dec_ref_known(v___x_2463_, 14);
                lean_dec_ref_known(v___x_2427_, 7);
                if lean_obj_tag(v___x_2464_) == 0 {
                    v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
                    v_isSharedCheck_2474_ = (!lean_is_exclusive(v___x_2464_)) as u8;
                    if v_isSharedCheck_2474_ == 0 {
                        v___x_2467_ = v___x_2464_;
                        v_isShared_2468_ = v_isSharedCheck_2474_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2465_);
                        lean_dec(v___x_2464_);
                        v___x_2467_ = lean_box(0);
                        v_isShared_2468_ = v_isSharedCheck_2474_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___y_2445_);
                    lean_dec(v___x_2443_);
                    v_a_2475_ = lean_ctor_get(v___x_2464_, 0);
                    v_isSharedCheck_2493_ = (!lean_is_exclusive(v___x_2464_)) as u8;
                    if v_isSharedCheck_2493_ == 0 {
                        v___x_2477_ = v___x_2464_;
                        v_isShared_2478_ = v_isSharedCheck_2493_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2475_);
                        lean_dec(v___x_2464_);
                        v___x_2477_ = lean_box(0);
                        v_isShared_2478_ = v_isSharedCheck_2493_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2469_ = lean_st_ref_get(v___y_2445_);
                lean_dec(v___y_2445_);
                lean_dec(v___x_2469_);
                v___x_2470_ = lean_st_ref_get(v___x_2443_);
                lean_dec(v___x_2443_);
                lean_dec(v___x_2470_);
                if v_isShared_2468_ == 0 {
                    v___x_2472_ = v___x_2467_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2465_);
                    v___x_2472_ = v_reuseFailAlloc_2473_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2472_;
            }
            4 => {
                if lean_obj_tag(v_a_2475_) == 0 {
                    v_msg_2479_ = lean_ctor_get(v_a_2475_, 1);
                    lean_inc_ref(v_msg_2479_);
                    lean_dec_ref_known(v_a_2475_, 2);
                    v___x_2480_ = l_Lean_MessageData_toString(v_msg_2479_);
                    v___x_2481_ = lean_mk_io_user_error(v___x_2480_);
                    if v_isShared_2478_ == 0 {
                        lean_ctor_set(v___x_2477_, 0, v___x_2481_);
                        v___x_2483_ = v___x_2477_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2481_);
                        v___x_2483_ = v_reuseFailAlloc_2484_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_id_2485_ = lean_ctor_get(v_a_2475_, 0);
                    lean_inc(v_id_2485_);
                    lean_dec_ref_known(v_a_2475_, 2);
                    v___x_2486_ = l_Lean_PrettyPrinter_ppExprLegacy___closed__19;
                    v___x_2487_ = l_Nat_reprFast(v_id_2485_);
                    v___x_2488_ = lean_string_append(v___x_2486_, v___x_2487_);
                    lean_dec_ref(v___x_2487_);
                    v___x_2489_ = lean_mk_io_user_error(v___x_2488_);
                    if v_isShared_2478_ == 0 {
                        lean_ctor_set(v___x_2477_, 0, v___x_2489_);
                        v___x_2491_ = v___x_2477_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2489_);
                        v___x_2491_ = v_reuseFailAlloc_2492_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_2483_;
            }
            6 => {
                return v___x_2491_;
            }
            7 => {
                v_fileName_2500_ = lean_ctor_get(v___y_2498_, 0);
                lean_inc_ref(v_fileName_2500_);
                v_fileMap_2501_ = lean_ctor_get(v___y_2498_, 1);
                lean_inc_ref(v_fileMap_2501_);
                v_currRecDepth_2502_ = lean_ctor_get(v___y_2498_, 3);
                lean_inc(v_currRecDepth_2502_);
                v_ref_2503_ = lean_ctor_get(v___y_2498_, 5);
                lean_inc(v_ref_2503_);
                v_currNamespace_2504_ = lean_ctor_get(v___y_2498_, 6);
                lean_inc(v_currNamespace_2504_);
                v_openDecls_2505_ = lean_ctor_get(v___y_2498_, 7);
                lean_inc(v_openDecls_2505_);
                v_initHeartbeats_2506_ = lean_ctor_get(v___y_2498_, 8);
                lean_inc(v_initHeartbeats_2506_);
                v_maxHeartbeats_2507_ = lean_ctor_get(v___y_2498_, 9);
                lean_inc(v_maxHeartbeats_2507_);
                v_quotContext_2508_ = lean_ctor_get(v___y_2498_, 10);
                lean_inc(v_quotContext_2508_);
                v_currMacroScope_2509_ = lean_ctor_get(v___y_2498_, 11);
                lean_inc(v_currMacroScope_2509_);
                v_cancelTk_x3f_2510_ = lean_ctor_get(v___y_2498_, 12);
                lean_inc(v_cancelTk_x3f_2510_);
                v_suppressElabErrors_2511_ = lean_ctor_get_uint8(
                    v___y_2498_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2512_ = lean_ctor_get(v___y_2498_, 13);
                lean_inc_ref(v_inheritedTraceOptions_2512_);
                lean_dec_ref(v___y_2498_);
                v___y_2445_ = v___y_2495_;
                v___y_2446_ = v___y_2496_;
                v___y_2447_ = v___y_2497_;
                v_fileName_2448_ = v_fileName_2500_;
                v_fileMap_2449_ = v_fileMap_2501_;
                v_currRecDepth_2450_ = v_currRecDepth_2502_;
                v_ref_2451_ = v_ref_2503_;
                v_currNamespace_2452_ = v_currNamespace_2504_;
                v_openDecls_2453_ = v_openDecls_2505_;
                v_initHeartbeats_2454_ = v_initHeartbeats_2506_;
                v_maxHeartbeats_2455_ = v_maxHeartbeats_2507_;
                v_quotContext_2456_ = v_quotContext_2508_;
                v_currMacroScope_2457_ = v_currMacroScope_2509_;
                v_cancelTk_x3f_2458_ = v_cancelTk_x3f_2510_;
                v_suppressElabErrors_2459_ = v_suppressElabErrors_2511_;
                v_inheritedTraceOptions_2460_ = v_inheritedTraceOptions_2512_;
                v___y_2461_ = v___y_2499_;
                state = 1;
                continue;
            }
            8 => {
                if v___y_2519_ == 0 {
                    v___x_2520_ = lean_st_ref_take(v___y_2517_);
                    v_env_2521_ = lean_ctor_get(v___x_2520_, 0);
                    v_nextMacroScope_2522_ = lean_ctor_get(v___x_2520_, 1);
                    v_ngen_2523_ = lean_ctor_get(v___x_2520_, 2);
                    v_auxDeclNGen_2524_ = lean_ctor_get(v___x_2520_, 3);
                    v_traceState_2525_ = lean_ctor_get(v___x_2520_, 4);
                    v_messages_2526_ = lean_ctor_get(v___x_2520_, 6);
                    v_infoState_2527_ = lean_ctor_get(v___x_2520_, 7);
                    v_snapshotTasks_2528_ = lean_ctor_get(v___x_2520_, 8);
                    v_isSharedCheck_2537_ = (!lean_is_exclusive(v___x_2520_)) as u8;
                    if v_isSharedCheck_2537_ == 0 {
                        v_unused_2538_ = lean_ctor_get(v___x_2520_, 5);
                        lean_dec(v_unused_2538_);
                        v___x_2530_ = v___x_2520_;
                        v_isShared_2531_ = v_isSharedCheck_2537_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_2528_);
                        lean_inc(v_infoState_2527_);
                        lean_inc(v_messages_2526_);
                        lean_inc(v_traceState_2525_);
                        lean_inc(v_auxDeclNGen_2524_);
                        lean_inc(v_ngen_2523_);
                        lean_inc(v_nextMacroScope_2522_);
                        lean_inc(v_env_2521_);
                        lean_dec(v___x_2520_);
                        v___x_2530_ = lean_box(0);
                        v_isShared_2531_ = v_isSharedCheck_2537_;
                        state = 9;
                        continue;
                    }
                } else {
                    v___y_2495_ = v___y_2514_;
                    v___y_2496_ = v___y_2515_;
                    v___y_2497_ = v___y_2518_;
                    v___y_2498_ = v___y_2516_;
                    v___y_2499_ = v___y_2517_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                v___x_2532_ = l_Lean_Kernel_enableDiag(v_env_2521_, v___y_2515_);
                if v_isShared_2531_ == 0 {
                    lean_ctor_set(v___x_2530_, 5, v___x_2431_);
                    lean_ctor_set(v___x_2530_, 0, v___x_2532_);
                    v___x_2534_ = v___x_2530_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2532_);
                    lean_ctor_set(v_reuseFailAlloc_2536_, 1, v_nextMacroScope_2522_);
                    lean_ctor_set(v_reuseFailAlloc_2536_, 2, v_ngen_2523_);
                    lean_ctor_set(v_reuseFailAlloc_2536_, 3, v_auxDeclNGen_2524_);
                    lean_ctor_set(v_reuseFailAlloc_2536_, 4, v_traceState_2525_);
                    lean_ctor_set(v_reuseFailAlloc_2536_, 5, v___x_2431_);
                    lean_ctor_set(v_reuseFailAlloc_2536_, 6, v_messages_2526_);
                    lean_ctor_set(v_reuseFailAlloc_2536_, 7, v_infoState_2527_);
                    lean_ctor_set(v_reuseFailAlloc_2536_, 8, v_snapshotTasks_2528_);
                    v___x_2534_ = v_reuseFailAlloc_2536_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2535_ = lean_st_ref_set(v___y_2517_, v___x_2534_);
                v___y_2495_ = v___y_2514_;
                v___y_2496_ = v___y_2515_;
                v___y_2497_ = v___y_2518_;
                v___y_2498_ = v___y_2516_;
                v___y_2499_ = v___y_2517_;
                state = 7;
                continue;
            }
            11 => {
                v___x_2556_ = lean_st_mk_ref(v___x_2550_);
                v___x_2557_ = lean_st_ref_get(v___y_2555_);
                v_fileName_2558_ = lean_ctor_get(v___y_2554_, 0);
                v_fileMap_2559_ = lean_ctor_get(v___y_2554_, 1);
                v_currRecDepth_2560_ = lean_ctor_get(v___y_2554_, 3);
                v_ref_2561_ = lean_ctor_get(v___y_2554_, 5);
                v_currNamespace_2562_ = lean_ctor_get(v___y_2554_, 6);
                v_openDecls_2563_ = lean_ctor_get(v___y_2554_, 7);
                v_initHeartbeats_2564_ = lean_ctor_get(v___y_2554_, 8);
                v_maxHeartbeats_2565_ = lean_ctor_get(v___y_2554_, 9);
                v_quotContext_2566_ = lean_ctor_get(v___y_2554_, 10);
                v_currMacroScope_2567_ = lean_ctor_get(v___y_2554_, 11);
                v_cancelTk_x3f_2568_ = lean_ctor_get(v___y_2554_, 12);
                v_suppressElabErrors_2569_ = lean_ctor_get_uint8(
                    v___y_2554_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2570_ = lean_ctor_get(v___y_2554_, 13);
                v_isSharedCheck_2582_ = (!lean_is_exclusive(v___y_2554_)) as u8;
                if v_isSharedCheck_2582_ == 0 {
                    v_unused_2583_ = lean_ctor_get(v___y_2554_, 4);
                    lean_dec(v_unused_2583_);
                    v_unused_2584_ = lean_ctor_get(v___y_2554_, 2);
                    lean_dec(v_unused_2584_);
                    v___x_2572_ = v___y_2554_;
                    v_isShared_2573_ = v_isSharedCheck_2582_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_inheritedTraceOptions_2570_);
                    lean_inc(v_cancelTk_x3f_2568_);
                    lean_inc(v_currMacroScope_2567_);
                    lean_inc(v_quotContext_2566_);
                    lean_inc(v_maxHeartbeats_2565_);
                    lean_inc(v_initHeartbeats_2564_);
                    lean_inc(v_openDecls_2563_);
                    lean_inc(v_currNamespace_2562_);
                    lean_inc(v_ref_2561_);
                    lean_inc(v_currRecDepth_2560_);
                    lean_inc(v_fileMap_2559_);
                    lean_inc(v_fileName_2558_);
                    lean_dec(v___y_2554_);
                    v___x_2572_ = lean_box(0);
                    v_isShared_2573_ = v_isSharedCheck_2582_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v_env_2574_ = lean_ctor_get(v___x_2557_, 0);
                lean_inc_ref(v_env_2574_);
                lean_dec(v___x_2557_);
                v___x_2575_ = l_Lean_maxRecDepth;
                v___x_2576_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__23),
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__23_once),
                    _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__23,
                );
                lean_inc_ref(v_inheritedTraceOptions_2570_);
                lean_inc(v_cancelTk_x3f_2568_);
                lean_inc(v_currMacroScope_2567_);
                lean_inc(v_quotContext_2566_);
                lean_inc(v_maxHeartbeats_2565_);
                lean_inc(v_initHeartbeats_2564_);
                lean_inc(v_openDecls_2563_);
                lean_inc(v_currNamespace_2562_);
                lean_inc(v_ref_2561_);
                lean_inc(v_currRecDepth_2560_);
                lean_inc_ref(v_fileMap_2559_);
                lean_inc_ref(v_fileName_2558_);
                if v_isShared_2573_ == 0 {
                    lean_ctor_set(v___x_2572_, 4, v___x_2576_);
                    lean_ctor_set(v___x_2572_, 2, v___x_2544_);
                    v___x_2578_ = v___x_2572_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 14, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_fileName_2558_);
                    lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_fileMap_2559_);
                    lean_ctor_set(v_reuseFailAlloc_2581_, 2, v___x_2544_);
                    lean_ctor_set(v_reuseFailAlloc_2581_, 3, v_currRecDepth_2560_);
                    lean_ctor_set(v_reuseFailAlloc_2581_, 4, v___x_2576_);
                    lean_ctor_set(v_reuseFailAlloc_2581_, 5, v_ref_2561_);
                    lean_ctor_set(v_reuseFailAlloc_2581_, 6, v_currNamespace_2562_);
                    lean_ctor_set(v_reuseFailAlloc_2581_, 7, v_openDecls_2563_);
                    lean_ctor_set(v_reuseFailAlloc_2581_, 8, v_initHeartbeats_2564_);
                    lean_ctor_set(v_reuseFailAlloc_2581_, 9, v_maxHeartbeats_2565_);
                    lean_ctor_set(v_reuseFailAlloc_2581_, 10, v_quotContext_2566_);
                    lean_ctor_set(v_reuseFailAlloc_2581_, 11, v_currMacroScope_2567_);
                    lean_ctor_set(v_reuseFailAlloc_2581_, 12, v_cancelTk_x3f_2568_);
                    lean_ctor_set(v_reuseFailAlloc_2581_, 13, v_inheritedTraceOptions_2570_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2581_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_2569_,
                    );
                    v___x_2578_ = v_reuseFailAlloc_2581_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                lean_ctor_set_uint8(
                    v___x_2578_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v___x_2552_,
                );
                v___x_2579_ = l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(v_opts_2417_, v___x_2551_);
                v___x_2580_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2574_);
                lean_dec_ref(v_env_2574_);
                if v___x_2580_ == 0 {
                    if v___x_2579_ == 0 {
                        lean_dec_ref(v___x_2578_);
                        v___y_2445_ = v___x_2556_;
                        v___y_2446_ = v___x_2579_;
                        v___y_2447_ = v___x_2575_;
                        v_fileName_2448_ = v_fileName_2558_;
                        v_fileMap_2449_ = v_fileMap_2559_;
                        v_currRecDepth_2450_ = v_currRecDepth_2560_;
                        v_ref_2451_ = v_ref_2561_;
                        v_currNamespace_2452_ = v_currNamespace_2562_;
                        v_openDecls_2453_ = v_openDecls_2563_;
                        v_initHeartbeats_2454_ = v_initHeartbeats_2564_;
                        v_maxHeartbeats_2455_ = v_maxHeartbeats_2565_;
                        v_quotContext_2456_ = v_quotContext_2566_;
                        v_currMacroScope_2457_ = v_currMacroScope_2567_;
                        v_cancelTk_x3f_2458_ = v_cancelTk_x3f_2568_;
                        v_suppressElabErrors_2459_ = v_suppressElabErrors_2569_;
                        v_inheritedTraceOptions_2460_ = v_inheritedTraceOptions_2570_;
                        v___y_2461_ = v___y_2555_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_inheritedTraceOptions_2570_);
                        lean_dec(v_cancelTk_x3f_2568_);
                        lean_dec(v_currMacroScope_2567_);
                        lean_dec(v_quotContext_2566_);
                        lean_dec(v_maxHeartbeats_2565_);
                        lean_dec(v_initHeartbeats_2564_);
                        lean_dec(v_openDecls_2563_);
                        lean_dec(v_currNamespace_2562_);
                        lean_dec(v_ref_2561_);
                        lean_dec(v_currRecDepth_2560_);
                        lean_dec_ref(v_fileMap_2559_);
                        lean_dec_ref(v_fileName_2558_);
                        v___y_2514_ = v___x_2556_;
                        v___y_2515_ = v___x_2579_;
                        v___y_2516_ = v___x_2578_;
                        v___y_2517_ = v___y_2555_;
                        v___y_2518_ = v___x_2575_;
                        v___y_2519_ = v___x_2580_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_inheritedTraceOptions_2570_);
                    lean_dec(v_cancelTk_x3f_2568_);
                    lean_dec(v_currMacroScope_2567_);
                    lean_dec(v_quotContext_2566_);
                    lean_dec(v_maxHeartbeats_2565_);
                    lean_dec(v_initHeartbeats_2564_);
                    lean_dec(v_openDecls_2563_);
                    lean_dec(v_currNamespace_2562_);
                    lean_dec(v_ref_2561_);
                    lean_dec(v_currRecDepth_2560_);
                    lean_dec_ref(v_fileMap_2559_);
                    lean_dec_ref(v_fileName_2558_);
                    v___y_2514_ = v___x_2556_;
                    v___y_2515_ = v___x_2579_;
                    v___y_2516_ = v___x_2578_;
                    v___y_2517_ = v___y_2555_;
                    v___y_2518_ = v___x_2575_;
                    v___y_2519_ = v___x_2579_;
                    state = 8;
                    continue;
                }
            }
            14 => {
                if v___y_2586_ == 0 {
                    v___x_2587_ = lean_st_ref_take(v___x_2443_);
                    v_env_2588_ = lean_ctor_get(v___x_2587_, 0);
                    v_nextMacroScope_2589_ = lean_ctor_get(v___x_2587_, 1);
                    v_ngen_2590_ = lean_ctor_get(v___x_2587_, 2);
                    v_auxDeclNGen_2591_ = lean_ctor_get(v___x_2587_, 3);
                    v_traceState_2592_ = lean_ctor_get(v___x_2587_, 4);
                    v_messages_2593_ = lean_ctor_get(v___x_2587_, 6);
                    v_infoState_2594_ = lean_ctor_get(v___x_2587_, 7);
                    v_snapshotTasks_2595_ = lean_ctor_get(v___x_2587_, 8);
                    v_isSharedCheck_2604_ = (!lean_is_exclusive(v___x_2587_)) as u8;
                    if v_isSharedCheck_2604_ == 0 {
                        v_unused_2605_ = lean_ctor_get(v___x_2587_, 5);
                        lean_dec(v_unused_2605_);
                        v___x_2597_ = v___x_2587_;
                        v_isShared_2598_ = v_isSharedCheck_2604_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_2595_);
                        lean_inc(v_infoState_2594_);
                        lean_inc(v_messages_2593_);
                        lean_inc(v_traceState_2592_);
                        lean_inc(v_auxDeclNGen_2591_);
                        lean_inc(v_ngen_2590_);
                        lean_inc(v_nextMacroScope_2589_);
                        lean_inc(v_env_2588_);
                        lean_dec(v___x_2587_);
                        v___x_2597_ = lean_box(0);
                        v_isShared_2598_ = v_isSharedCheck_2604_;
                        state = 15;
                        continue;
                    }
                } else {
                    lean_inc(v___x_2443_);
                    v___y_2554_ = v___x_2548_;
                    v___y_2555_ = v___x_2443_;
                    state = 11;
                    continue;
                }
            }
            15 => {
                v___x_2599_ = l_Lean_Kernel_enableDiag(v_env_2588_, v___x_2552_);
                if v_isShared_2598_ == 0 {
                    lean_ctor_set(v___x_2597_, 5, v___x_2431_);
                    lean_ctor_set(v___x_2597_, 0, v___x_2599_);
                    v___x_2601_ = v___x_2597_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2599_);
                    lean_ctor_set(v_reuseFailAlloc_2603_, 1, v_nextMacroScope_2589_);
                    lean_ctor_set(v_reuseFailAlloc_2603_, 2, v_ngen_2590_);
                    lean_ctor_set(v_reuseFailAlloc_2603_, 3, v_auxDeclNGen_2591_);
                    lean_ctor_set(v_reuseFailAlloc_2603_, 4, v_traceState_2592_);
                    lean_ctor_set(v_reuseFailAlloc_2603_, 5, v___x_2431_);
                    lean_ctor_set(v_reuseFailAlloc_2603_, 6, v_messages_2593_);
                    lean_ctor_set(v_reuseFailAlloc_2603_, 7, v_infoState_2594_);
                    lean_ctor_set(v_reuseFailAlloc_2603_, 8, v_snapshotTasks_2595_);
                    v___x_2601_ = v_reuseFailAlloc_2603_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_2602_ = lean_st_ref_set(v___x_2443_, v___x_2601_);
                lean_inc(v___x_2443_);
                v___y_2554_ = v___x_2548_;
                v___y_2555_ = v___x_2443_;
                state = 11;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PrettyPrinter_ppExprLegacy___boxed(
    mut v_env_2607_: *mut LeanObject,
    mut v_mctx_2608_: *mut LeanObject,
    mut v_lctx_2609_: *mut LeanObject,
    mut v_opts_2610_: *mut LeanObject,
    mut v_e_2611_: *mut LeanObject,
    mut v_a_2612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2613_: *mut LeanObject = core::ptr::null_mut();
    v_res_2613_ = l_Lean_PrettyPrinter_ppExprLegacy(
        v_env_2607_,
        v_mctx_2608_,
        v_lctx_2609_,
        v_opts_2610_,
        v_e_2611_,
    );
    return v_res_2613_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppLevel(
    mut v_l_2617_: *mut LeanObject,
    mut v_a_2618_: *mut LeanObject,
    mut v_a_2619_: *mut LeanObject,
    mut v_a_2620_: *mut LeanObject,
    mut v_a_2621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2631_: u8 = 0;
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2635_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2623_ = lean_unsigned_to_nat(0);
                v___x_2624_ = l_Lean_PrettyPrinter_delabLevel(
                    v_l_2617_,
                    v___x_2623_,
                    v_a_2618_,
                    v_a_2619_,
                    v_a_2620_,
                    v_a_2621_,
                );
                if lean_obj_tag(v___x_2624_) == 0 {
                    v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
                    lean_inc(v_a_2625_);
                    lean_dec_ref_known(v___x_2624_, 1);
                    v___x_2626_ = l_Lean_PrettyPrinter_ppLevel___closed__1;
                    v___x_2627_ = l_Lean_PrettyPrinter_ppCategory(
                        v___x_2626_,
                        v_a_2625_,
                        v_a_2620_,
                        v_a_2621_,
                    );
                    return v___x_2627_;
                } else {
                    v_a_2628_ = lean_ctor_get(v___x_2624_, 0);
                    v_isSharedCheck_2635_ = (!lean_is_exclusive(v___x_2624_)) as u8;
                    if v_isSharedCheck_2635_ == 0 {
                        v___x_2630_ = v___x_2624_;
                        v_isShared_2631_ = v_isSharedCheck_2635_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2628_);
                        lean_dec(v___x_2624_);
                        v___x_2630_ = lean_box(0);
                        v_isShared_2631_ = v_isSharedCheck_2635_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2631_ == 0 {
                    v___x_2633_ = v___x_2630_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
                    v___x_2633_ = v_reuseFailAlloc_2634_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2633_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PrettyPrinter_ppLevel___boxed(
    mut v_l_2636_: *mut LeanObject,
    mut v_a_2637_: *mut LeanObject,
    mut v_a_2638_: *mut LeanObject,
    mut v_a_2639_: *mut LeanObject,
    mut v_a_2640_: *mut LeanObject,
    mut v_a_2641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2642_: *mut LeanObject = core::ptr::null_mut();
    v_res_2642_ =
        l_Lean_PrettyPrinter_ppLevel(v_l_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_);
    lean_dec(v_a_2640_);
    lean_dec_ref(v_a_2639_);
    lean_dec(v_a_2638_);
    lean_dec_ref(v_a_2637_);
    return v_res_2642_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppTactic(
    mut v_stx_2646_: *mut LeanObject,
    mut v_a_2647_: *mut LeanObject,
    mut v_a_2648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    v___x_2650_ = l_Lean_PrettyPrinter_ppTactic___closed__1;
    v___x_2651_ = l_Lean_PrettyPrinter_ppCategory(v___x_2650_, v_stx_2646_, v_a_2647_, v_a_2648_);
    return v___x_2651_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppTactic___boxed(
    mut v_stx_2652_: *mut LeanObject,
    mut v_a_2653_: *mut LeanObject,
    mut v_a_2654_: *mut LeanObject,
    mut v_a_2655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2656_: *mut LeanObject = core::ptr::null_mut();
    v_res_2656_ = l_Lean_PrettyPrinter_ppTactic(v_stx_2652_, v_a_2653_, v_a_2654_);
    lean_dec(v_a_2654_);
    lean_dec_ref(v_a_2653_);
    return v_res_2656_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppCommand(
    mut v_stx_2660_: *mut LeanObject,
    mut v_a_2661_: *mut LeanObject,
    mut v_a_2662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    v___x_2664_ = l_Lean_PrettyPrinter_ppCommand___closed__1;
    v___x_2665_ = l_Lean_PrettyPrinter_ppCategory(v___x_2664_, v_stx_2660_, v_a_2661_, v_a_2662_);
    return v___x_2665_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppCommand___boxed(
    mut v_stx_2666_: *mut LeanObject,
    mut v_a_2667_: *mut LeanObject,
    mut v_a_2668_: *mut LeanObject,
    mut v_a_2669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2670_: *mut LeanObject = core::ptr::null_mut();
    v_res_2670_ = l_Lean_PrettyPrinter_ppCommand(v_stx_2666_, v_a_2667_, v_a_2668_);
    lean_dec(v_a_2668_);
    lean_dec_ref(v_a_2667_);
    return v_res_2670_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppModule(
    mut v_stx_2673_: *mut LeanObject,
    mut v_a_2674_: *mut LeanObject,
    mut v_a_2675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2685_: u8 = 0;
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2689_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2677_ = l_Lean_PrettyPrinter_ppModule___closed__0;
                v___x_2678_ = l_Lean_PrettyPrinter_parenthesize(
                    v___x_2677_,
                    v_stx_2673_,
                    v_a_2674_,
                    v_a_2675_,
                );
                if lean_obj_tag(v___x_2678_) == 0 {
                    v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
                    lean_inc(v_a_2679_);
                    lean_dec_ref_known(v___x_2678_, 1);
                    v___x_2680_ = l_Lean_PrettyPrinter_ppModule___closed__1;
                    v___x_2681_ =
                        l_Lean_PrettyPrinter_format(v___x_2680_, v_a_2679_, v_a_2674_, v_a_2675_);
                    return v___x_2681_;
                } else {
                    v_a_2682_ = lean_ctor_get(v___x_2678_, 0);
                    v_isSharedCheck_2689_ = (!lean_is_exclusive(v___x_2678_)) as u8;
                    if v_isSharedCheck_2689_ == 0 {
                        v___x_2684_ = v___x_2678_;
                        v_isShared_2685_ = v_isSharedCheck_2689_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2682_);
                        lean_dec(v___x_2678_);
                        v___x_2684_ = lean_box(0);
                        v_isShared_2685_ = v_isSharedCheck_2689_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2685_ == 0 {
                    v___x_2687_ = v___x_2684_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2682_);
                    v___x_2687_ = v_reuseFailAlloc_2688_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2687_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PrettyPrinter_ppModule___boxed(
    mut v_stx_2690_: *mut LeanObject,
    mut v_a_2691_: *mut LeanObject,
    mut v_a_2692_: *mut LeanObject,
    mut v_a_2693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2694_: *mut LeanObject = core::ptr::null_mut();
    v_res_2694_ = l_Lean_PrettyPrinter_ppModule(v_stx_2690_, v_a_2691_, v_a_2692_);
    lean_dec(v_a_2692_);
    lean_dec_ref(v_a_2691_);
    return v_res_2694_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    v___x_2695_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2695_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    v___x_2696_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
    v___x_2697_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2697_, 0, v___x_2696_);
    return v___x_2697_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    v___x_2698_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_2699_ = lean_unsigned_to_nat(0);
    v___x_2700_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_2700_, 0, v___x_2699_);
    lean_ctor_set(v___x_2700_, 1, v___x_2699_);
    lean_ctor_set(v___x_2700_, 2, v___x_2699_);
    lean_ctor_set(v___x_2700_, 3, v___x_2699_);
    lean_ctor_set(v___x_2700_, 4, v___x_2698_);
    lean_ctor_set(v___x_2700_, 5, v___x_2698_);
    lean_ctor_set(v___x_2700_, 6, v___x_2698_);
    lean_ctor_set(v___x_2700_, 7, v___x_2698_);
    lean_ctor_set(v___x_2700_, 8, v___x_2698_);
    lean_ctor_set(v___x_2700_, 9, v___x_2698_);
    return v___x_2700_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    v___x_2701_ = lean_unsigned_to_nat(32);
    v___x_2702_ = lean_mk_empty_array_with_capacity(v___x_2701_);
    v___x_2703_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2703_, 0, v___x_2702_);
    return v___x_2703_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_2704_: usize = 0;
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    v___x_2704_ = 5usize;
    v___x_2705_ = lean_unsigned_to_nat(0);
    v___x_2706_ = lean_unsigned_to_nat(32);
    v___x_2707_ = lean_mk_empty_array_with_capacity(v___x_2706_);
    v___x_2708_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
    v___x_2709_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_2709_, 0, v___x_2708_);
    lean_ctor_set(v___x_2709_, 1, v___x_2707_);
    lean_ctor_set(v___x_2709_, 2, v___x_2705_);
    lean_ctor_set(v___x_2709_, 3, v___x_2705_);
    lean_ctor_set_usize(v___x_2709_, 4, v___x_2704_);
    return v___x_2709_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    v___x_2710_ = lean_box(1);
    v___x_2711_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
    v___x_2712_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_2713_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2713_, 0, v___x_2712_);
    lean_ctor_set(v___x_2713_, 1, v___x_2711_);
    lean_ctor_set(v___x_2713_, 2, v___x_2710_);
    return v___x_2713_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    v___x_2715_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6;
    v___x_2716_ = l_Lean_stringToMessageData(v___x_2715_);
    return v___x_2716_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    v___x_2718_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8;
    v___x_2719_ = l_Lean_stringToMessageData(v___x_2718_);
    return v___x_2719_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    v___x_2721_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10;
    v___x_2722_ = l_Lean_stringToMessageData(v___x_2721_);
    return v___x_2722_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    v___x_2724_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12;
    v___x_2725_ = l_Lean_stringToMessageData(v___x_2724_);
    return v___x_2725_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    v___x_2727_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14;
    v___x_2728_ = l_Lean_stringToMessageData(v___x_2727_);
    return v___x_2728_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    v___x_2730_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16;
    v___x_2731_ = l_Lean_stringToMessageData(v___x_2730_);
    return v___x_2731_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    v___x_2733_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18;
    v___x_2734_ = l_Lean_stringToMessageData(v___x_2733_);
    return v___x_2734_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_msg_2735_: *mut LeanObject,
    mut v_declHint_2736_: *mut LeanObject,
    mut v___y_2737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: u8 = 0;
    let mut v_isExporting_2742_: u8 = 0;
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: u8 = 0;
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2764_: u8 = 0;
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: u8 = 0;
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2796_: u8 = 0;
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2739_ = lean_st_ref_get(v___y_2737_);
                v_env_2740_ = lean_ctor_get(v___x_2739_, 0);
                lean_inc_ref(v_env_2740_);
                lean_dec(v___x_2739_);
                v___x_2741_ = l_Lean_Name_isAnonymous(v_declHint_2736_);
                if v___x_2741_ == 0 {
                    v_isExporting_2742_ = lean_ctor_get_uint8(
                        v_env_2740_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_2742_ == 0 {
                        lean_dec_ref(v_env_2740_);
                        lean_dec(v_declHint_2736_);
                        v___x_2743_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2743_, 0, v_msg_2735_);
                        return v___x_2743_;
                    } else {
                        lean_inc_ref(v_env_2740_);
                        v___x_2744_ = l_Lean_Environment_setExporting(v_env_2740_, v___x_2741_);
                        lean_inc(v_declHint_2736_);
                        lean_inc_ref(v___x_2744_);
                        v___x_2745_ = l_Lean_Environment_contains(
                            v___x_2744_,
                            v_declHint_2736_,
                            v_isExporting_2742_,
                        );
                        if v___x_2745_ == 0 {
                            lean_dec_ref(v___x_2744_);
                            lean_dec_ref(v_env_2740_);
                            lean_dec(v_declHint_2736_);
                            v___x_2746_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_2746_, 0, v_msg_2735_);
                            return v___x_2746_;
                        } else {
                            v___x_2747_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
                            v___x_2748_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                            v___x_2749_ = l_Lean_Options_empty;
                            v___x_2750_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_2750_, 0, v___x_2744_);
                            lean_ctor_set(v___x_2750_, 1, v___x_2747_);
                            lean_ctor_set(v___x_2750_, 2, v___x_2748_);
                            lean_ctor_set(v___x_2750_, 3, v___x_2749_);
                            lean_inc(v_declHint_2736_);
                            v___x_2751_ =
                                l_Lean_MessageData_ofConstName(v_declHint_2736_, v___x_2741_);
                            v_c_2752_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_2752_, 0, v___x_2750_);
                            lean_ctor_set(v_c_2752_, 1, v___x_2751_);
                            v___x_2753_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_2740_,
                                v_declHint_2736_,
                            );
                            if lean_obj_tag(v___x_2753_) == 0 {
                                lean_dec_ref(v_env_2740_);
                                lean_dec(v_declHint_2736_);
                                v___x_2754_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                                v___x_2755_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2755_, 0, v___x_2754_);
                                lean_ctor_set(v___x_2755_, 1, v_c_2752_);
                                v___x_2756_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
                                v___x_2757_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2757_, 0, v___x_2755_);
                                lean_ctor_set(v___x_2757_, 1, v___x_2756_);
                                v___x_2758_ = l_Lean_MessageData_note(v___x_2757_);
                                v___x_2759_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2759_, 0, v_msg_2735_);
                                lean_ctor_set(v___x_2759_, 1, v___x_2758_);
                                v___x_2760_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_2760_, 0, v___x_2759_);
                                return v___x_2760_;
                            } else {
                                v_val_2761_ = lean_ctor_get(v___x_2753_, 0);
                                v_isSharedCheck_2796_ = (!lean_is_exclusive(v___x_2753_)) as u8;
                                if v_isSharedCheck_2796_ == 0 {
                                    v___x_2763_ = v___x_2753_;
                                    v_isShared_2764_ = v_isSharedCheck_2796_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_2761_);
                                    lean_dec(v___x_2753_);
                                    v___x_2763_ = lean_box(0);
                                    v_isShared_2764_ = v_isSharedCheck_2796_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_2740_);
                    lean_dec(v_declHint_2736_);
                    v___x_2797_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2797_, 0, v_msg_2735_);
                    return v___x_2797_;
                }
            }
            1 => {
                v___x_2765_ = lean_box(0);
                v___x_2766_ = l_Lean_Environment_header(v_env_2740_);
                lean_dec_ref(v_env_2740_);
                v___x_2767_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2766_);
                v_mod_2768_ = lean_array_get(v___x_2765_, v___x_2767_, v_val_2761_);
                lean_dec(v_val_2761_);
                lean_dec_ref(v___x_2767_);
                v___x_2769_ = l_Lean_isPrivateName(v_declHint_2736_);
                lean_dec(v_declHint_2736_);
                if v___x_2769_ == 0 {
                    v___x_2770_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
                    v___x_2771_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2771_, 0, v___x_2770_);
                    lean_ctor_set(v___x_2771_, 1, v_c_2752_);
                    v___x_2772_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
                    v___x_2773_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2773_, 0, v___x_2771_);
                    lean_ctor_set(v___x_2773_, 1, v___x_2772_);
                    v___x_2774_ = l_Lean_MessageData_ofName(v_mod_2768_);
                    v___x_2775_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2775_, 0, v___x_2773_);
                    lean_ctor_set(v___x_2775_, 1, v___x_2774_);
                    v___x_2776_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
                    v___x_2777_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2777_, 0, v___x_2775_);
                    lean_ctor_set(v___x_2777_, 1, v___x_2776_);
                    v___x_2778_ = l_Lean_MessageData_note(v___x_2777_);
                    v___x_2779_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2779_, 0, v_msg_2735_);
                    lean_ctor_set(v___x_2779_, 1, v___x_2778_);
                    if v_isShared_2764_ == 0 {
                        lean_ctor_set_tag(v___x_2763_, 0);
                        lean_ctor_set(v___x_2763_, 0, v___x_2779_);
                        v___x_2781_ = v___x_2763_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2779_);
                        v___x_2781_ = v_reuseFailAlloc_2782_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2783_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                    v___x_2784_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2784_, 0, v___x_2783_);
                    lean_ctor_set(v___x_2784_, 1, v_c_2752_);
                    v___x_2785_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
                    v___x_2786_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2786_, 0, v___x_2784_);
                    lean_ctor_set(v___x_2786_, 1, v___x_2785_);
                    v___x_2787_ = l_Lean_MessageData_ofName(v_mod_2768_);
                    v___x_2788_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2788_, 0, v___x_2786_);
                    lean_ctor_set(v___x_2788_, 1, v___x_2787_);
                    v___x_2789_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
                    v___x_2790_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2790_, 0, v___x_2788_);
                    lean_ctor_set(v___x_2790_, 1, v___x_2789_);
                    v___x_2791_ = l_Lean_MessageData_note(v___x_2790_);
                    v___x_2792_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2792_, 0, v_msg_2735_);
                    lean_ctor_set(v___x_2792_, 1, v___x_2791_);
                    if v_isShared_2764_ == 0 {
                        lean_ctor_set_tag(v___x_2763_, 0);
                        lean_ctor_set(v___x_2763_, 0, v___x_2792_);
                        v___x_2794_ = v___x_2763_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2792_);
                        v___x_2794_ = v_reuseFailAlloc_2795_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2781_;
            }
            3 => {
                return v___x_2794_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_msg_2798_: *mut LeanObject,
    mut v_declHint_2799_: *mut LeanObject,
    mut v___y_2800_: *mut LeanObject,
    mut v___y_2801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2802_: *mut LeanObject = core::ptr::null_mut();
    v_res_2802_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2798_, v_declHint_2799_, v___y_2800_);
    lean_dec(v___y_2800_);
    return v_res_2802_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_msg_2803_: *mut LeanObject,
    mut v_declHint_2804_: *mut LeanObject,
    mut v___y_2805_: *mut LeanObject,
    mut v___y_2806_: *mut LeanObject,
    mut v___y_2807_: *mut LeanObject,
    mut v___y_2808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2814_: u8 = 0;
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2820_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2810_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2803_, v_declHint_2804_, v___y_2808_);
                v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
                v_isSharedCheck_2820_ = (!lean_is_exclusive(v___x_2810_)) as u8;
                if v_isSharedCheck_2820_ == 0 {
                    v___x_2813_ = v___x_2810_;
                    v_isShared_2814_ = v_isSharedCheck_2820_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2811_);
                    lean_dec(v___x_2810_);
                    v___x_2813_ = lean_box(0);
                    v_isShared_2814_ = v_isSharedCheck_2820_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2815_ = l_Lean_unknownIdentifierMessageTag;
                v___x_2816_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_2816_, 0, v___x_2815_);
                lean_ctor_set(v___x_2816_, 1, v_a_2811_);
                if v_isShared_2814_ == 0 {
                    lean_ctor_set(v___x_2813_, 0, v___x_2816_);
                    v___x_2818_ = v___x_2813_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2819_, 0, v___x_2816_);
                    v___x_2818_ = v_reuseFailAlloc_2819_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2818_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(
    mut v_msg_2821_: *mut LeanObject,
    mut v_declHint_2822_: *mut LeanObject,
    mut v___y_2823_: *mut LeanObject,
    mut v___y_2824_: *mut LeanObject,
    mut v___y_2825_: *mut LeanObject,
    mut v___y_2826_: *mut LeanObject,
    mut v___y_2827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2828_: *mut LeanObject = core::ptr::null_mut();
    v_res_2828_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2821_, v_declHint_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
    lean_dec(v___y_2826_);
    lean_dec_ref(v___y_2825_);
    lean_dec(v___y_2824_);
    lean_dec_ref(v___y_2823_);
    return v_res_2828_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(
    mut v_msgData_2829_: *mut LeanObject,
    mut v___y_2830_: *mut LeanObject,
    mut v___y_2831_: *mut LeanObject,
    mut v___y_2832_: *mut LeanObject,
    mut v___y_2833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    v___x_2835_ = lean_st_ref_get(v___y_2833_);
    v_env_2836_ = lean_ctor_get(v___x_2835_, 0);
    lean_inc_ref(v_env_2836_);
    lean_dec(v___x_2835_);
    v___x_2837_ = lean_st_ref_get(v___y_2831_);
    v_mctx_2838_ = lean_ctor_get(v___x_2837_, 0);
    lean_inc_ref(v_mctx_2838_);
    lean_dec(v___x_2837_);
    v_lctx_2839_ = lean_ctor_get(v___y_2830_, 2);
    v_options_2840_ = lean_ctor_get(v___y_2832_, 2);
    lean_inc_ref(v_options_2840_);
    lean_inc_ref(v_lctx_2839_);
    v___x_2841_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2841_, 0, v_env_2836_);
    lean_ctor_set(v___x_2841_, 1, v_mctx_2838_);
    lean_ctor_set(v___x_2841_, 2, v_lctx_2839_);
    lean_ctor_set(v___x_2841_, 3, v_options_2840_);
    v___x_2842_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2842_, 0, v___x_2841_);
    lean_ctor_set(v___x_2842_, 1, v_msgData_2829_);
    v___x_2843_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2843_, 0, v___x_2842_);
    return v___x_2843_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(
    mut v_msgData_2844_: *mut LeanObject,
    mut v___y_2845_: *mut LeanObject,
    mut v___y_2846_: *mut LeanObject,
    mut v___y_2847_: *mut LeanObject,
    mut v___y_2848_: *mut LeanObject,
    mut v___y_2849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2850_: *mut LeanObject = core::ptr::null_mut();
    v_res_2850_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
    lean_dec(v___y_2848_);
    lean_dec_ref(v___y_2847_);
    lean_dec(v___y_2846_);
    lean_dec_ref(v___y_2845_);
    return v_res_2850_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_msg_2851_: *mut LeanObject,
    mut v___y_2852_: *mut LeanObject,
    mut v___y_2853_: *mut LeanObject,
    mut v___y_2854_: *mut LeanObject,
    mut v___y_2855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2862_: u8 = 0;
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2857_ = lean_ctor_get(v___y_2854_, 5);
                v___x_2858_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
                v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
                v_isSharedCheck_2867_ = (!lean_is_exclusive(v___x_2858_)) as u8;
                if v_isSharedCheck_2867_ == 0 {
                    v___x_2861_ = v___x_2858_;
                    v_isShared_2862_ = v_isSharedCheck_2867_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2859_);
                    lean_dec(v___x_2858_);
                    v___x_2861_ = lean_box(0);
                    v_isShared_2862_ = v_isSharedCheck_2867_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2857_);
                v___x_2863_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2863_, 0, v_ref_2857_);
                lean_ctor_set(v___x_2863_, 1, v_a_2859_);
                if v_isShared_2862_ == 0 {
                    lean_ctor_set_tag(v___x_2861_, 1);
                    lean_ctor_set(v___x_2861_, 0, v___x_2863_);
                    v___x_2865_ = v___x_2861_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2866_, 0, v___x_2863_);
                    v___x_2865_ = v_reuseFailAlloc_2866_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(
    mut v_msg_2868_: *mut LeanObject,
    mut v___y_2869_: *mut LeanObject,
    mut v___y_2870_: *mut LeanObject,
    mut v___y_2871_: *mut LeanObject,
    mut v___y_2872_: *mut LeanObject,
    mut v___y_2873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2874_: *mut LeanObject = core::ptr::null_mut();
    v_res_2874_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
    lean_dec(v___y_2872_);
    lean_dec_ref(v___y_2871_);
    lean_dec(v___y_2870_);
    lean_dec_ref(v___y_2869_);
    return v_res_2874_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_ref_2875_: *mut LeanObject,
    mut v_msg_2876_: *mut LeanObject,
    mut v___y_2877_: *mut LeanObject,
    mut v___y_2878_: *mut LeanObject,
    mut v___y_2879_: *mut LeanObject,
    mut v___y_2880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2894_: u8 = 0;
    let mut v_cancelTk_x3f_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2896_: u8 = 0;
    let mut v_inheritedTraceOptions_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_2882_ = lean_ctor_get(v___y_2879_, 0);
    v_fileMap_2883_ = lean_ctor_get(v___y_2879_, 1);
    v_options_2884_ = lean_ctor_get(v___y_2879_, 2);
    v_currRecDepth_2885_ = lean_ctor_get(v___y_2879_, 3);
    v_maxRecDepth_2886_ = lean_ctor_get(v___y_2879_, 4);
    v_ref_2887_ = lean_ctor_get(v___y_2879_, 5);
    v_currNamespace_2888_ = lean_ctor_get(v___y_2879_, 6);
    v_openDecls_2889_ = lean_ctor_get(v___y_2879_, 7);
    v_initHeartbeats_2890_ = lean_ctor_get(v___y_2879_, 8);
    v_maxHeartbeats_2891_ = lean_ctor_get(v___y_2879_, 9);
    v_quotContext_2892_ = lean_ctor_get(v___y_2879_, 10);
    v_currMacroScope_2893_ = lean_ctor_get(v___y_2879_, 11);
    v_diag_2894_ = lean_ctor_get_uint8(
        v___y_2879_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2895_ = lean_ctor_get(v___y_2879_, 12);
    v_suppressElabErrors_2896_ = lean_ctor_get_uint8(
        v___y_2879_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_2897_ = lean_ctor_get(v___y_2879_, 13);
    v_ref_2898_ = l_Lean_replaceRef(v_ref_2875_, v_ref_2887_);
    lean_inc_ref(v_inheritedTraceOptions_2897_);
    lean_inc(v_cancelTk_x3f_2895_);
    lean_inc(v_currMacroScope_2893_);
    lean_inc(v_quotContext_2892_);
    lean_inc(v_maxHeartbeats_2891_);
    lean_inc(v_initHeartbeats_2890_);
    lean_inc(v_openDecls_2889_);
    lean_inc(v_currNamespace_2888_);
    lean_inc(v_maxRecDepth_2886_);
    lean_inc(v_currRecDepth_2885_);
    lean_inc_ref(v_options_2884_);
    lean_inc_ref(v_fileMap_2883_);
    lean_inc_ref(v_fileName_2882_);
    v___x_2899_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_2899_, 0, v_fileName_2882_);
    lean_ctor_set(v___x_2899_, 1, v_fileMap_2883_);
    lean_ctor_set(v___x_2899_, 2, v_options_2884_);
    lean_ctor_set(v___x_2899_, 3, v_currRecDepth_2885_);
    lean_ctor_set(v___x_2899_, 4, v_maxRecDepth_2886_);
    lean_ctor_set(v___x_2899_, 5, v_ref_2898_);
    lean_ctor_set(v___x_2899_, 6, v_currNamespace_2888_);
    lean_ctor_set(v___x_2899_, 7, v_openDecls_2889_);
    lean_ctor_set(v___x_2899_, 8, v_initHeartbeats_2890_);
    lean_ctor_set(v___x_2899_, 9, v_maxHeartbeats_2891_);
    lean_ctor_set(v___x_2899_, 10, v_quotContext_2892_);
    lean_ctor_set(v___x_2899_, 11, v_currMacroScope_2893_);
    lean_ctor_set(v___x_2899_, 12, v_cancelTk_x3f_2895_);
    lean_ctor_set(v___x_2899_, 13, v_inheritedTraceOptions_2897_);
    lean_ctor_set_uint8(
        v___x_2899_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_2894_,
    );
    lean_ctor_set_uint8(
        v___x_2899_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_2896_,
    );
    v___x_2900_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2876_, v___y_2877_, v___y_2878_, v___x_2899_, v___y_2880_);
    lean_dec_ref_known(v___x_2899_, 14);
    return v___x_2900_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_ref_2901_: *mut LeanObject,
    mut v_msg_2902_: *mut LeanObject,
    mut v___y_2903_: *mut LeanObject,
    mut v___y_2904_: *mut LeanObject,
    mut v___y_2905_: *mut LeanObject,
    mut v___y_2906_: *mut LeanObject,
    mut v___y_2907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2908_: *mut LeanObject = core::ptr::null_mut();
    v_res_2908_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2901_, v_msg_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
    lean_dec(v___y_2906_);
    lean_dec_ref(v___y_2905_);
    lean_dec(v___y_2904_);
    lean_dec_ref(v___y_2903_);
    lean_dec(v_ref_2901_);
    return v_res_2908_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_2909_: *mut LeanObject,
    mut v_msg_2910_: *mut LeanObject,
    mut v_declHint_2911_: *mut LeanObject,
    mut v___y_2912_: *mut LeanObject,
    mut v___y_2913_: *mut LeanObject,
    mut v___y_2914_: *mut LeanObject,
    mut v___y_2915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    v___x_2917_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2910_, v_declHint_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
    v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
    lean_inc(v_a_2918_);
    lean_dec_ref(v___x_2917_);
    v___x_2919_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2909_, v_a_2918_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
    return v___x_2919_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_2920_: *mut LeanObject,
    mut v_msg_2921_: *mut LeanObject,
    mut v_declHint_2922_: *mut LeanObject,
    mut v___y_2923_: *mut LeanObject,
    mut v___y_2924_: *mut LeanObject,
    mut v___y_2925_: *mut LeanObject,
    mut v___y_2926_: *mut LeanObject,
    mut v___y_2927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2928_: *mut LeanObject = core::ptr::null_mut();
    v_res_2928_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2920_, v_msg_2921_, v_declHint_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
    lean_dec(v___y_2926_);
    lean_dec_ref(v___y_2925_);
    lean_dec(v___y_2924_);
    lean_dec_ref(v___y_2923_);
    lean_dec(v_ref_2920_);
    return v_res_2928_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    v___x_2930_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_2931_ = l_Lean_stringToMessageData(v___x_2930_);
    return v___x_2931_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    v___x_2933_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_2934_ = l_Lean_stringToMessageData(v___x_2933_);
    return v___x_2934_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg(
    mut v_ref_2935_: *mut LeanObject,
    mut v_constName_2936_: *mut LeanObject,
    mut v___y_2937_: *mut LeanObject,
    mut v___y_2938_: *mut LeanObject,
    mut v___y_2939_: *mut LeanObject,
    mut v___y_2940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: u8 = 0;
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    v___x_2942_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_2943_ = 0;
    lean_inc(v_constName_2936_);
    v___x_2944_ = l_Lean_MessageData_ofConstName(v_constName_2936_, v___x_2943_);
    v___x_2945_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2945_, 0, v___x_2942_);
    lean_ctor_set(v___x_2945_, 1, v___x_2944_);
    v___x_2946_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_2947_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2947_, 0, v___x_2945_);
    lean_ctor_set(v___x_2947_, 1, v___x_2946_);
    v___x_2948_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2935_, v___x_2947_, v_constName_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
    return v___x_2948_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_2949_: *mut LeanObject,
    mut v_constName_2950_: *mut LeanObject,
    mut v___y_2951_: *mut LeanObject,
    mut v___y_2952_: *mut LeanObject,
    mut v___y_2953_: *mut LeanObject,
    mut v___y_2954_: *mut LeanObject,
    mut v___y_2955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2956_: *mut LeanObject = core::ptr::null_mut();
    v_res_2956_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg(v_ref_2949_, v_constName_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
    lean_dec(v___y_2954_);
    lean_dec_ref(v___y_2953_);
    lean_dec(v___y_2952_);
    lean_dec_ref(v___y_2951_);
    lean_dec(v_ref_2949_);
    return v_res_2956_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg(
    mut v_constName_2957_: *mut LeanObject,
    mut v___y_2958_: *mut LeanObject,
    mut v___y_2959_: *mut LeanObject,
    mut v___y_2960_: *mut LeanObject,
    mut v___y_2961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    v_ref_2963_ = lean_ctor_get(v___y_2960_, 5);
    v___x_2964_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg(v_ref_2963_, v_constName_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
    return v___x_2964_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg___boxed(
    mut v_constName_2965_: *mut LeanObject,
    mut v___y_2966_: *mut LeanObject,
    mut v___y_2967_: *mut LeanObject,
    mut v___y_2968_: *mut LeanObject,
    mut v___y_2969_: *mut LeanObject,
    mut v___y_2970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2971_: *mut LeanObject = core::ptr::null_mut();
    v_res_2971_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg(v_constName_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
    lean_dec(v___y_2969_);
    lean_dec_ref(v___y_2968_);
    lean_dec(v___y_2967_);
    lean_dec_ref(v___y_2966_);
    return v_res_2971_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0(
    mut v_constName_2972_: *mut LeanObject,
    mut v___y_2973_: *mut LeanObject,
    mut v___y_2974_: *mut LeanObject,
    mut v___y_2975_: *mut LeanObject,
    mut v___y_2976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: u8 = 0;
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2986_: u8 = 0;
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2990_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2978_ = lean_st_ref_get(v___y_2976_);
                v_env_2979_ = lean_ctor_get(v___x_2978_, 0);
                lean_inc_ref(v_env_2979_);
                lean_dec(v___x_2978_);
                v___x_2980_ = 0;
                lean_inc(v_constName_2972_);
                v___x_2981_ =
                    l_Lean_Environment_find_x3f(v_env_2979_, v_constName_2972_, v___x_2980_);
                if lean_obj_tag(v___x_2981_) == 0 {
                    v___x_2982_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg(v_constName_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
                    return v___x_2982_;
                } else {
                    lean_dec(v_constName_2972_);
                    v_val_2983_ = lean_ctor_get(v___x_2981_, 0);
                    v_isSharedCheck_2990_ = (!lean_is_exclusive(v___x_2981_)) as u8;
                    if v_isSharedCheck_2990_ == 0 {
                        v___x_2985_ = v___x_2981_;
                        v_isShared_2986_ = v_isSharedCheck_2990_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2983_);
                        lean_dec(v___x_2981_);
                        v___x_2985_ = lean_box(0);
                        v_isShared_2986_ = v_isSharedCheck_2990_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2986_ == 0 {
                    lean_ctor_set_tag(v___x_2985_, 0);
                    v___x_2988_ = v___x_2985_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_val_2983_);
                    v___x_2988_ = v_reuseFailAlloc_2989_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2988_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0___boxed(
    mut v_constName_2991_: *mut LeanObject,
    mut v___y_2992_: *mut LeanObject,
    mut v___y_2993_: *mut LeanObject,
    mut v___y_2994_: *mut LeanObject,
    mut v___y_2995_: *mut LeanObject,
    mut v___y_2996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2997_: *mut LeanObject = core::ptr::null_mut();
    v_res_2997_ = l_Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0(
        v_constName_2991_,
        v___y_2992_,
        v___y_2993_,
        v___y_2994_,
        v___y_2995_,
    );
    lean_dec(v___y_2995_);
    lean_dec_ref(v___y_2994_);
    lean_dec(v___y_2993_);
    lean_dec_ref(v___y_2992_);
    return v_res_2997_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppSignature(
    mut v_c_3002_: *mut LeanObject,
    mut v_a_3003_: *mut LeanObject,
    mut v_a_3004_: *mut LeanObject,
    mut v_a_3005_: *mut LeanObject,
    mut v_a_3006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3012_: u8 = 0;
    let mut v_options_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: u8 = 0;
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3028_: u8 = 0;
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3033_: u8 = 0;
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3040_: u8 = 0;
    let mut v_a_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3044_: u8 = 0;
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3048_: u8 = 0;
    let mut v_isSharedCheck_3049_: u8 = 0;
    let mut v_a_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3053_: u8 = 0;
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3057_: u8 = 0;
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3070_: u8 = 0;
    let mut v_a_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3074_: u8 = 0;
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3078_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_c_3002_);
                v___x_3008_ = l_Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0(
                    v_c_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_,
                );
                if lean_obj_tag(v___x_3008_) == 0 {
                    v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
                    v_isSharedCheck_3070_ = (!lean_is_exclusive(v___x_3008_)) as u8;
                    if v_isSharedCheck_3070_ == 0 {
                        v___x_3011_ = v___x_3008_;
                        v_isShared_3012_ = v_isSharedCheck_3070_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3009_);
                        lean_dec(v___x_3008_);
                        v___x_3011_ = lean_box(0);
                        v_isShared_3012_ = v_isSharedCheck_3070_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_c_3002_);
                    v_a_3071_ = lean_ctor_get(v___x_3008_, 0);
                    v_isSharedCheck_3078_ = (!lean_is_exclusive(v___x_3008_)) as u8;
                    if v_isSharedCheck_3078_ == 0 {
                        v___x_3073_ = v___x_3008_;
                        v_isShared_3074_ = v_isSharedCheck_3078_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_3071_);
                        lean_dec(v___x_3008_);
                        v___x_3073_ = lean_box(0);
                        v_isShared_3074_ = v_isSharedCheck_3078_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v_options_3013_ = lean_ctor_get(v_a_3005_, 2);
                v___x_3014_ = l_Lean_ConstantInfo_levelParams(v_a_3009_);
                v___x_3015_ = lean_box(0);
                v___x_3016_ =
                    l_List_mapTR_loop___at___00Lean_PrettyPrinter_ppConstNameWithInfos_spec__0(
                        v___x_3014_,
                        v___x_3015_,
                    );
                v___x_3017_ = l_Lean_Expr_const___override(v_c_3002_, v___x_3016_);
                v___x_3018_ = l_Lean_pp_raw;
                v___x_3019_ = l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(v_options_3013_, v___x_3018_);
                if v___x_3019_ == 0 {
                    lean_del_object(v___x_3011_);
                    lean_dec(v_a_3009_);
                    v___x_3020_ = lean_box(1);
                    v___x_3021_ = l_Lean_PrettyPrinter_ppSignature___closed__0;
                    v___x_3022_ = l_Lean_PrettyPrinter_delabCore___redArg(
                        v___x_3017_,
                        v___x_3020_,
                        v___x_3021_,
                        v_a_3003_,
                        v_a_3004_,
                        v_a_3005_,
                        v_a_3006_,
                    );
                    if lean_obj_tag(v___x_3022_) == 0 {
                        v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
                        lean_inc(v_a_3023_);
                        lean_dec_ref_known(v___x_3022_, 1);
                        v_fst_3024_ = lean_ctor_get(v_a_3023_, 0);
                        v_snd_3025_ = lean_ctor_get(v_a_3023_, 1);
                        v_isSharedCheck_3049_ = (!lean_is_exclusive(v_a_3023_)) as u8;
                        if v_isSharedCheck_3049_ == 0 {
                            v___x_3027_ = v_a_3023_;
                            v_isShared_3028_ = v_isSharedCheck_3049_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_snd_3025_);
                            lean_inc(v_fst_3024_);
                            lean_dec(v_a_3023_);
                            v___x_3027_ = lean_box(0);
                            v_isShared_3028_ = v_isSharedCheck_3049_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_3050_ = lean_ctor_get(v___x_3022_, 0);
                        v_isSharedCheck_3057_ = (!lean_is_exclusive(v___x_3022_)) as u8;
                        if v_isSharedCheck_3057_ == 0 {
                            v___x_3052_ = v___x_3022_;
                            v_isShared_3053_ = v_isSharedCheck_3057_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_3050_);
                            lean_dec(v___x_3022_);
                            v___x_3052_ = lean_box(0);
                            v_isShared_3053_ = v_isSharedCheck_3057_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v___x_3058_ = lean_expr_dbg_to_string(v___x_3017_);
                    lean_dec_ref(v___x_3017_);
                    v___x_3059_ = l_Lean_PrettyPrinter_ppSignature___closed__1;
                    v___x_3060_ = lean_string_append(v___x_3058_, v___x_3059_);
                    v___x_3061_ = l_Lean_ConstantInfo_type(v_a_3009_);
                    lean_dec(v_a_3009_);
                    v___x_3062_ = lean_expr_dbg_to_string(v___x_3061_);
                    lean_dec_ref(v___x_3061_);
                    v___x_3063_ = lean_string_append(v___x_3060_, v___x_3062_);
                    lean_dec_ref(v___x_3062_);
                    v___x_3064_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_3064_, 0, v___x_3063_);
                    v___x_3065_ = lean_box(1);
                    v___x_3066_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3066_, 0, v___x_3064_);
                    lean_ctor_set(v___x_3066_, 1, v___x_3065_);
                    if v_isShared_3012_ == 0 {
                        lean_ctor_set(v___x_3011_, 0, v___x_3066_);
                        v___x_3068_ = v___x_3011_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3069_, 0, v___x_3066_);
                        v___x_3068_ = v_reuseFailAlloc_3069_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3029_ = l_Lean_PrettyPrinter_ppTerm(v_fst_3024_, v_a_3005_, v_a_3006_);
                if lean_obj_tag(v___x_3029_) == 0 {
                    v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
                    v_isSharedCheck_3040_ = (!lean_is_exclusive(v___x_3029_)) as u8;
                    if v_isSharedCheck_3040_ == 0 {
                        v___x_3032_ = v___x_3029_;
                        v_isShared_3033_ = v_isSharedCheck_3040_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3030_);
                        lean_dec(v___x_3029_);
                        v___x_3032_ = lean_box(0);
                        v_isShared_3033_ = v_isSharedCheck_3040_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3027_);
                    lean_dec(v_snd_3025_);
                    v_a_3041_ = lean_ctor_get(v___x_3029_, 0);
                    v_isSharedCheck_3048_ = (!lean_is_exclusive(v___x_3029_)) as u8;
                    if v_isSharedCheck_3048_ == 0 {
                        v___x_3043_ = v___x_3029_;
                        v_isShared_3044_ = v_isSharedCheck_3048_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3041_);
                        lean_dec(v___x_3029_);
                        v___x_3043_ = lean_box(0);
                        v_isShared_3044_ = v_isSharedCheck_3048_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3028_ == 0 {
                    lean_ctor_set(v___x_3027_, 0, v_a_3030_);
                    v___x_3035_ = v___x_3027_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3039_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_3030_);
                    lean_ctor_set(v_reuseFailAlloc_3039_, 1, v_snd_3025_);
                    v___x_3035_ = v_reuseFailAlloc_3039_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3033_ == 0 {
                    lean_ctor_set(v___x_3032_, 0, v___x_3035_);
                    v___x_3037_ = v___x_3032_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3035_);
                    v___x_3037_ = v_reuseFailAlloc_3038_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3037_;
            }
            6 => {
                if v_isShared_3044_ == 0 {
                    v___x_3046_ = v___x_3043_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3041_);
                    v___x_3046_ = v_reuseFailAlloc_3047_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3046_;
            }
            8 => {
                if v_isShared_3053_ == 0 {
                    v___x_3055_ = v___x_3052_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3050_);
                    v___x_3055_ = v_reuseFailAlloc_3056_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3055_;
            }
            10 => {
                return v___x_3068_;
            }
            11 => {
                if v_isShared_3074_ == 0 {
                    v___x_3076_ = v___x_3073_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
                    v___x_3076_ = v_reuseFailAlloc_3077_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3076_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PrettyPrinter_ppSignature___boxed(
    mut v_c_3079_: *mut LeanObject,
    mut v_a_3080_: *mut LeanObject,
    mut v_a_3081_: *mut LeanObject,
    mut v_a_3082_: *mut LeanObject,
    mut v_a_3083_: *mut LeanObject,
    mut v_a_3084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3085_: *mut LeanObject = core::ptr::null_mut();
    v_res_3085_ =
        l_Lean_PrettyPrinter_ppSignature(v_c_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_);
    lean_dec(v_a_3083_);
    lean_dec_ref(v_a_3082_);
    lean_dec(v_a_3081_);
    lean_dec_ref(v_a_3080_);
    return v_res_3085_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0(
    mut v_00_u03b1_3086_: *mut LeanObject,
    mut v_constName_3087_: *mut LeanObject,
    mut v___y_3088_: *mut LeanObject,
    mut v___y_3089_: *mut LeanObject,
    mut v___y_3090_: *mut LeanObject,
    mut v___y_3091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    v___x_3093_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg(v_constName_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
    return v___x_3093_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___boxed(
    mut v_00_u03b1_3094_: *mut LeanObject,
    mut v_constName_3095_: *mut LeanObject,
    mut v___y_3096_: *mut LeanObject,
    mut v___y_3097_: *mut LeanObject,
    mut v___y_3098_: *mut LeanObject,
    mut v___y_3099_: *mut LeanObject,
    mut v___y_3100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3101_: *mut LeanObject = core::ptr::null_mut();
    v_res_3101_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0(v_00_u03b1_3094_, v_constName_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_);
    lean_dec(v___y_3099_);
    lean_dec_ref(v___y_3098_);
    lean_dec(v___y_3097_);
    lean_dec_ref(v___y_3096_);
    return v_res_3101_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1(
    mut v_00_u03b1_3102_: *mut LeanObject,
    mut v_ref_3103_: *mut LeanObject,
    mut v_constName_3104_: *mut LeanObject,
    mut v___y_3105_: *mut LeanObject,
    mut v___y_3106_: *mut LeanObject,
    mut v___y_3107_: *mut LeanObject,
    mut v___y_3108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    v___x_3110_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg(v_ref_3103_, v_constName_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
    return v___x_3110_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_3111_: *mut LeanObject,
    mut v_ref_3112_: *mut LeanObject,
    mut v_constName_3113_: *mut LeanObject,
    mut v___y_3114_: *mut LeanObject,
    mut v___y_3115_: *mut LeanObject,
    mut v___y_3116_: *mut LeanObject,
    mut v___y_3117_: *mut LeanObject,
    mut v___y_3118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3119_: *mut LeanObject = core::ptr::null_mut();
    v_res_3119_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1(v_00_u03b1_3111_, v_ref_3112_, v_constName_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
    lean_dec(v___y_3117_);
    lean_dec_ref(v___y_3116_);
    lean_dec(v___y_3115_);
    lean_dec_ref(v___y_3114_);
    lean_dec(v_ref_3112_);
    return v_res_3119_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_3120_: *mut LeanObject,
    mut v_ref_3121_: *mut LeanObject,
    mut v_msg_3122_: *mut LeanObject,
    mut v_declHint_3123_: *mut LeanObject,
    mut v___y_3124_: *mut LeanObject,
    mut v___y_3125_: *mut LeanObject,
    mut v___y_3126_: *mut LeanObject,
    mut v___y_3127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    v___x_3129_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3121_, v_msg_3122_, v_declHint_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
    return v___x_3129_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_3130_: *mut LeanObject,
    mut v_ref_3131_: *mut LeanObject,
    mut v_msg_3132_: *mut LeanObject,
    mut v_declHint_3133_: *mut LeanObject,
    mut v___y_3134_: *mut LeanObject,
    mut v___y_3135_: *mut LeanObject,
    mut v___y_3136_: *mut LeanObject,
    mut v___y_3137_: *mut LeanObject,
    mut v___y_3138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3139_: *mut LeanObject = core::ptr::null_mut();
    v_res_3139_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3130_, v_ref_3131_, v_msg_3132_, v_declHint_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
    lean_dec(v___y_3137_);
    lean_dec_ref(v___y_3136_);
    lean_dec(v___y_3135_);
    lean_dec_ref(v___y_3134_);
    lean_dec(v_ref_3131_);
    return v_res_3139_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_3140_: *mut LeanObject,
    mut v_declHint_3141_: *mut LeanObject,
    mut v___y_3142_: *mut LeanObject,
    mut v___y_3143_: *mut LeanObject,
    mut v___y_3144_: *mut LeanObject,
    mut v___y_3145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    v___x_3147_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_3140_, v_declHint_3141_, v___y_3145_);
    return v___x_3147_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msg_3148_: *mut LeanObject,
    mut v_declHint_3149_: *mut LeanObject,
    mut v___y_3150_: *mut LeanObject,
    mut v___y_3151_: *mut LeanObject,
    mut v___y_3152_: *mut LeanObject,
    mut v___y_3153_: *mut LeanObject,
    mut v___y_3154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3155_: *mut LeanObject = core::ptr::null_mut();
    v_res_3155_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_3148_, v_declHint_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
    lean_dec(v___y_3153_);
    lean_dec_ref(v___y_3152_);
    lean_dec(v___y_3151_);
    lean_dec_ref(v___y_3150_);
    return v_res_3155_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b1_3156_: *mut LeanObject,
    mut v_ref_3157_: *mut LeanObject,
    mut v_msg_3158_: *mut LeanObject,
    mut v___y_3159_: *mut LeanObject,
    mut v___y_3160_: *mut LeanObject,
    mut v___y_3161_: *mut LeanObject,
    mut v___y_3162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    v___x_3164_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3157_, v_msg_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
    return v___x_3164_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_3165_: *mut LeanObject,
    mut v_ref_3166_: *mut LeanObject,
    mut v_msg_3167_: *mut LeanObject,
    mut v___y_3168_: *mut LeanObject,
    mut v___y_3169_: *mut LeanObject,
    mut v___y_3170_: *mut LeanObject,
    mut v___y_3171_: *mut LeanObject,
    mut v___y_3172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3173_: *mut LeanObject = core::ptr::null_mut();
    v_res_3173_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_3165_, v_ref_3166_, v_msg_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
    lean_dec(v___y_3171_);
    lean_dec_ref(v___y_3170_);
    lean_dec(v___y_3169_);
    lean_dec_ref(v___y_3168_);
    lean_dec(v_ref_3166_);
    return v_res_3173_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b1_3174_: *mut LeanObject,
    mut v_msg_3175_: *mut LeanObject,
    mut v___y_3176_: *mut LeanObject,
    mut v___y_3177_: *mut LeanObject,
    mut v___y_3178_: *mut LeanObject,
    mut v___y_3179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    v___x_3181_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
    return v___x_3181_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b1_3182_: *mut LeanObject,
    mut v_msg_3183_: *mut LeanObject,
    mut v___y_3184_: *mut LeanObject,
    mut v___y_3185_: *mut LeanObject,
    mut v___y_3186_: *mut LeanObject,
    mut v___y_3187_: *mut LeanObject,
    mut v___y_3188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3189_: *mut LeanObject = core::ptr::null_mut();
    v_res_3189_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_3182_, v_msg_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
    lean_dec(v___y_3187_);
    lean_dec_ref(v___y_3186_);
    lean_dec(v___y_3185_);
    lean_dec_ref(v___y_3184_);
    return v_res_3189_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(
    mut v_x_3190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3197_: u8 = 0;
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3202_: u8 = 0;
    let mut v_a_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3207_: u8 = 0;
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3212_: u8 = 0;
    let mut v_a_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3216_: u8 = 0;
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3221_: u8 = 0;
    let mut v_a_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3226_: u8 = 0;
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3232_: u8 = 0;
    let mut v_a_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3237_: u8 = 0;
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3242_: u8 = 0;
    let mut v_data_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3248_: u8 = 0;
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3250_: usize = 0;
    let mut v___x_3251_: usize = 0;
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3256_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_3190_) {
                3 => {
                    v_a_3191_ = lean_ctor_get(v_x_3190_, 1);
                    lean_inc_ref(v_a_3191_);
                    lean_dec_ref_known(v_x_3190_, 2);
                    v_x_3190_ = v_a_3191_;
                    state = 0;
                    continue;
                }
                4 => {
                    v_a_3193_ = lean_ctor_get(v_x_3190_, 0);
                    v_a_3194_ = lean_ctor_get(v_x_3190_, 1);
                    v_isSharedCheck_3202_ = (!lean_is_exclusive(v_x_3190_)) as u8;
                    if v_isSharedCheck_3202_ == 0 {
                        v___x_3196_ = v_x_3190_;
                        v_isShared_3197_ = v_isSharedCheck_3202_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3194_);
                        lean_inc(v_a_3193_);
                        lean_dec(v_x_3190_);
                        v___x_3196_ = lean_box(0);
                        v_isShared_3197_ = v_isSharedCheck_3202_;
                        state = 1;
                        continue;
                    }
                }
                5 => {
                    v_a_3203_ = lean_ctor_get(v_x_3190_, 0);
                    v_a_3204_ = lean_ctor_get(v_x_3190_, 1);
                    v_isSharedCheck_3212_ = (!lean_is_exclusive(v_x_3190_)) as u8;
                    if v_isSharedCheck_3212_ == 0 {
                        v___x_3206_ = v_x_3190_;
                        v_isShared_3207_ = v_isSharedCheck_3212_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3204_);
                        lean_inc(v_a_3203_);
                        lean_dec(v_x_3190_);
                        v___x_3206_ = lean_box(0);
                        v_isShared_3207_ = v_isSharedCheck_3212_;
                        state = 3;
                        continue;
                    }
                }
                6 => {
                    v_a_3213_ = lean_ctor_get(v_x_3190_, 0);
                    v_isSharedCheck_3221_ = (!lean_is_exclusive(v_x_3190_)) as u8;
                    if v_isSharedCheck_3221_ == 0 {
                        v___x_3215_ = v_x_3190_;
                        v_isShared_3216_ = v_isSharedCheck_3221_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3213_);
                        lean_dec(v_x_3190_);
                        v___x_3215_ = lean_box(0);
                        v_isShared_3216_ = v_isSharedCheck_3221_;
                        state = 5;
                        continue;
                    }
                }
                7 => {
                    v_a_3222_ = lean_ctor_get(v_x_3190_, 0);
                    v_a_3223_ = lean_ctor_get(v_x_3190_, 1);
                    v_isSharedCheck_3232_ = (!lean_is_exclusive(v_x_3190_)) as u8;
                    if v_isSharedCheck_3232_ == 0 {
                        v___x_3225_ = v_x_3190_;
                        v_isShared_3226_ = v_isSharedCheck_3232_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3223_);
                        lean_inc(v_a_3222_);
                        lean_dec(v_x_3190_);
                        v___x_3225_ = lean_box(0);
                        v_isShared_3226_ = v_isSharedCheck_3232_;
                        state = 7;
                        continue;
                    }
                }
                8 => {
                    v_a_3233_ = lean_ctor_get(v_x_3190_, 0);
                    v_a_3234_ = lean_ctor_get(v_x_3190_, 1);
                    v_isSharedCheck_3242_ = (!lean_is_exclusive(v_x_3190_)) as u8;
                    if v_isSharedCheck_3242_ == 0 {
                        v___x_3236_ = v_x_3190_;
                        v_isShared_3237_ = v_isSharedCheck_3242_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_3234_);
                        lean_inc(v_a_3233_);
                        lean_dec(v_x_3190_);
                        v___x_3236_ = lean_box(0);
                        v_isShared_3237_ = v_isSharedCheck_3242_;
                        state = 9;
                        continue;
                    }
                }
                9 => {
                    v_data_3243_ = lean_ctor_get(v_x_3190_, 0);
                    v_msg_3244_ = lean_ctor_get(v_x_3190_, 1);
                    v_children_3245_ = lean_ctor_get(v_x_3190_, 2);
                    v_isSharedCheck_3256_ = (!lean_is_exclusive(v_x_3190_)) as u8;
                    if v_isSharedCheck_3256_ == 0 {
                        v___x_3247_ = v_x_3190_;
                        v_isShared_3248_ = v_isSharedCheck_3256_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_children_3245_);
                        lean_inc(v_msg_3244_);
                        lean_inc(v_data_3243_);
                        lean_dec(v_x_3190_);
                        v___x_3247_ = lean_box(0);
                        v_isShared_3248_ = v_isSharedCheck_3256_;
                        state = 11;
                        continue;
                    }
                }
                _ => {
                    return v_x_3190_;
                }
            },
            1 => {
                v___x_3198_ =
                    l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_a_3194_);
                if v_isShared_3197_ == 0 {
                    lean_ctor_set(v___x_3196_, 1, v___x_3198_);
                    v___x_3200_ = v___x_3196_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3201_ = lean_alloc_ctor(4, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3193_);
                    lean_ctor_set(v_reuseFailAlloc_3201_, 1, v___x_3198_);
                    v___x_3200_ = v_reuseFailAlloc_3201_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3200_;
            }
            3 => {
                v___x_3208_ =
                    l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_a_3204_);
                if v_isShared_3207_ == 0 {
                    lean_ctor_set(v___x_3206_, 1, v___x_3208_);
                    v___x_3210_ = v___x_3206_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3211_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3203_);
                    lean_ctor_set(v_reuseFailAlloc_3211_, 1, v___x_3208_);
                    v___x_3210_ = v_reuseFailAlloc_3211_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3210_;
            }
            5 => {
                v___x_3217_ =
                    l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_a_3213_);
                if v_isShared_3216_ == 0 {
                    lean_ctor_set(v___x_3215_, 0, v___x_3217_);
                    v___x_3219_ = v___x_3215_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3220_ = lean_alloc_ctor(6, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3217_);
                    v___x_3219_ = v_reuseFailAlloc_3220_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3219_;
            }
            7 => {
                v___x_3227_ =
                    l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_a_3222_);
                v___x_3228_ =
                    l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_a_3223_);
                if v_isShared_3226_ == 0 {
                    lean_ctor_set(v___x_3225_, 1, v___x_3228_);
                    lean_ctor_set(v___x_3225_, 0, v___x_3227_);
                    v___x_3230_ = v___x_3225_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3231_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___x_3227_);
                    lean_ctor_set(v_reuseFailAlloc_3231_, 1, v___x_3228_);
                    v___x_3230_ = v_reuseFailAlloc_3231_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3230_;
            }
            9 => {
                v___x_3238_ =
                    l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_a_3234_);
                if v_isShared_3237_ == 0 {
                    lean_ctor_set(v___x_3236_, 1, v___x_3238_);
                    v___x_3240_ = v___x_3236_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3241_ = lean_alloc_ctor(8, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3233_);
                    lean_ctor_set(v_reuseFailAlloc_3241_, 1, v___x_3238_);
                    v___x_3240_ = v_reuseFailAlloc_3241_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3240_;
            }
            11 => {
                v___x_3249_ =
                    l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_msg_3244_);
                v_sz_3250_ = lean_array_size(v_children_3245_);
                v___x_3251_ = 0usize;
                v___x_3252_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0(v_sz_3250_, v___x_3251_, v_children_3245_);
                if v_isShared_3248_ == 0 {
                    lean_ctor_set(v___x_3247_, 2, v___x_3252_);
                    lean_ctor_set(v___x_3247_, 1, v___x_3249_);
                    v___x_3254_ = v___x_3247_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3255_ = lean_alloc_ctor(9, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_data_3243_);
                    lean_ctor_set(v_reuseFailAlloc_3255_, 1, v___x_3249_);
                    lean_ctor_set(v_reuseFailAlloc_3255_, 2, v___x_3252_);
                    v___x_3254_ = v_reuseFailAlloc_3255_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3254_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0(
    mut v_sz_3257_: usize,
    mut v_i_3258_: usize,
    mut v_bs_3259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3260_: u8 = 0;
    let mut v_v_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: usize = 0;
    let mut v___x_3266_: usize = 0;
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3260_ = lean_usize_dec_lt(v_i_3258_, v_sz_3257_);
                if v___x_3260_ == 0 {
                    return v_bs_3259_;
                } else {
                    v_v_3261_ = lean_array_uget(v_bs_3259_, v_i_3258_);
                    v___x_3262_ = lean_unsigned_to_nat(0);
                    v_bs_x27_3263_ = lean_array_uset(v_bs_3259_, v_i_3258_, v___x_3262_);
                    v___x_3264_ =
                        l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_v_3261_);
                    v___x_3265_ = 1usize;
                    v___x_3266_ = lean_usize_add(v_i_3258_, v___x_3265_);
                    v___x_3267_ = lean_array_uset(v_bs_x27_3263_, v_i_3258_, v___x_3264_);
                    v_i_3258_ = v___x_3266_;
                    v_bs_3259_ = v___x_3267_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0___boxed(
    mut v_sz_3269_: *mut LeanObject,
    mut v_i_3270_: *mut LeanObject,
    mut v_bs_3271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3272_: usize = 0;
    let mut v_i_boxed_3273_: usize = 0;
    let mut v_res_3274_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3272_ = lean_unbox_usize(v_sz_3269_);
    lean_dec(v_sz_3269_);
    v_i_boxed_3273_ = lean_unbox_usize(v_i_3270_);
    lean_dec(v_i_3270_);
    v_res_3274_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0(v_sz_boxed_3272_, v_i_boxed_3273_, v_bs_3271_);
    return v_res_3274_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg___lam__0(
    mut v_throw_3275_: *mut LeanObject,
    mut v_x_3276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3281_: u8 = 0;
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3287_: u8 = 0;
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3276_) == 0 {
                    v_ref_3277_ = lean_ctor_get(v_x_3276_, 0);
                    v_msg_3278_ = lean_ctor_get(v_x_3276_, 1);
                    v_isSharedCheck_3287_ = (!lean_is_exclusive(v_x_3276_)) as u8;
                    if v_isSharedCheck_3287_ == 0 {
                        v___x_3280_ = v_x_3276_;
                        v_isShared_3281_ = v_isSharedCheck_3287_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_msg_3278_);
                        lean_inc(v_ref_3277_);
                        lean_dec(v_x_3276_);
                        v___x_3280_ = lean_box(0);
                        v_isShared_3281_ = v_isSharedCheck_3287_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3288_ = lean_apply_2(v_throw_3275_, lean_box(0), v_x_3276_);
                    return v___x_3288_;
                }
            }
            1 => {
                v___x_3282_ =
                    l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_msg_3278_);
                if v_isShared_3281_ == 0 {
                    lean_ctor_set(v___x_3280_, 1, v___x_3282_);
                    v___x_3284_ = v___x_3280_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_ref_3277_);
                    lean_ctor_set(v_reuseFailAlloc_3286_, 1, v___x_3282_);
                    v___x_3284_ = v_reuseFailAlloc_3286_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3285_ = lean_apply_2(v_throw_3275_, lean_box(0), v___x_3284_);
                return v___x_3285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg(
    mut v_inst_3289_: *mut LeanObject,
    mut v_x_3290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_throw_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    v_throw_3291_ = lean_ctor_get(v_inst_3289_, 0);
    lean_inc(v_throw_3291_);
    v_tryCatch_3292_ = lean_ctor_get(v_inst_3289_, 1);
    lean_inc(v_tryCatch_3292_);
    lean_dec_ref(v_inst_3289_);
    v___f_3293_ = lean_alloc_closure(
        l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3293_, 0, v_throw_3291_);
    v___x_3294_ = lean_apply_3(v_tryCatch_3292_, lean_box(0), v_x_3290_, v___f_3293_);
    return v___x_3294_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext(
    mut v_00_u03b1_3295_: *mut LeanObject,
    mut v_m_3296_: *mut LeanObject,
    mut v_inst_3297_: *mut LeanObject,
    mut v_x_3298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    v___x_3299_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg(
        v_inst_3297_,
        v_x_3298_,
    );
    return v___x_3299_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___redArg(
    mut v_x_3300_: *mut LeanObject,
    mut v___y_3301_: *mut LeanObject,
    mut v___y_3302_: *mut LeanObject,
    mut v___y_3303_: *mut LeanObject,
    mut v___y_3304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3309_: u8 = 0;
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3312_: u8 = 0;
    let mut v_ref_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3317_: u8 = 0;
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3325_: u8 = 0;
    let mut v_isSharedCheck_3326_: u8 = 0;
    let mut v_unused_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: u8 = 0;
    let mut v___x_3329_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_3304_);
                lean_inc_ref(v___y_3303_);
                lean_inc(v___y_3302_);
                lean_inc_ref(v___y_3301_);
                v___x_3306_ = lean_apply_5(
                    v_x_3300_,
                    v___y_3301_,
                    v___y_3302_,
                    v___y_3303_,
                    v___y_3304_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_3306_) == 0 {
                    return v___x_3306_;
                } else {
                    v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
                    lean_inc(v_a_3307_);
                    v___x_3328_ = l_Lean_Exception_isInterrupt(v_a_3307_);
                    if v___x_3328_ == 0 {
                        lean_inc(v_a_3307_);
                        v___x_3329_ = l_Lean_Exception_isRuntime(v_a_3307_);
                        v___y_3309_ = v___x_3329_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3309_ = v___x_3328_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_3309_ == 0 {
                    if lean_obj_tag(v_a_3307_) == 0 {
                        v_isSharedCheck_3326_ = (!lean_is_exclusive(v___x_3306_)) as u8;
                        if v_isSharedCheck_3326_ == 0 {
                            v_unused_3327_ = lean_ctor_get(v___x_3306_, 0);
                            lean_dec(v_unused_3327_);
                            v___x_3311_ = v___x_3306_;
                            v_isShared_3312_ = v_isSharedCheck_3326_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_3306_);
                            v___x_3311_ = lean_box(0);
                            v_isShared_3312_ = v_isSharedCheck_3326_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3307_);
                        return v___x_3306_;
                    }
                } else {
                    lean_dec(v_a_3307_);
                    return v___x_3306_;
                }
            }
            2 => {
                v_ref_3313_ = lean_ctor_get(v_a_3307_, 0);
                v_msg_3314_ = lean_ctor_get(v_a_3307_, 1);
                v_isSharedCheck_3325_ = (!lean_is_exclusive(v_a_3307_)) as u8;
                if v_isSharedCheck_3325_ == 0 {
                    v___x_3316_ = v_a_3307_;
                    v_isShared_3317_ = v_isSharedCheck_3325_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_msg_3314_);
                    lean_inc(v_ref_3313_);
                    lean_dec(v_a_3307_);
                    v___x_3316_ = lean_box(0);
                    v_isShared_3317_ = v_isSharedCheck_3325_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3318_ =
                    l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_msg_3314_);
                if v_isShared_3317_ == 0 {
                    lean_ctor_set(v___x_3316_, 1, v___x_3318_);
                    v___x_3320_ = v___x_3316_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_ref_3313_);
                    lean_ctor_set(v_reuseFailAlloc_3324_, 1, v___x_3318_);
                    v___x_3320_ = v_reuseFailAlloc_3324_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3312_ == 0 {
                    lean_ctor_set(v___x_3311_, 0, v___x_3320_);
                    v___x_3322_ = v___x_3311_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3323_, 0, v___x_3320_);
                    v___x_3322_ = v_reuseFailAlloc_3323_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3322_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_x_3330_: *mut LeanObject,
    mut v___y_3331_: *mut LeanObject,
    mut v___y_3332_: *mut LeanObject,
    mut v___y_3333_: *mut LeanObject,
    mut v___y_3334_: *mut LeanObject,
    mut v___y_3335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3336_: *mut LeanObject = core::ptr::null_mut();
    v_res_3336_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___redArg(v_x_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
    lean_dec(v___y_3334_);
    lean_dec_ref(v___y_3333_);
    lean_dec(v___y_3332_);
    lean_dec_ref(v___y_3331_);
    return v_res_3336_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_3337_: *mut LeanObject,
    mut v_x_3338_: *mut LeanObject,
    mut v___y_3339_: *mut LeanObject,
    mut v___y_3340_: *mut LeanObject,
    mut v___y_3341_: *mut LeanObject,
    mut v___y_3342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    v___x_3344_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___redArg(v_x_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
    return v___x_3344_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_3345_: *mut LeanObject,
    mut v_x_3346_: *mut LeanObject,
    mut v___y_3347_: *mut LeanObject,
    mut v___y_3348_: *mut LeanObject,
    mut v___y_3349_: *mut LeanObject,
    mut v___y_3350_: *mut LeanObject,
    mut v___y_3351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3352_: *mut LeanObject = core::ptr::null_mut();
    v_res_3352_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0(v_00_u03b1_3345_, v_x_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
    lean_dec(v___y_3350_);
    lean_dec_ref(v___y_3349_);
    lean_dec(v___y_3348_);
    lean_dec_ref(v___y_3347_);
    return v_res_3352_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___redArg(
    mut v_x_3353_: *mut LeanObject,
    mut v___y_3354_: *mut LeanObject,
    mut v___y_3355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3360_: u8 = 0;
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3363_: u8 = 0;
    let mut v_ref_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3368_: u8 = 0;
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3376_: u8 = 0;
    let mut v_isSharedCheck_3377_: u8 = 0;
    let mut v_unused_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: u8 = 0;
    let mut v___x_3380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_3355_);
                lean_inc_ref(v___y_3354_);
                v___x_3357_ = lean_apply_3(v_x_3353_, v___y_3354_, v___y_3355_, lean_box(0));
                if lean_obj_tag(v___x_3357_) == 0 {
                    return v___x_3357_;
                } else {
                    v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
                    lean_inc(v_a_3358_);
                    v___x_3379_ = l_Lean_Exception_isInterrupt(v_a_3358_);
                    if v___x_3379_ == 0 {
                        lean_inc(v_a_3358_);
                        v___x_3380_ = l_Lean_Exception_isRuntime(v_a_3358_);
                        v___y_3360_ = v___x_3380_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3360_ = v___x_3379_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_3360_ == 0 {
                    if lean_obj_tag(v_a_3358_) == 0 {
                        v_isSharedCheck_3377_ = (!lean_is_exclusive(v___x_3357_)) as u8;
                        if v_isSharedCheck_3377_ == 0 {
                            v_unused_3378_ = lean_ctor_get(v___x_3357_, 0);
                            lean_dec(v_unused_3378_);
                            v___x_3362_ = v___x_3357_;
                            v_isShared_3363_ = v_isSharedCheck_3377_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_3357_);
                            v___x_3362_ = lean_box(0);
                            v_isShared_3363_ = v_isSharedCheck_3377_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3358_);
                        return v___x_3357_;
                    }
                } else {
                    lean_dec(v_a_3358_);
                    return v___x_3357_;
                }
            }
            2 => {
                v_ref_3364_ = lean_ctor_get(v_a_3358_, 0);
                v_msg_3365_ = lean_ctor_get(v_a_3358_, 1);
                v_isSharedCheck_3376_ = (!lean_is_exclusive(v_a_3358_)) as u8;
                if v_isSharedCheck_3376_ == 0 {
                    v___x_3367_ = v_a_3358_;
                    v_isShared_3368_ = v_isSharedCheck_3376_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_msg_3365_);
                    lean_inc(v_ref_3364_);
                    lean_dec(v_a_3358_);
                    v___x_3367_ = lean_box(0);
                    v_isShared_3368_ = v_isSharedCheck_3376_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3369_ =
                    l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_msg_3365_);
                if v_isShared_3368_ == 0 {
                    lean_ctor_set(v___x_3367_, 1, v___x_3369_);
                    v___x_3371_ = v___x_3367_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3375_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_ref_3364_);
                    lean_ctor_set(v_reuseFailAlloc_3375_, 1, v___x_3369_);
                    v___x_3371_ = v_reuseFailAlloc_3375_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3363_ == 0 {
                    lean_ctor_set(v___x_3362_, 0, v___x_3371_);
                    v___x_3373_ = v___x_3362_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3371_);
                    v___x_3373_ = v_reuseFailAlloc_3374_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3373_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_x_3381_: *mut LeanObject,
    mut v___y_3382_: *mut LeanObject,
    mut v___y_3383_: *mut LeanObject,
    mut v___y_3384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3385_: *mut LeanObject = core::ptr::null_mut();
    v_res_3385_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___redArg(v_x_3381_, v___y_3382_, v___y_3383_);
    lean_dec(v___y_3383_);
    lean_dec_ref(v___y_3382_);
    return v_res_3385_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1(
    mut v_00_u03b1_3386_: *mut LeanObject,
    mut v_x_3387_: *mut LeanObject,
    mut v___y_3388_: *mut LeanObject,
    mut v___y_3389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    v___x_3391_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___redArg(v_x_3387_, v___y_3388_, v___y_3389_);
    return v___x_3391_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___boxed(
    mut v_00_u03b1_3392_: *mut LeanObject,
    mut v_x_3393_: *mut LeanObject,
    mut v___y_3394_: *mut LeanObject,
    mut v___y_3395_: *mut LeanObject,
    mut v___y_3396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3397_: *mut LeanObject = core::ptr::null_mut();
    v_res_3397_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1(v_00_u03b1_3392_, v_x_3393_, v___y_3394_, v___y_3395_);
    lean_dec(v___y_3395_);
    lean_dec_ref(v___y_3394_);
    return v_res_3397_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(
    mut v_ctx_3399_: *mut LeanObject,
    mut v_e_3400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    v___x_3402_ = lean_box(1);
    v___x_3403_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0___closed__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_;
    v___x_3404_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_ppExprWithInfos___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_3404_, 0, v_e_3400_);
    lean_closure_set(v___x_3404_, 1, v___x_3402_);
    lean_closure_set(v___x_3404_, 2, v___x_3403_);
    v___x_3405_ = lean_alloc_closure(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___boxed as *mut core::ffi::c_void, 7, 2);
    lean_closure_set(v___x_3405_, 0, lean_box(0));
    lean_closure_set(v___x_3405_, 1, v___x_3404_);
    v___x_3406_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_3399_, v___x_3405_);
    return v___x_3406_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(
    mut v_ctx_3407_: *mut LeanObject,
    mut v_e_3408_: *mut LeanObject,
    mut v___y_3409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3410_: *mut LeanObject = core::ptr::null_mut();
    v_res_3410_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(v_ctx_3407_, v_e_3408_);
    lean_dec_ref(v_ctx_3407_);
    return v_res_3410_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(
    mut v_ctx_3411_: *mut LeanObject,
    mut v_n_3412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    v___x_3414_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_ppConstNameWithInfos___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_3414_, 0, v_n_3412_);
    v___x_3415_ = lean_alloc_closure(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___boxed as *mut core::ffi::c_void, 7, 2);
    lean_closure_set(v___x_3415_, 0, lean_box(0));
    lean_closure_set(v___x_3415_, 1, v___x_3414_);
    v___x_3416_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_3411_, v___x_3415_);
    return v___x_3416_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(
    mut v_ctx_3417_: *mut LeanObject,
    mut v_n_3418_: *mut LeanObject,
    mut v___y_3419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3420_: *mut LeanObject = core::ptr::null_mut();
    v_res_3420_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(v_ctx_3417_, v_n_3418_);
    lean_dec_ref(v_ctx_3417_);
    return v_res_3420_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(
    mut v_ctx_3421_: *mut LeanObject,
    mut v_l_3422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    v___x_3424_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_ppLevel___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_3424_, 0, v_l_3422_);
    v___x_3425_ = lean_alloc_closure(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___boxed as *mut core::ffi::c_void, 7, 2);
    lean_closure_set(v___x_3425_, 0, lean_box(0));
    lean_closure_set(v___x_3425_, 1, v___x_3424_);
    v___x_3426_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_3421_, v___x_3425_);
    return v___x_3426_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(
    mut v_ctx_3427_: *mut LeanObject,
    mut v_l_3428_: *mut LeanObject,
    mut v___y_3429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3430_: *mut LeanObject = core::ptr::null_mut();
    v_res_3430_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(v_ctx_3427_, v_l_3428_);
    lean_dec_ref(v_ctx_3427_);
    return v_res_3430_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(
    mut v_ctx_3431_: *mut LeanObject,
    mut v_mvarId_3432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    v___x_3434_ = lean_alloc_closure(l_Lean_Meta_ppGoal___boxed as *mut core::ffi::c_void, 6, 1);
    lean_closure_set(v___x_3434_, 0, v_mvarId_3432_);
    v___x_3435_ = lean_alloc_closure(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___boxed as *mut core::ffi::c_void, 7, 2);
    lean_closure_set(v___x_3435_, 0, lean_box(0));
    lean_closure_set(v___x_3435_, 1, v___x_3434_);
    v___x_3436_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_3431_, v___x_3435_);
    return v___x_3436_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(
    mut v_ctx_3437_: *mut LeanObject,
    mut v_mvarId_3438_: *mut LeanObject,
    mut v___y_3439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3440_: *mut LeanObject = core::ptr::null_mut();
    v_res_3440_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(v_ctx_3437_, v_mvarId_3438_);
    lean_dec_ref(v_ctx_3437_);
    return v_res_3440_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(
    mut v_ctx_3441_: *mut LeanObject,
    mut v_stx_3442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    v___x_3444_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_ppTerm___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___x_3444_, 0, v_stx_3442_);
    v___x_3445_ = lean_alloc_closure(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___boxed as *mut core::ffi::c_void, 5, 2);
    lean_closure_set(v___x_3445_, 0, lean_box(0));
    lean_closure_set(v___x_3445_, 1, v___x_3444_);
    v___x_3446_ = l_Lean_PPContext_runCoreM___redArg(v_ctx_3441_, v___x_3445_);
    return v___x_3446_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(
    mut v_ctx_3447_: *mut LeanObject,
    mut v_stx_3448_: *mut LeanObject,
    mut v___y_3449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3450_: *mut LeanObject = core::ptr::null_mut();
    v_res_3450_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(v_ctx_3447_, v_stx_3448_);
    lean_dec_ref(v_ctx_3447_);
    return v_res_3450_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    v___x_3463_ = l_Lean_ppFnsRef;
    v___x_3464_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_;
    v___x_3465_ = lean_st_ref_set(v___x_3463_, v___x_3464_);
    v___x_3466_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3466_, 0, v___x_3465_);
    return v___x_3466_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(
    mut v_a_3467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3468_: *mut LeanObject = core::ptr::null_mut();
    v_res_3468_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_();
    return v_res_3468_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: u8 = 0;
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    v___x_3519_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_;
    v___x_3520_ = 0;
    v___x_3521_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__19_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_;
    v___x_3522_ = l_Lean_registerTraceClass(v___x_3519_, v___x_3520_, v___x_3521_);
    return v___x_3522_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2____boxed(
    mut v_a_3523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3524_: *mut LeanObject = core::ptr::null_mut();
    v_res_3524_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_();
    return v_res_3524_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__2() -> *mut LeanObject {
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    v___x_3528_ = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
    v___x_3529_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_3530_ = l_Lean_PrettyPrinter_registerParserCompilers___closed__1;
    v___x_3531_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3531_, 0, v___x_3530_);
    lean_ctor_set(v___x_3531_, 1, v___x_3529_);
    lean_ctor_set(v___x_3531_, 2, v___x_3528_);
    return v___x_3531_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__5() -> *mut LeanObject {
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    v___x_3535_ = l_Lean_PrettyPrinter_combinatorFormatterAttribute;
    v___x_3536_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3537_ = l_Lean_PrettyPrinter_registerParserCompilers___closed__4;
    v___x_3538_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3538_, 0, v___x_3537_);
    lean_ctor_set(v___x_3538_, 1, v___x_3536_);
    lean_ctor_set(v___x_3538_, 2, v___x_3535_);
    return v___x_3538_;
}
pub unsafe fn l_Lean_PrettyPrinter_registerParserCompilers() -> *mut LeanObject {
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    v___x_3540_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_registerParserCompilers___closed__2),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_registerParserCompilers___closed__2_once),
        _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__2,
    );
    v___x_3541_ = l_Lean_ParserCompiler_registerParserCompiler___redArg(v___x_3540_);
    if lean_obj_tag(v___x_3541_) == 0 {
        let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_3541_, 1);
        v___x_3542_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_registerParserCompilers___closed__5),
            core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_registerParserCompilers___closed__5_once),
            _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__5,
        );
        v___x_3543_ = l_Lean_ParserCompiler_registerParserCompiler___redArg(v___x_3542_);
        return v___x_3543_;
    } else {
        return v___x_3541_;
    }
}
pub unsafe fn l_Lean_PrettyPrinter_registerParserCompilers___boxed(
    mut v_a_3544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3545_: *mut LeanObject = core::ptr::null_mut();
    v_res_3545_ = l_Lean_PrettyPrinter_registerParserCompilers();
    return v_res_3545_;
}
pub unsafe fn _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1() -> *mut LeanObject
{
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    v___x_3547_ = l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__0;
    v___x_3548_ = l_Lean_stringToMessageData(v___x_3547_);
    return v___x_3548_;
}
pub unsafe fn _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3() -> *mut LeanObject
{
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    v___x_3550_ = l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__2;
    v___x_3551_ = l_Lean_stringToMessageData(v___x_3550_);
    return v___x_3551_;
}
pub unsafe fn l_Lean_MessageData_ofFormatWithInfosM___lam__0(
    mut v_fmt_3552_: *mut LeanObject,
    mut v_ctx_3553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3559_: u8 = 0;
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3563_: u8 = 0;
    let mut v_a_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3567_: u8 = 0;
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3577_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3555_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_3553_, v_fmt_3552_);
                if lean_obj_tag(v___x_3555_) == 0 {
                    v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
                    v_isSharedCheck_3563_ = (!lean_is_exclusive(v___x_3555_)) as u8;
                    if v_isSharedCheck_3563_ == 0 {
                        v___x_3558_ = v___x_3555_;
                        v_isShared_3559_ = v_isSharedCheck_3563_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3556_);
                        lean_dec(v___x_3555_);
                        v___x_3558_ = lean_box(0);
                        v_isShared_3559_ = v_isSharedCheck_3563_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3564_ = lean_ctor_get(v___x_3555_, 0);
                    v_isSharedCheck_3577_ = (!lean_is_exclusive(v___x_3555_)) as u8;
                    if v_isSharedCheck_3577_ == 0 {
                        v___x_3566_ = v___x_3555_;
                        v_isShared_3567_ = v_isSharedCheck_3577_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3564_);
                        lean_dec(v___x_3555_);
                        v___x_3566_ = lean_box(0);
                        v_isShared_3567_ = v_isSharedCheck_3577_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3559_ == 0 {
                    v___x_3561_ = v___x_3558_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3556_);
                    v___x_3561_ = v_reuseFailAlloc_3562_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3561_;
            }
            3 => {
                v___x_3568_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1_once
                    ),
                    _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1,
                );
                v___x_3569_ = lean_io_error_to_string(v_a_3564_);
                if v_isShared_3567_ == 0 {
                    lean_ctor_set_tag(v___x_3566_, 3);
                    lean_ctor_set(v___x_3566_, 0, v___x_3569_);
                    v___x_3571_ = v___x_3566_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3576_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3569_);
                    v___x_3571_ = v_reuseFailAlloc_3576_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3572_ = l_Lean_MessageData_ofFormat(v___x_3571_);
                v___x_3573_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3573_, 0, v___x_3568_);
                lean_ctor_set(v___x_3573_, 1, v___x_3572_);
                v___x_3574_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3_once
                    ),
                    _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3,
                );
                v___x_3575_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3575_, 0, v___x_3573_);
                lean_ctor_set(v___x_3575_, 1, v___x_3574_);
                return v___x_3575_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MessageData_ofFormatWithInfosM___lam__0___boxed(
    mut v_fmt_3578_: *mut LeanObject,
    mut v_ctx_3579_: *mut LeanObject,
    mut v___y_3580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3581_: *mut LeanObject = core::ptr::null_mut();
    v_res_3581_ = l_Lean_MessageData_ofFormatWithInfosM___lam__0(v_fmt_3578_, v_ctx_3579_);
    lean_dec_ref(v_ctx_3579_);
    return v_res_3581_;
}
pub unsafe fn l_Lean_MessageData_ofFormatWithInfosM___lam__1(mut v_x_3582_: *mut LeanObject) -> u8 {
    let mut v___x_3583_: u8 = 0;
    v___x_3583_ = 0;
    return v___x_3583_;
}
pub unsafe fn l_Lean_MessageData_ofFormatWithInfosM___lam__1___boxed(
    mut v_x_3584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3585_: u8 = 0;
    let mut v_r_3586_: *mut LeanObject = core::ptr::null_mut();
    v_res_3585_ = l_Lean_MessageData_ofFormatWithInfosM___lam__1(v_x_3584_);
    lean_dec_ref(v_x_3584_);
    v_r_3586_ = lean_box((v_res_3585_) as usize);
    return v_r_3586_;
}
pub unsafe fn _init_l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2() -> *mut LeanObject
{
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    v___x_3590_ = l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__1;
    v___x_3591_ = l_Lean_MessageData_ofFormat(v___x_3590_);
    return v___x_3591_;
}
pub unsafe fn l_Lean_MessageData_ofFormatWithInfosM___lam__2(
    mut v_x_3592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    v___x_3594_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2),
        core::ptr::addr_of_mut!(l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2_once),
        _init_l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2,
    );
    return v___x_3594_;
}
pub unsafe fn l_Lean_MessageData_ofFormatWithInfosM___lam__2___boxed(
    mut v_x_3595_: *mut LeanObject,
    mut v___y_3596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3597_: *mut LeanObject = core::ptr::null_mut();
    v_res_3597_ = l_Lean_MessageData_ofFormatWithInfosM___lam__2(v_x_3595_);
    return v_res_3597_;
}
pub unsafe fn l_Lean_MessageData_ofFormatWithInfosM(
    mut v_fmt_3600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    v___f_3601_ = lean_alloc_closure(
        l_Lean_MessageData_ofFormatWithInfosM___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3601_, 0, v_fmt_3600_);
    v___f_3602_ = l_Lean_MessageData_ofFormatWithInfosM___closed__0;
    v___f_3603_ = l_Lean_MessageData_ofFormatWithInfosM___closed__1;
    v___x_3604_ = l_Lean_MessageData_lazy(v___f_3601_, v___f_3602_, v___f_3603_);
    return v___x_3604_;
}
pub unsafe fn l_panic___at___00Lean_MessageData_ofConst_spec__0(
    mut v___x_3605_: *mut LeanObject,
    mut v_msg_3606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    v___x_3607_ = lean_panic_fn_borrowed(v___x_3605_, v_msg_3606_);
    return v___x_3607_;
}
pub unsafe fn l_panic___at___00Lean_MessageData_ofConst_spec__0___boxed(
    mut v___x_3608_: *mut LeanObject,
    mut v_msg_3609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3610_: *mut LeanObject = core::ptr::null_mut();
    v_res_3610_ = l_panic___at___00Lean_MessageData_ofConst_spec__0(v___x_3608_, v_msg_3609_);
    lean_dec_ref(v___x_3608_);
    return v_res_3610_;
}
pub unsafe fn _init_l_Lean_MessageData_ofConst___closed__1() -> *mut LeanObject {
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    v___x_3612_ = l_Lean_MessageData_ofConst___closed__0;
    v___x_3613_ = l_Lean_stringToMessageData(v___x_3612_);
    return v___x_3613_;
}
pub unsafe fn _init_l_Lean_MessageData_ofConst___closed__2() -> *mut LeanObject {
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    v___x_3614_ = lean_box(1);
    v___x_3615_ = l_Lean_MessageData_ofFormat(v___x_3614_);
    return v___x_3615_;
}
pub unsafe fn _init_l_Lean_MessageData_ofConst___closed__3() -> *mut LeanObject {
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    v___x_3616_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MessageData_ofConst___closed__2),
        core::ptr::addr_of_mut!(l_Lean_MessageData_ofConst___closed__2_once),
        _init_l_Lean_MessageData_ofConst___closed__2,
    );
    v___x_3617_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MessageData_ofConst___closed__1),
        core::ptr::addr_of_mut!(l_Lean_MessageData_ofConst___closed__1_once),
        _init_l_Lean_MessageData_ofConst___closed__1,
    );
    v___x_3618_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3618_, 0, v___x_3617_);
    lean_ctor_set(v___x_3618_, 1, v___x_3616_);
    return v___x_3618_;
}
pub unsafe fn _init_l_Lean_MessageData_ofConst___closed__7() -> *mut LeanObject {
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    v___x_3622_ = l_Lean_MessageData_ofConst___closed__6;
    v___x_3623_ = lean_unsigned_to_nat(4);
    v___x_3624_ = lean_unsigned_to_nat(156);
    v___x_3625_ = l_Lean_MessageData_ofConst___closed__5;
    v___x_3626_ = l_Lean_MessageData_ofConst___closed__4;
    v___x_3627_ = l_mkPanicMessageWithDecl(
        v___x_3626_,
        v___x_3625_,
        v___x_3624_,
        v___x_3623_,
        v___x_3622_,
    );
    return v___x_3627_;
}
pub unsafe fn l_Lean_MessageData_ofConst(mut v_e_3628_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3629_: u8 = 0;
    v___x_3629_ = l_Lean_Expr_isConst(v_e_3628_);
    if v___x_3629_ == 0 {
        let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
        v___x_3630_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_MessageData_ofConst___closed__3),
            core::ptr::addr_of_mut!(l_Lean_MessageData_ofConst___closed__3_once),
            _init_l_Lean_MessageData_ofConst___closed__3,
        );
        v___x_3631_ = l_Lean_MessageData_ofExpr(v_e_3628_);
        v___x_3632_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_3632_, 0, v___x_3630_);
        lean_ctor_set(v___x_3632_, 1, v___x_3631_);
        v___x_3633_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_MessageData_ofConst___closed__7),
            core::ptr::addr_of_mut!(l_Lean_MessageData_ofConst___closed__7_once),
            _init_l_Lean_MessageData_ofConst___closed__7,
        );
        v___x_3634_ = lean_panic_fn_borrowed(v___x_3632_, v___x_3633_);
        lean_dec_ref_known(v___x_3632_, 2);
        return v___x_3634_;
    } else {
        let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
        let mut v_delab_3638_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
        v___x_3635_ = l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1;
        v___x_3636_ = lean_alloc_ctor(1, 0, (1) as u32);
        lean_ctor_set_uint8(v___x_3636_, 0 as u32, v___x_3629_);
        v___x_3637_ = l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__3;
        v_delab_3638_ = lean_alloc_closure(
            l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___boxed as *mut core::ffi::c_void,
            11,
            4,
        );
        lean_closure_set(v_delab_3638_, 0, lean_box(0));
        lean_closure_set(v_delab_3638_, 1, v___x_3635_);
        lean_closure_set(v_delab_3638_, 2, v___x_3636_);
        lean_closure_set(v_delab_3638_, 3, v___x_3637_);
        v___x_3639_ = lean_box(1);
        v___x_3640_ = lean_alloc_closure(
            l_Lean_PrettyPrinter_ppExprWithInfos___boxed as *mut core::ffi::c_void,
            8,
            3,
        );
        lean_closure_set(v___x_3640_, 0, v_e_3628_);
        lean_closure_set(v___x_3640_, 1, v___x_3639_);
        lean_closure_set(v___x_3640_, 2, v_delab_3638_);
        v___x_3641_ = l_Lean_MessageData_ofFormatWithInfosM(v___x_3640_);
        return v___x_3641_;
    }
}
pub unsafe fn _init_l_Lean_MessageData_signature___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    v___x_3643_ = l_Lean_MessageData_signature___lam__0___closed__0;
    v___x_3644_ = l_Lean_stringToMessageData(v___x_3643_);
    return v___x_3644_;
}
pub unsafe fn l_Lean_MessageData_signature___lam__0(
    mut v_c_3645_: *mut LeanObject,
    mut v_ctx_3646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3653_: u8 = 0;
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3657_: u8 = 0;
    let mut v_a_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3661_: u8 = 0;
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3675_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_c_3645_);
                v___x_3648_ = lean_alloc_closure(
                    l_Lean_PrettyPrinter_ppSignature___boxed as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___x_3648_, 0, v_c_3645_);
                v___x_3649_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_3646_, v___x_3648_);
                if lean_obj_tag(v___x_3649_) == 0 {
                    lean_dec(v_c_3645_);
                    v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
                    v_isSharedCheck_3657_ = (!lean_is_exclusive(v___x_3649_)) as u8;
                    if v_isSharedCheck_3657_ == 0 {
                        v___x_3652_ = v___x_3649_;
                        v_isShared_3653_ = v_isSharedCheck_3657_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3650_);
                        lean_dec(v___x_3649_);
                        v___x_3652_ = lean_box(0);
                        v_isShared_3653_ = v_isSharedCheck_3657_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3658_ = lean_ctor_get(v___x_3649_, 0);
                    v_isSharedCheck_3675_ = (!lean_is_exclusive(v___x_3649_)) as u8;
                    if v_isSharedCheck_3675_ == 0 {
                        v___x_3660_ = v___x_3649_;
                        v_isShared_3661_ = v_isSharedCheck_3675_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3658_);
                        lean_dec(v___x_3649_);
                        v___x_3660_ = lean_box(0);
                        v_isShared_3661_ = v_isSharedCheck_3675_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3653_ == 0 {
                    v___x_3655_ = v___x_3652_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_a_3650_);
                    v___x_3655_ = v_reuseFailAlloc_3656_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3655_;
            }
            3 => {
                v___x_3662_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MessageData_signature___lam__0___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_MessageData_signature___lam__0___closed__1_once),
                    _init_l_Lean_MessageData_signature___lam__0___closed__1,
                );
                v___x_3663_ = lean_io_error_to_string(v_a_3658_);
                if v_isShared_3661_ == 0 {
                    lean_ctor_set_tag(v___x_3660_, 3);
                    lean_ctor_set(v___x_3660_, 0, v___x_3663_);
                    v___x_3665_ = v___x_3660_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3674_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3663_);
                    v___x_3665_ = v_reuseFailAlloc_3674_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3666_ = l_Lean_MessageData_ofFormat(v___x_3665_);
                v___x_3667_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3667_, 0, v___x_3662_);
                lean_ctor_set(v___x_3667_, 1, v___x_3666_);
                v___x_3668_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3_once
                    ),
                    _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3,
                );
                v___x_3669_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3669_, 0, v___x_3667_);
                lean_ctor_set(v___x_3669_, 1, v___x_3668_);
                v___x_3670_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MessageData_ofConst___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_MessageData_ofConst___closed__2_once),
                    _init_l_Lean_MessageData_ofConst___closed__2,
                );
                v___x_3671_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3671_, 0, v___x_3669_);
                lean_ctor_set(v___x_3671_, 1, v___x_3670_);
                v___x_3672_ = l_Lean_MessageData_ofName(v_c_3645_);
                v___x_3673_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3673_, 0, v___x_3671_);
                lean_ctor_set(v___x_3673_, 1, v___x_3672_);
                return v___x_3673_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MessageData_signature___lam__0___boxed(
    mut v_c_3676_: *mut LeanObject,
    mut v_ctx_3677_: *mut LeanObject,
    mut v___y_3678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3679_: *mut LeanObject = core::ptr::null_mut();
    v_res_3679_ = l_Lean_MessageData_signature___lam__0(v_c_3676_, v_ctx_3677_);
    lean_dec_ref(v_ctx_3677_);
    return v_res_3679_;
}
pub unsafe fn l_Lean_MessageData_signature(mut v_c_3680_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
    v___f_3681_ = lean_alloc_closure(
        l_Lean_MessageData_signature___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_3681_, 0, v_c_3680_);
    v___f_3682_ = l_Lean_MessageData_ofFormatWithInfosM___closed__0;
    v___f_3683_ = l_Lean_MessageData_ofFormatWithInfosM___closed__1;
    v___x_3684_ = l_Lean_MessageData_lazy(v___f_3681_, v___f_3682_, v___f_3683_);
    return v___x_3684_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_PrettyPrinter(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Module(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_ParserCompiler(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_NumObjs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ShareCommon(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_PrettyPrinter_pp_exprSizes = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_PrettyPrinter_pp_exprSizes);
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l_Lean_PrettyPrinter_registerParserCompilers();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_PrettyPrinter(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_PrettyPrinter(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_PrettyPrinter_Delaborator_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_PrettyPrinter_Delaborator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Parser_Module(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_ParserCompiler(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_NumObjs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_ShareCommon(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_PrettyPrinter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_PrettyPrinter(builtin);
}

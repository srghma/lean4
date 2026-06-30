// Lean compiler output
// Module: Lean.PrettyPrinter
// Imports: Lean.PrettyPrinter.Delaborator.Basic Lean.PrettyPrinter.Delaborator Lean.Parser.Module Lean.ParserCompiler Lean.Util.NumObjs Lean.Util.ShareCommon
use crate::ffi::{
    lean_array_get, lean_array_size, lean_array_uget, lean_array_uset, lean_expr_dbg_to_string,
    lean_io_get_num_heartbeats, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_panic_fn_borrowed, lean_sharecommon_quick, lean_st_mk_ref, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_string_append, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::lean_mk_syntax_ident;
use crate::r#gen::Init::Prelude::{l_Lean_firstFrontendMacroScope, l_Lean_replaceRef};
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
pub static l_Lean_PrettyPrinter_ppTerm___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_PrettyPrinter_ppTerm___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppTerm___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_ppTerm___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_PrettyPrinter_ppTerm___closed__0_value)
                as *mut leanh::LeanObject,
            8609355255726335675 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_PrettyPrinter_ppTerm___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppTerm___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [112, 112, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 120, 112, 114, 83, 105, 122, 101, 115, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut leanh::LeanObject,6746591144584426489 as *mut leanh::LeanObject] };
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut leanh::LeanObject,14719458919086744478 as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value: leanh::LeanStringObject<146> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 146, m_capacity: 146, m_length: 145, m_data: [40, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116, 101, 114, 41, 32, 112, 114, 101, 102, 105, 120, 32, 101, 97, 99, 104, 32, 101, 109, 98, 101, 100, 100, 101, 100, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 119, 105, 116, 104, 32, 105, 116, 115, 32, 115, 105, 122, 101, 115, 32, 105, 110, 32, 116, 104, 101, 32, 102, 111, 114, 109, 97, 116, 32, 40, 115, 105, 122, 101, 32, 100, 105, 115, 114, 101, 103, 97, 114, 100, 105, 110, 103, 32, 115, 104, 97, 114, 105, 110, 103, 47, 115, 105, 122, 101, 32, 119, 105, 116, 104, 32, 115, 104, 97, 114, 105, 110, 103, 47, 115, 105, 122, 101, 32, 119, 105, 116, 104, 32, 109, 97, 120, 32, 115, 104, 97, 114, 105, 110, 103, 41, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut leanh::LeanObject,300274991653824376 as *mut leanh::LeanObject] };
static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut leanh::LeanObject,8668468711051311310 as *mut leanh::LeanObject] };
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut leanh::LeanObject,615934169399469925 as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l_Lean_PrettyPrinter_pp_exprSizes: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [91, 115, 105, 122, 101, 32, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [47, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__2_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__4_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [93, 32, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__5_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__4_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_ppExpr___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PrettyPrinter_ppExpr___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_PrettyPrinter_ppExpr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppExpr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__0_value:
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
    m_data: [116, 97, 103, 65, 112, 112, 70, 110, 115, 0],
};
static mut l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut leanh::LeanObject,6746591144584426489 as *mut leanh::LeanObject] };
pub static l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__0_value)
            as *mut leanh::LeanObject,
        11389724230315925419 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 1,
    },
    m_objs: [1 as *mut leanh::LeanObject],
};
static mut l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__3_value:
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
    m_fun: l_Lean_PrettyPrinter_Delaborator_delabConst___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__4_value:
    leanh::LeanClosureObject<4> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___boxed as *const core::ffi::c_void,
    m_arity: 11,
    m_num_fixed: 4,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_ppExprLegacy___closed__0_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0
                + 24) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [
            282574488338432 as *mut leanh::LeanObject,
            72621647814721793 as *mut leanh::LeanObject,
            65793 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppExprLegacy___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__1: u64 = 0;
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_ppExprLegacy___closed__3_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppExprLegacy___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_ppExprLegacy___closed__13_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppExprLegacy___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_ppExprLegacy___closed__14_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_PrettyPrinter_ppExprLegacy___closed__13_value)
                as *mut leanh::LeanObject,
            3978731030111751661 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppExprLegacy___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_ppExprLegacy___closed__15_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_PrettyPrinter_ppExprLegacy___closed__14_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppExprLegacy___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_ppExprLegacy___closed__16_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppExprLegacy___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_ppExprLegacy___closed__19_value: leanh::LeanStringObject<
    21,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32,
        35, 0,
    ],
};
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppExprLegacy___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_ppExprLegacy___closed__20_value: leanh::LeanStringObject<
    16,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppExprLegacy___closed__20_value)
        as *mut leanh::LeanObject;
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__22: u8 = 0;
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_PrettyPrinter_ppExprLegacy___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_ppLevel___closed__0_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_PrettyPrinter_ppLevel___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppLevel___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_ppLevel___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_PrettyPrinter_ppLevel___closed__0_value)
                as *mut leanh::LeanObject,
            18250387975948097528 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_PrettyPrinter_ppLevel___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppLevel___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_ppTactic___closed__0_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_PrettyPrinter_ppTactic___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppTactic___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_ppTactic___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_PrettyPrinter_ppTactic___closed__0_value)
                as *mut leanh::LeanObject,
            16145843736367156323 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_PrettyPrinter_ppTactic___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppTactic___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_ppCommand___closed__0_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_PrettyPrinter_ppCommand___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppCommand___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_ppCommand___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_PrettyPrinter_ppCommand___closed__0_value)
                as *mut leanh::LeanObject,
            5063646790596052253 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_PrettyPrinter_ppCommand___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppCommand___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_ppModule___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_Module_module_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_PrettyPrinter_ppModule___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppModule___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_ppModule___closed__1_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_Module_module_formatter___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_PrettyPrinter_ppModule___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppModule___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_ppSignature___closed__0_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PrettyPrinter_Delaborator_delabConstWithSignature___boxed
            as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 1,
        m_objs: [(((1 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lean_PrettyPrinter_ppSignature___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppSignature___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_ppSignature___closed__1_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_PrettyPrinter_ppSignature___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_ppSignature___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0___closed__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Delaborator_delab___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0___closed__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0___closed__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value: leanh::LeanCtorObject<5> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut leanh::LeanObject,61860673417901001 as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__3_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut leanh::LeanObject,9744575919760971988 as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,5398202083655750613 as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut leanh::LeanObject,9389539652570169024 as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11976248792036758390 as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__8_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10922233481441388379 as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__9_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__10_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5240565782728729790 as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__11_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut leanh::LeanObject,15235184053563701895 as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__12_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__6_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__value) as *mut leanh::LeanObject,5863280441230316749 as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__13_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 675687902 as usize) << 1) | 1) as *mut leanh::LeanObject,4673300960555192562 as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__14_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__15_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1664012690685931901 as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__17_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__17_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__17_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__18_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__16_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__17_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8299898913973098717 as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__18_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__18_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__19_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__18_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,8491952124216464304 as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__19_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__19_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_registerParserCompilers___closed__0_value:
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
        112, 97, 114, 101, 110, 116, 104, 101, 115, 105, 122, 101, 114, 0,
    ],
};
static mut l_Lean_PrettyPrinter_registerParserCompilers___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_registerParserCompilers___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_registerParserCompilers___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PrettyPrinter_registerParserCompilers___closed__0_value)
            as *mut leanh::LeanObject,
        4356502393917455154 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_PrettyPrinter_registerParserCompilers___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_registerParserCompilers___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_PrettyPrinter_registerParserCompilers___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_registerParserCompilers___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_registerParserCompilers___closed__3_value:
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
    m_data: [102, 111, 114, 109, 97, 116, 116, 101, 114, 0],
};
static mut l_Lean_PrettyPrinter_registerParserCompilers___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_registerParserCompilers___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_registerParserCompilers___closed__4_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PrettyPrinter_registerParserCompilers___closed__3_value)
            as *mut leanh::LeanObject,
        7217738091093750654 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_PrettyPrinter_registerParserCompilers___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_registerParserCompilers___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_PrettyPrinter_registerParserCompilers___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_registerParserCompilers___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__0_value:
    leanh::LeanStringObject<25> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        91, 69, 114, 114, 111, 114, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116,
        105, 110, 103, 58, 32, 0,
    ],
};
static mut l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__2_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__0_value:
    leanh::LeanStringObject<44> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 44,
    m_capacity: 44,
    m_length: 43,
    m_data: [
        40, 105, 110, 118, 97, 108, 105, 100, 32, 77, 101, 115, 115, 97, 103, 101, 68, 97, 116, 97,
        46, 108, 97, 122, 121, 44, 32, 109, 105, 115, 115, 105, 110, 103, 32, 99, 111, 110, 116,
        101, 120, 116, 41, 0,
    ],
};
static mut l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MessageData_ofFormatWithInfosM___closed__0_value:
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
    m_fun: l_Lean_MessageData_ofFormatWithInfosM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_MessageData_ofFormatWithInfosM___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_ofFormatWithInfosM___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MessageData_ofFormatWithInfosM___closed__1_value:
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
    m_fun: l_Lean_MessageData_ofFormatWithInfosM___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_MessageData_ofFormatWithInfosM___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_ofFormatWithInfosM___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MessageData_ofConst___closed__0_value: leanh::LeanStringObject<51> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 51,
        m_capacity: 51,
        m_length: 50,
        m_data: [
            91, 69, 114, 114, 111, 114, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110,
            116, 105, 110, 103, 58, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 110,
            111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 97, 110, 116, 93, 0,
        ],
    };
static mut l_Lean_MessageData_ofConst___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_ofConst___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_MessageData_ofConst___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MessageData_ofConst___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MessageData_ofConst___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MessageData_ofConst___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MessageData_ofConst___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MessageData_ofConst___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MessageData_ofConst___closed__4_value: leanh::LeanStringObject<19> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_MessageData_ofConst___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_ofConst___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MessageData_ofConst___closed__5_value: leanh::LeanStringObject<25> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 115, 115, 97, 103, 101, 68, 97, 116, 97, 46, 111, 102,
            67, 111, 110, 115, 116, 0,
        ],
    };
static mut l_Lean_MessageData_ofConst___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_ofConst___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_MessageData_ofConst___closed__6_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_MessageData_ofConst___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_ofConst___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_MessageData_ofConst___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MessageData_ofConst___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MessageData_signature___lam__0___closed__0_value: leanh::LeanStringObject<
    35,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        91, 69, 114, 114, 111, 114, 32, 112, 114, 101, 116, 116, 121, 32, 112, 114, 105, 110, 116,
        105, 110, 103, 32, 115, 105, 103, 110, 97, 116, 117, 114, 101, 58, 32, 0,
    ],
};
static mut l_Lean_MessageData_signature___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_signature___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_MessageData_signature___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MessageData_signature___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_PrettyPrinter_ppCategory(
    mut v_cat_1843_: *mut leanh::LeanObject,
    mut v_stx_1844_: *mut leanh::LeanObject,
    mut v_a_1845_: *mut leanh::LeanObject,
    mut v_a_1846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1859_: u8 = 0;
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1863_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_1848_ = leanh::lean_ctor_get(v_a_1845_, 2);
                v___x_1849_ = leanh::lean_box(1);
                leanh::lean_inc_ref(v_options_1848_);
                v___x_1850_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1850_, 0, v_options_1848_);
                leanh::lean_ctor_set(v___x_1850_, 1, v___x_1849_);
                leanh::lean_ctor_set(v___x_1850_, 2, v___x_1849_);
                v___x_1851_ = l_Lean_sanitizeSyntax(v_stx_1844_, v___x_1850_);
                v_fst_1852_ = leanh::lean_ctor_get(v___x_1851_, 0);
                leanh::lean_inc(v_fst_1852_);
                leanh::lean_dec_ref(v___x_1851_);
                leanh::lean_inc(v_cat_1843_);
                v___x_1853_ = l_Lean_PrettyPrinter_parenthesizeCategory(
                    v_cat_1843_,
                    v_fst_1852_,
                    v_a_1845_,
                    v_a_1846_,
                );
                if leanh::lean_obj_tag(v___x_1853_) == 0 {
                    v_a_1854_ = leanh::lean_ctor_get(v___x_1853_, 0);
                    leanh::lean_inc(v_a_1854_);
                    leanh::lean_dec_ref_known(v___x_1853_, 1);
                    v___x_1855_ = l_Lean_PrettyPrinter_formatCategory(
                        v_cat_1843_,
                        v_a_1854_,
                        v_a_1845_,
                        v_a_1846_,
                    );
                    return v___x_1855_;
                } else {
                    leanh::lean_dec(v_cat_1843_);
                    v_a_1856_ = leanh::lean_ctor_get(v___x_1853_, 0);
                    v_isSharedCheck_1863_ = (!leanh::lean_is_exclusive(v___x_1853_)) as u8;
                    if v_isSharedCheck_1863_ == 0 {
                        v___x_1858_ = v___x_1853_;
                        v_isShared_1859_ = v_isSharedCheck_1863_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1856_);
                        leanh::lean_dec(v___x_1853_);
                        v___x_1858_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1862_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
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
    mut v_cat_1864_: *mut leanh::LeanObject,
    mut v_stx_1865_: *mut leanh::LeanObject,
    mut v_a_1866_: *mut leanh::LeanObject,
    mut v_a_1867_: *mut leanh::LeanObject,
    mut v_a_1868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1869_ = l_Lean_PrettyPrinter_ppCategory(v_cat_1864_, v_stx_1865_, v_a_1866_, v_a_1867_);
    leanh::lean_dec(v_a_1867_);
    leanh::lean_dec_ref(v_a_1866_);
    return v_res_1869_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppTerm(
    mut v_stx_1873_: *mut leanh::LeanObject,
    mut v_a_1874_: *mut leanh::LeanObject,
    mut v_a_1875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1877_ = l_Lean_PrettyPrinter_ppTerm___closed__1;
    v___x_1878_ = l_Lean_PrettyPrinter_ppCategory(v___x_1877_, v_stx_1873_, v_a_1874_, v_a_1875_);
    return v___x_1878_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppTerm___boxed(
    mut v_stx_1879_: *mut leanh::LeanObject,
    mut v_a_1880_: *mut leanh::LeanObject,
    mut v_a_1881_: *mut leanh::LeanObject,
    mut v_a_1882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1883_ = l_Lean_PrettyPrinter_ppTerm(v_stx_1879_, v_a_1880_, v_a_1881_);
    leanh::lean_dec(v_a_1881_);
    leanh::lean_dec_ref(v_a_1880_);
    return v_res_1883_;
}
pub unsafe fn l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___redArg(
    mut v_lctx_1884_: *mut leanh::LeanObject,
    mut v_x_1885_: *mut leanh::LeanObject,
    mut v___y_1886_: *mut leanh::LeanObject,
    mut v___y_1887_: *mut leanh::LeanObject,
    mut v___y_1888_: *mut leanh::LeanObject,
    mut v___y_1889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_keyedConfig_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trackZetaDelta_1892_: u8 = 0;
    let mut v_zetaDeltaSet_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_1898_: u8 = 0;
    let mut v_inTypeClassResolution_1899_: u8 = 0;
    let mut v_cacheInferType_1900_: u8 = 0;
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_keyedConfig_1891_ = leanh::lean_ctor_get(v___y_1886_, 0);
    v_trackZetaDelta_1892_ = leanh::lean_ctor_get_uint8(
        v___y_1886_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
    );
    v_zetaDeltaSet_1893_ = leanh::lean_ctor_get(v___y_1886_, 1);
    v_localInstances_1894_ = leanh::lean_ctor_get(v___y_1886_, 3);
    v_defEqCtx_x3f_1895_ = leanh::lean_ctor_get(v___y_1886_, 4);
    v_synthPendingDepth_1896_ = leanh::lean_ctor_get(v___y_1886_, 5);
    v_canUnfold_x3f_1897_ = leanh::lean_ctor_get(v___y_1886_, 6);
    v_univApprox_1898_ = leanh::lean_ctor_get_uint8(
        v___y_1886_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
    );
    v_inTypeClassResolution_1899_ = leanh::lean_ctor_get_uint8(
        v___y_1886_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
    );
    v_cacheInferType_1900_ = leanh::lean_ctor_get_uint8(
        v___y_1886_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
    );
    leanh::lean_inc(v_canUnfold_x3f_1897_);
    leanh::lean_inc(v_synthPendingDepth_1896_);
    leanh::lean_inc(v_defEqCtx_x3f_1895_);
    leanh::lean_inc_ref(v_localInstances_1894_);
    leanh::lean_inc(v_zetaDeltaSet_1893_);
    leanh::lean_inc_ref(v_keyedConfig_1891_);
    v___x_1901_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
    leanh::lean_ctor_set(v___x_1901_, 0, v_keyedConfig_1891_);
    leanh::lean_ctor_set(v___x_1901_, 1, v_zetaDeltaSet_1893_);
    leanh::lean_ctor_set(v___x_1901_, 2, v_lctx_1884_);
    leanh::lean_ctor_set(v___x_1901_, 3, v_localInstances_1894_);
    leanh::lean_ctor_set(v___x_1901_, 4, v_defEqCtx_x3f_1895_);
    leanh::lean_ctor_set(v___x_1901_, 5, v_synthPendingDepth_1896_);
    leanh::lean_ctor_set(v___x_1901_, 6, v_canUnfold_x3f_1897_);
    leanh::lean_ctor_set_uint8(
        v___x_1901_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
        v_trackZetaDelta_1892_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1901_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
        v_univApprox_1898_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1901_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
        v_inTypeClassResolution_1899_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1901_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
        v_cacheInferType_1900_,
    );
    leanh::lean_inc(v___y_1889_);
    leanh::lean_inc_ref(v___y_1888_);
    leanh::lean_inc(v___y_1887_);
    v___x_1902_ = leanh::lean_apply_5(
        v_x_1885_,
        v___x_1901_,
        v___y_1887_,
        v___y_1888_,
        v___y_1889_,
        leanh::lean_box(0),
    );
    return v___x_1902_;
}
pub unsafe fn l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___redArg___boxed(
    mut v_lctx_1903_: *mut leanh::LeanObject,
    mut v_x_1904_: *mut leanh::LeanObject,
    mut v___y_1905_: *mut leanh::LeanObject,
    mut v___y_1906_: *mut leanh::LeanObject,
    mut v___y_1907_: *mut leanh::LeanObject,
    mut v___y_1908_: *mut leanh::LeanObject,
    mut v___y_1909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1910_ = l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0___redArg(
        v_lctx_1903_,
        v_x_1904_,
        v___y_1905_,
        v___y_1906_,
        v___y_1907_,
        v___y_1908_,
    );
    leanh::lean_dec(v___y_1908_);
    leanh::lean_dec_ref(v___y_1907_);
    leanh::lean_dec(v___y_1906_);
    leanh::lean_dec_ref(v___y_1905_);
    return v_res_1910_;
}
pub unsafe fn l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0(
    mut v_00_u03b1_1911_: *mut leanh::LeanObject,
    mut v_lctx_1912_: *mut leanh::LeanObject,
    mut v_x_1913_: *mut leanh::LeanObject,
    mut v___y_1914_: *mut leanh::LeanObject,
    mut v___y_1915_: *mut leanh::LeanObject,
    mut v___y_1916_: *mut leanh::LeanObject,
    mut v___y_1917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1920_: *mut leanh::LeanObject,
    mut v_lctx_1921_: *mut leanh::LeanObject,
    mut v_x_1922_: *mut leanh::LeanObject,
    mut v___y_1923_: *mut leanh::LeanObject,
    mut v___y_1924_: *mut leanh::LeanObject,
    mut v___y_1925_: *mut leanh::LeanObject,
    mut v___y_1926_: *mut leanh::LeanObject,
    mut v___y_1927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1928_ = l_Lean_Meta_withLCtx_x27___at___00Lean_PrettyPrinter_ppUsing_spec__0(
        v_00_u03b1_1920_,
        v_lctx_1921_,
        v_x_1922_,
        v___y_1923_,
        v___y_1924_,
        v___y_1925_,
        v___y_1926_,
    );
    leanh::lean_dec(v___y_1926_);
    leanh::lean_dec_ref(v___y_1925_);
    leanh::lean_dec(v___y_1924_);
    leanh::lean_dec_ref(v___y_1923_);
    return v_res_1928_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppUsing___lam__0(
    mut v_delab_1929_: *mut leanh::LeanObject,
    mut v_e_1930_: *mut leanh::LeanObject,
    mut v___y_1931_: *mut leanh::LeanObject,
    mut v___y_1932_: *mut leanh::LeanObject,
    mut v___y_1933_: *mut leanh::LeanObject,
    mut v___y_1934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1942_: u8 = 0;
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1946_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_1934_);
                leanh::lean_inc_ref(v___y_1933_);
                v___x_1936_ = leanh::lean_apply_6(
                    v_delab_1929_,
                    v_e_1930_,
                    v___y_1931_,
                    v___y_1932_,
                    v___y_1933_,
                    v___y_1934_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1936_) == 0 {
                    v_a_1937_ = leanh::lean_ctor_get(v___x_1936_, 0);
                    leanh::lean_inc(v_a_1937_);
                    leanh::lean_dec_ref_known(v___x_1936_, 1);
                    v___x_1938_ = l_Lean_PrettyPrinter_ppTerm(v_a_1937_, v___y_1933_, v___y_1934_);
                    leanh::lean_dec(v___y_1934_);
                    leanh::lean_dec_ref(v___y_1933_);
                    return v___x_1938_;
                } else {
                    leanh::lean_dec(v___y_1934_);
                    leanh::lean_dec_ref(v___y_1933_);
                    v_a_1939_ = leanh::lean_ctor_get(v___x_1936_, 0);
                    v_isSharedCheck_1946_ = (!leanh::lean_is_exclusive(v___x_1936_)) as u8;
                    if v_isSharedCheck_1946_ == 0 {
                        v___x_1941_ = v___x_1936_;
                        v_isShared_1942_ = v_isSharedCheck_1946_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1939_);
                        leanh::lean_dec(v___x_1936_);
                        v___x_1941_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1945_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
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
    mut v_delab_1947_: *mut leanh::LeanObject,
    mut v_e_1948_: *mut leanh::LeanObject,
    mut v___y_1949_: *mut leanh::LeanObject,
    mut v___y_1950_: *mut leanh::LeanObject,
    mut v___y_1951_: *mut leanh::LeanObject,
    mut v___y_1952_: *mut leanh::LeanObject,
    mut v___y_1953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_e_1955_: *mut leanh::LeanObject,
    mut v_delab_1956_: *mut leanh::LeanObject,
    mut v_a_1957_: *mut leanh::LeanObject,
    mut v_a_1958_: *mut leanh::LeanObject,
    mut v_a_1959_: *mut leanh::LeanObject,
    mut v_a_1960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lctx_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lctx_1962_ = leanh::lean_ctor_get(v_a_1957_, 2);
    v_options_1963_ = leanh::lean_ctor_get(v_a_1959_, 2);
    v___x_1964_ = leanh::lean_box(1);
    leanh::lean_inc_ref(v_options_1963_);
    v___x_1965_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1965_, 0, v_options_1963_);
    leanh::lean_ctor_set(v___x_1965_, 1, v___x_1964_);
    leanh::lean_ctor_set(v___x_1965_, 2, v___x_1964_);
    leanh::lean_inc_ref(v_lctx_1962_);
    v___x_1966_ = l_Lean_LocalContext_sanitizeNames(v_lctx_1962_, v___x_1965_);
    v_fst_1967_ = leanh::lean_ctor_get(v___x_1966_, 0);
    leanh::lean_inc(v_fst_1967_);
    leanh::lean_dec_ref(v___x_1966_);
    v___f_1968_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_ppUsing___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_1968_, 0, v_delab_1956_);
    leanh::lean_closure_set(v___f_1968_, 1, v_e_1955_);
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
    mut v_e_1970_: *mut leanh::LeanObject,
    mut v_delab_1971_: *mut leanh::LeanObject,
    mut v_a_1972_: *mut leanh::LeanObject,
    mut v_a_1973_: *mut leanh::LeanObject,
    mut v_a_1974_: *mut leanh::LeanObject,
    mut v_a_1975_: *mut leanh::LeanObject,
    mut v_a_1976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1977_ = l_Lean_PrettyPrinter_ppUsing(
        v_e_1970_,
        v_delab_1971_,
        v_a_1972_,
        v_a_1973_,
        v_a_1974_,
        v_a_1975_,
    );
    leanh::lean_dec(v_a_1975_);
    leanh::lean_dec_ref(v_a_1974_);
    leanh::lean_dec(v_a_1973_);
    leanh::lean_dec_ref(v_a_1972_);
    return v_res_1977_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__spec__0(
    mut v_name_1978_: *mut leanh::LeanObject,
    mut v_decl_1979_: *mut leanh::LeanObject,
    mut v_ref_1980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defValue_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: u8 = 0;
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1991_: u8 = 0;
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1996_: u8 = 0;
    let mut v_unused_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2001_: u8 = 0;
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2005_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_1982_ = leanh::lean_ctor_get(v_decl_1979_, 0);
                v_descr_1983_ = leanh::lean_ctor_get(v_decl_1979_, 1);
                v_deprecation_x3f_1984_ = leanh::lean_ctor_get(v_decl_1979_, 2);
                v___x_1985_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_1986_ = (leanh::lean_unbox(v_defValue_1982_) as u8);
                leanh::lean_ctor_set_uint8(v___x_1985_, 0 as u32, v___x_1986_);
                leanh::lean_inc(v_deprecation_x3f_1984_);
                leanh::lean_inc_ref(v_descr_1983_);
                leanh::lean_inc_n(v_name_1978_, 2);
                v___x_1987_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_1987_, 0, v_name_1978_);
                leanh::lean_ctor_set(v___x_1987_, 1, v_ref_1980_);
                leanh::lean_ctor_set(v___x_1987_, 2, v___x_1985_);
                leanh::lean_ctor_set(v___x_1987_, 3, v_descr_1983_);
                leanh::lean_ctor_set(v___x_1987_, 4, v_deprecation_x3f_1984_);
                v___x_1988_ = lean_register_option(v_name_1978_, v___x_1987_);
                if leanh::lean_obj_tag(v___x_1988_) == 0 {
                    v_isSharedCheck_1996_ = (!leanh::lean_is_exclusive(v___x_1988_)) as u8;
                    if v_isSharedCheck_1996_ == 0 {
                        v_unused_1997_ = leanh::lean_ctor_get(v___x_1988_, 0);
                        leanh::lean_dec(v_unused_1997_);
                        v___x_1990_ = v___x_1988_;
                        v_isShared_1991_ = v_isSharedCheck_1996_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1988_);
                        v___x_1990_ = leanh::lean_box(0);
                        v_isShared_1991_ = v_isSharedCheck_1996_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_name_1978_);
                    v_a_1998_ = leanh::lean_ctor_get(v___x_1988_, 0);
                    v_isSharedCheck_2005_ = (!leanh::lean_is_exclusive(v___x_1988_)) as u8;
                    if v_isSharedCheck_2005_ == 0 {
                        v___x_2000_ = v___x_1988_;
                        v_isShared_2001_ = v_isSharedCheck_2005_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1998_);
                        leanh::lean_dec(v___x_1988_);
                        v___x_2000_ = leanh::lean_box(0);
                        v_isShared_2001_ = v_isSharedCheck_2005_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_defValue_1982_);
                v___x_1992_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1992_, 0, v_name_1978_);
                leanh::lean_ctor_set(v___x_1992_, 1, v_defValue_1982_);
                if v_isShared_1991_ == 0 {
                    leanh::lean_ctor_set(v___x_1990_, 0, v___x_1992_);
                    v___x_1994_ = v___x_1990_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1995_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1992_);
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
                    v_reuseFailAlloc_2004_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1998_);
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
    mut v_name_2006_: *mut leanh::LeanObject,
    mut v_decl_2007_: *mut leanh::LeanObject,
    mut v_ref_2008_: *mut leanh::LeanObject,
    mut v_a_2009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2010_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__spec__0(v_name_2006_, v_decl_2007_, v_ref_2008_);
    leanh::lean_dec_ref(v_decl_2007_);
    return v_res_2010_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2030_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__2_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_;
    v___x_2031_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__4_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_;
    v___x_2032_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__7_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_;
    v___x_2033_ = l_Lean_Option_register___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4__spec__0(v___x_2030_, v___x_2031_, v___x_2032_);
    return v___x_2033_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4____boxed(
    mut v_a_2034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2035_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_();
    return v_res_2035_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(
    mut v_opts_2036_: *mut leanh::LeanObject,
    mut v_opt_2037_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_2038_ = leanh::lean_ctor_get(v_opt_2037_, 0);
    v_defValue_2039_ = leanh::lean_ctor_get(v_opt_2037_, 1);
    v_map_2040_ = leanh::lean_ctor_get(v_opts_2036_, 0);
    v___x_2041_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2040_,
            v_name_2038_,
        );
    if leanh::lean_obj_tag(v___x_2041_) == 0 {
        let mut v___x_2042_: u8 = 0;
        v___x_2042_ = (leanh::lean_unbox(v_defValue_2039_) as u8);
        return v___x_2042_;
    } else {
        let mut v_val_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2043_ = leanh::lean_ctor_get(v___x_2041_, 0);
        leanh::lean_inc(v_val_2043_);
        leanh::lean_dec_ref_known(v___x_2041_, 1);
        if leanh::lean_obj_tag(v_val_2043_) == 1 {
            let mut v_v_2044_: u8 = 0;
            v_v_2044_ = leanh::lean_ctor_get_uint8(v_val_2043_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_2043_, 0);
            return v_v_2044_;
        } else {
            let mut v___x_2045_: u8 = 0;
            leanh::lean_dec(v_val_2043_);
            v___x_2045_ = (leanh::lean_unbox(v_defValue_2039_) as u8);
            return v___x_2045_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0___boxed(
    mut v_opts_2046_: *mut leanh::LeanObject,
    mut v_opt_2047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2048_: u8 = 0;
    let mut v_r_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2048_ = l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(v_opts_2046_, v_opt_2047_);
    leanh::lean_dec_ref(v_opt_2047_);
    leanh::lean_dec_ref(v_opts_2046_);
    v_r_2049_ = leanh::lean_box((v_res_2048_) as usize);
    return v_r_2049_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(
    mut v_e_2059_: *mut leanh::LeanObject,
    mut v_f_2060_: *mut leanh::LeanObject,
    mut v_a_2061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: u8 = 0;
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2075_: u8 = 0;
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2096_: u8 = 0;
    let mut v_a_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2100_: u8 = 0;
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2108_: u8 = 0;
    let mut v_a_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2112_: u8 = 0;
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2120_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_2063_ = leanh::lean_ctor_get(v_a_2061_, 2);
                v_ref_2064_ = leanh::lean_ctor_get(v_a_2061_, 5);
                v___x_2065_ = l_Lean_PrettyPrinter_pp_exprSizes;
                v___x_2066_ = l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(v_options_2063_, v___x_2065_);
                if v___x_2066_ == 0 {
                    leanh::lean_dec_ref(v_e_2059_);
                    v___x_2067_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2067_, 0, v_f_2060_);
                    return v___x_2067_;
                } else {
                    leanh::lean_inc_ref(v_e_2059_);
                    v___x_2068_ = l_Lean_Expr_numObjs(v_e_2059_);
                    if leanh::lean_obj_tag(v___x_2068_) == 0 {
                        v_a_2069_ = leanh::lean_ctor_get(v___x_2068_, 0);
                        leanh::lean_inc(v_a_2069_);
                        leanh::lean_dec_ref_known(v___x_2068_, 1);
                        v___x_2070_ = lean_sharecommon_quick(v_e_2059_);
                        v___x_2071_ = l_Lean_Expr_numObjs(v___x_2070_);
                        if leanh::lean_obj_tag(v___x_2071_) == 0 {
                            v_a_2072_ = leanh::lean_ctor_get(v___x_2071_, 0);
                            v_isSharedCheck_2096_ =
                                (!leanh::lean_is_exclusive(v___x_2071_)) as u8;
                            if v_isSharedCheck_2096_ == 0 {
                                v___x_2074_ = v___x_2071_;
                                v_isShared_2075_ = v_isSharedCheck_2096_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2072_);
                                leanh::lean_dec(v___x_2071_);
                                v___x_2074_ = leanh::lean_box(0);
                                v_isShared_2075_ = v_isSharedCheck_2096_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_2069_);
                            leanh::lean_dec(v_f_2060_);
                            leanh::lean_dec_ref(v_e_2059_);
                            v_a_2097_ = leanh::lean_ctor_get(v___x_2071_, 0);
                            v_isSharedCheck_2108_ =
                                (!leanh::lean_is_exclusive(v___x_2071_)) as u8;
                            if v_isSharedCheck_2108_ == 0 {
                                v___x_2099_ = v___x_2071_;
                                v_isShared_2100_ = v_isSharedCheck_2108_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2097_);
                                leanh::lean_dec(v___x_2071_);
                                v___x_2099_ = leanh::lean_box(0);
                                v_isShared_2100_ = v_isSharedCheck_2108_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_f_2060_);
                        leanh::lean_dec_ref(v_e_2059_);
                        v_a_2109_ = leanh::lean_ctor_get(v___x_2068_, 0);
                        v_isSharedCheck_2120_ =
                            (!leanh::lean_is_exclusive(v___x_2068_)) as u8;
                        if v_isSharedCheck_2120_ == 0 {
                            v___x_2111_ = v___x_2068_;
                            v_isShared_2112_ = v_isSharedCheck_2120_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2109_);
                            leanh::lean_dec(v___x_2068_);
                            v___x_2111_ = leanh::lean_box(0);
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
                leanh::lean_dec_ref(v_e_2059_);
                v___x_2078_ = l_Nat_reprFast(v___x_2077_);
                v___x_2079_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2079_, 0, v___x_2078_);
                v___x_2080_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2080_, 0, v___x_2076_);
                leanh::lean_ctor_set(v___x_2080_, 1, v___x_2079_);
                v___x_2081_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__3;
                v___x_2082_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2082_, 0, v___x_2080_);
                leanh::lean_ctor_set(v___x_2082_, 1, v___x_2081_);
                v___x_2083_ = l_Nat_reprFast(v_a_2069_);
                v___x_2084_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2084_, 0, v___x_2083_);
                v___x_2085_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2085_, 0, v___x_2082_);
                leanh::lean_ctor_set(v___x_2085_, 1, v___x_2084_);
                v___x_2086_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2086_, 0, v___x_2085_);
                leanh::lean_ctor_set(v___x_2086_, 1, v___x_2081_);
                v___x_2087_ = l_Nat_reprFast(v_a_2072_);
                v___x_2088_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2088_, 0, v___x_2087_);
                v___x_2089_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2089_, 0, v___x_2086_);
                leanh::lean_ctor_set(v___x_2089_, 1, v___x_2088_);
                v___x_2090_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__5;
                v___x_2091_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2091_, 0, v___x_2089_);
                leanh::lean_ctor_set(v___x_2091_, 1, v___x_2090_);
                v___x_2092_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2092_, 0, v___x_2091_);
                leanh::lean_ctor_set(v___x_2092_, 1, v_f_2060_);
                if v_isShared_2075_ == 0 {
                    leanh::lean_ctor_set(v___x_2074_, 0, v___x_2092_);
                    v___x_2094_ = v___x_2074_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2095_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2092_);
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
                v___x_2102_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2102_, 0, v___x_2101_);
                v___x_2103_ = l_Lean_MessageData_ofFormat(v___x_2102_);
                leanh::lean_inc(v_ref_2064_);
                v___x_2104_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2104_, 0, v_ref_2064_);
                leanh::lean_ctor_set(v___x_2104_, 1, v___x_2103_);
                if v_isShared_2100_ == 0 {
                    leanh::lean_ctor_set(v___x_2099_, 0, v___x_2104_);
                    v___x_2106_ = v___x_2099_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2107_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
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
                v___x_2114_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2114_, 0, v___x_2113_);
                v___x_2115_ = l_Lean_MessageData_ofFormat(v___x_2114_);
                leanh::lean_inc(v_ref_2064_);
                v___x_2116_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2116_, 0, v_ref_2064_);
                leanh::lean_ctor_set(v___x_2116_, 1, v___x_2115_);
                if v_isShared_2112_ == 0 {
                    leanh::lean_ctor_set(v___x_2111_, 0, v___x_2116_);
                    v___x_2118_ = v___x_2111_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2119_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2116_);
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
    mut v_e_2121_: *mut leanh::LeanObject,
    mut v_f_2122_: *mut leanh::LeanObject,
    mut v_a_2123_: *mut leanh::LeanObject,
    mut v_a_2124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2125_ =
        l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(
            v_e_2121_, v_f_2122_, v_a_2123_,
        );
    leanh::lean_dec_ref(v_a_2123_);
    return v_res_2125_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes(
    mut v_e_2126_: *mut leanh::LeanObject,
    mut v_f_2127_: *mut leanh::LeanObject,
    mut v_a_2128_: *mut leanh::LeanObject,
    mut v_a_2129_: *mut leanh::LeanObject,
    mut v_a_2130_: *mut leanh::LeanObject,
    mut v_a_2131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2133_ =
        l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(
            v_e_2126_, v_f_2127_, v_a_2130_,
        );
    return v___x_2133_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___boxed(
    mut v_e_2134_: *mut leanh::LeanObject,
    mut v_f_2135_: *mut leanh::LeanObject,
    mut v_a_2136_: *mut leanh::LeanObject,
    mut v_a_2137_: *mut leanh::LeanObject,
    mut v_a_2138_: *mut leanh::LeanObject,
    mut v_a_2139_: *mut leanh::LeanObject,
    mut v_a_2140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2141_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes(
        v_e_2134_, v_f_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_,
    );
    leanh::lean_dec(v_a_2139_);
    leanh::lean_dec_ref(v_a_2138_);
    leanh::lean_dec(v_a_2137_);
    leanh::lean_dec_ref(v_a_2136_);
    return v_res_2141_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppExpr___lam__0(
    mut v_e_2142_: *mut leanh::LeanObject,
    mut v___y_2143_: *mut leanh::LeanObject,
    mut v___y_2144_: *mut leanh::LeanObject,
    mut v___y_2145_: *mut leanh::LeanObject,
    mut v___y_2146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2148_ = leanh::lean_box(1);
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
    mut v_e_2150_: *mut leanh::LeanObject,
    mut v___y_2151_: *mut leanh::LeanObject,
    mut v___y_2152_: *mut leanh::LeanObject,
    mut v___y_2153_: *mut leanh::LeanObject,
    mut v___y_2154_: *mut leanh::LeanObject,
    mut v___y_2155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2156_ = l_Lean_PrettyPrinter_ppExpr___lam__0(
        v_e_2150_,
        v___y_2151_,
        v___y_2152_,
        v___y_2153_,
        v___y_2154_,
    );
    leanh::lean_dec(v___y_2154_);
    leanh::lean_dec_ref(v___y_2153_);
    leanh::lean_dec(v___y_2152_);
    leanh::lean_dec_ref(v___y_2151_);
    return v_res_2156_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppExpr(
    mut v_e_2158_: *mut leanh::LeanObject,
    mut v_a_2159_: *mut leanh::LeanObject,
    mut v_a_2160_: *mut leanh::LeanObject,
    mut v_a_2161_: *mut leanh::LeanObject,
    mut v_a_2162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2164_ = l_Lean_PrettyPrinter_ppExpr___closed__0;
    leanh::lean_inc_ref(v_e_2158_);
    v___x_2165_ = l_Lean_PrettyPrinter_ppUsing(
        v_e_2158_,
        v___f_2164_,
        v_a_2159_,
        v_a_2160_,
        v_a_2161_,
        v_a_2162_,
    );
    if leanh::lean_obj_tag(v___x_2165_) == 0 {
        let mut v_a_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_2166_ = leanh::lean_ctor_get(v___x_2165_, 0);
        leanh::lean_inc(v_a_2166_);
        leanh::lean_dec_ref_known(v___x_2165_, 1);
        v___x_2167_ =
            l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(
                v_e_2158_, v_a_2166_, v_a_2161_,
            );
        return v___x_2167_;
    } else {
        leanh::lean_dec_ref(v_e_2158_);
        return v___x_2165_;
    }
}
pub unsafe fn l_Lean_PrettyPrinter_ppExpr___boxed(
    mut v_e_2168_: *mut leanh::LeanObject,
    mut v_a_2169_: *mut leanh::LeanObject,
    mut v_a_2170_: *mut leanh::LeanObject,
    mut v_a_2171_: *mut leanh::LeanObject,
    mut v_a_2172_: *mut leanh::LeanObject,
    mut v_a_2173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2174_ =
        l_Lean_PrettyPrinter_ppExpr(v_e_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
    leanh::lean_dec(v_a_2172_);
    leanh::lean_dec_ref(v_a_2171_);
    leanh::lean_dec(v_a_2170_);
    leanh::lean_dec_ref(v_a_2169_);
    return v_res_2174_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppExprWithInfos___lam__0(
    mut v_e_2175_: *mut leanh::LeanObject,
    mut v_optsPerPos_2176_: *mut leanh::LeanObject,
    mut v_delab_2177_: *mut leanh::LeanObject,
    mut v___y_2178_: *mut leanh::LeanObject,
    mut v___y_2179_: *mut leanh::LeanObject,
    mut v___y_2180_: *mut leanh::LeanObject,
    mut v___y_2181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2189_: u8 = 0;
    let mut v___y_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2195_: u8 = 0;
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2202_: u8 = 0;
    let mut v_a_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2206_: u8 = 0;
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2210_: u8 = 0;
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2214_: u8 = 0;
    let mut v_a_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2218_: u8 = 0;
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2222_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_2175_);
                v___x_2183_ = l_Lean_PrettyPrinter_delabCore___redArg(
                    v_e_2175_,
                    v_optsPerPos_2176_,
                    v_delab_2177_,
                    v___y_2178_,
                    v___y_2179_,
                    v___y_2180_,
                    v___y_2181_,
                );
                if leanh::lean_obj_tag(v___x_2183_) == 0 {
                    v_a_2184_ = leanh::lean_ctor_get(v___x_2183_, 0);
                    leanh::lean_inc(v_a_2184_);
                    leanh::lean_dec_ref_known(v___x_2183_, 1);
                    v_fst_2185_ = leanh::lean_ctor_get(v_a_2184_, 0);
                    v_snd_2186_ = leanh::lean_ctor_get(v_a_2184_, 1);
                    v_isSharedCheck_2214_ = (!leanh::lean_is_exclusive(v_a_2184_)) as u8;
                    if v_isSharedCheck_2214_ == 0 {
                        v___x_2188_ = v_a_2184_;
                        v_isShared_2189_ = v_isSharedCheck_2214_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2186_);
                        leanh::lean_inc(v_fst_2185_);
                        leanh::lean_dec(v_a_2184_);
                        v___x_2188_ = leanh::lean_box(0);
                        v_isShared_2189_ = v_isSharedCheck_2214_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_2175_);
                    v_a_2215_ = leanh::lean_ctor_get(v___x_2183_, 0);
                    v_isSharedCheck_2222_ = (!leanh::lean_is_exclusive(v___x_2183_)) as u8;
                    if v_isSharedCheck_2222_ == 0 {
                        v___x_2217_ = v___x_2183_;
                        v_isShared_2218_ = v_isSharedCheck_2222_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2215_);
                        leanh::lean_dec(v___x_2183_);
                        v___x_2217_ = leanh::lean_box(0);
                        v_isShared_2218_ = v_isSharedCheck_2222_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2211_ = l_Lean_PrettyPrinter_ppTerm(v_fst_2185_, v___y_2180_, v___y_2181_);
                if leanh::lean_obj_tag(v___x_2211_) == 0 {
                    v_a_2212_ = leanh::lean_ctor_get(v___x_2211_, 0);
                    leanh::lean_inc(v_a_2212_);
                    leanh::lean_dec_ref_known(v___x_2211_, 1);
                    v___x_2213_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(v_e_2175_, v_a_2212_, v___y_2180_);
                    v___y_2191_ = v___x_2213_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_e_2175_);
                    v___y_2191_ = v___x_2211_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if leanh::lean_obj_tag(v___y_2191_) == 0 {
                    v_a_2192_ = leanh::lean_ctor_get(v___y_2191_, 0);
                    v_isSharedCheck_2202_ = (!leanh::lean_is_exclusive(v___y_2191_)) as u8;
                    if v_isSharedCheck_2202_ == 0 {
                        v___x_2194_ = v___y_2191_;
                        v_isShared_2195_ = v_isSharedCheck_2202_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2192_);
                        leanh::lean_dec(v___y_2191_);
                        v___x_2194_ = leanh::lean_box(0);
                        v_isShared_2195_ = v_isSharedCheck_2202_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2188_);
                    leanh::lean_dec(v_snd_2186_);
                    v_a_2203_ = leanh::lean_ctor_get(v___y_2191_, 0);
                    v_isSharedCheck_2210_ = (!leanh::lean_is_exclusive(v___y_2191_)) as u8;
                    if v_isSharedCheck_2210_ == 0 {
                        v___x_2205_ = v___y_2191_;
                        v_isShared_2206_ = v_isSharedCheck_2210_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2203_);
                        leanh::lean_dec(v___y_2191_);
                        v___x_2205_ = leanh::lean_box(0);
                        v_isShared_2206_ = v_isSharedCheck_2210_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2189_ == 0 {
                    leanh::lean_ctor_set(v___x_2188_, 0, v_a_2192_);
                    v___x_2197_ = v___x_2188_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2201_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2192_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_snd_2186_);
                    v___x_2197_ = v_reuseFailAlloc_2201_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2195_ == 0 {
                    leanh::lean_ctor_set(v___x_2194_, 0, v___x_2197_);
                    v___x_2199_ = v___x_2194_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2200_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2197_);
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
                    v_reuseFailAlloc_2209_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2203_);
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
                    v_reuseFailAlloc_2221_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
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
    mut v_e_2223_: *mut leanh::LeanObject,
    mut v_optsPerPos_2224_: *mut leanh::LeanObject,
    mut v_delab_2225_: *mut leanh::LeanObject,
    mut v___y_2226_: *mut leanh::LeanObject,
    mut v___y_2227_: *mut leanh::LeanObject,
    mut v___y_2228_: *mut leanh::LeanObject,
    mut v___y_2229_: *mut leanh::LeanObject,
    mut v___y_2230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2231_ = l_Lean_PrettyPrinter_ppExprWithInfos___lam__0(
        v_e_2223_,
        v_optsPerPos_2224_,
        v_delab_2225_,
        v___y_2226_,
        v___y_2227_,
        v___y_2228_,
        v___y_2229_,
    );
    leanh::lean_dec(v___y_2229_);
    leanh::lean_dec_ref(v___y_2228_);
    leanh::lean_dec(v___y_2227_);
    leanh::lean_dec_ref(v___y_2226_);
    return v_res_2231_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppExprWithInfos(
    mut v_e_2232_: *mut leanh::LeanObject,
    mut v_optsPerPos_2233_: *mut leanh::LeanObject,
    mut v_delab_2234_: *mut leanh::LeanObject,
    mut v_a_2235_: *mut leanh::LeanObject,
    mut v_a_2236_: *mut leanh::LeanObject,
    mut v_a_2237_: *mut leanh::LeanObject,
    mut v_a_2238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lctx_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lctx_2240_ = leanh::lean_ctor_get(v_a_2235_, 2);
    v_options_2241_ = leanh::lean_ctor_get(v_a_2237_, 2);
    v___x_2242_ = leanh::lean_box(1);
    leanh::lean_inc_ref(v_options_2241_);
    v___x_2243_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2243_, 0, v_options_2241_);
    leanh::lean_ctor_set(v___x_2243_, 1, v___x_2242_);
    leanh::lean_ctor_set(v___x_2243_, 2, v___x_2242_);
    leanh::lean_inc_ref(v_lctx_2240_);
    v___x_2244_ = l_Lean_LocalContext_sanitizeNames(v_lctx_2240_, v___x_2243_);
    v_fst_2245_ = leanh::lean_ctor_get(v___x_2244_, 0);
    leanh::lean_inc(v_fst_2245_);
    leanh::lean_dec_ref(v___x_2244_);
    v___f_2246_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_ppExprWithInfos___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___f_2246_, 0, v_e_2232_);
    leanh::lean_closure_set(v___f_2246_, 1, v_optsPerPos_2233_);
    leanh::lean_closure_set(v___f_2246_, 2, v_delab_2234_);
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
    mut v_e_2248_: *mut leanh::LeanObject,
    mut v_optsPerPos_2249_: *mut leanh::LeanObject,
    mut v_delab_2250_: *mut leanh::LeanObject,
    mut v_a_2251_: *mut leanh::LeanObject,
    mut v_a_2252_: *mut leanh::LeanObject,
    mut v_a_2253_: *mut leanh::LeanObject,
    mut v_a_2254_: *mut leanh::LeanObject,
    mut v_a_2255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2256_ = l_Lean_PrettyPrinter_ppExprWithInfos(
        v_e_2248_,
        v_optsPerPos_2249_,
        v_delab_2250_,
        v_a_2251_,
        v_a_2252_,
        v_a_2253_,
        v_a_2254_,
    );
    leanh::lean_dec(v_a_2254_);
    leanh::lean_dec_ref(v_a_2253_);
    leanh::lean_dec(v_a_2252_);
    leanh::lean_dec_ref(v_a_2251_);
    return v_res_2256_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_PrettyPrinter_ppConstNameWithInfos_spec__0(
    mut v_a_2257_: *mut leanh::LeanObject,
    mut v_a_2258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2264_: u8 = 0;
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2270_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2257_) == 0 {
                    v___x_2259_ = l_List_reverse___redArg(v_a_2258_);
                    return v___x_2259_;
                } else {
                    v_head_2260_ = leanh::lean_ctor_get(v_a_2257_, 0);
                    v_tail_2261_ = leanh::lean_ctor_get(v_a_2257_, 1);
                    v_isSharedCheck_2270_ = (!leanh::lean_is_exclusive(v_a_2257_)) as u8;
                    if v_isSharedCheck_2270_ == 0 {
                        v___x_2263_ = v_a_2257_;
                        v_isShared_2264_ = v_isSharedCheck_2270_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2261_);
                        leanh::lean_inc(v_head_2260_);
                        leanh::lean_dec(v_a_2257_);
                        v___x_2263_ = leanh::lean_box(0);
                        v_isShared_2264_ = v_isSharedCheck_2270_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2265_ = l_Lean_mkLevelParam(v_head_2260_);
                if v_isShared_2264_ == 0 {
                    leanh::lean_ctor_set(v___x_2263_, 1, v_a_2258_);
                    leanh::lean_ctor_set(v___x_2263_, 0, v___x_2265_);
                    v___x_2267_ = v___x_2263_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2269_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2265_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_a_2258_);
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
    mut v_constName_2282_: *mut leanh::LeanObject,
    mut v_a_2283_: *mut leanh::LeanObject,
    mut v_a_2284_: *mut leanh::LeanObject,
    mut v_a_2285_: *mut leanh::LeanObject,
    mut v_a_2286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: u8 = 0;
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2308_: u8 = 0;
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2314_: u8 = 0;
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2321_: u8 = 0;
    let mut v_a_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2325_: u8 = 0;
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2329_: u8 = 0;
    let mut v_isSharedCheck_2330_: u8 = 0;
    let mut v_unused_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2288_ = lean_st_ref_get(v_a_2286_);
                v_env_2289_ = leanh::lean_ctor_get(v___x_2288_, 0);
                leanh::lean_inc_ref(v_env_2289_);
                leanh::lean_dec(v___x_2288_);
                v___x_2290_ = 0;
                leanh::lean_inc(v_constName_2282_);
                v___x_2291_ =
                    l_Lean_Environment_find_x3f(v_env_2289_, v_constName_2282_, v___x_2290_);
                if leanh::lean_obj_tag(v___x_2291_) == 1 {
                    v_val_2292_ = leanh::lean_ctor_get(v___x_2291_, 0);
                    leanh::lean_inc(v_val_2292_);
                    leanh::lean_dec_ref_known(v___x_2291_, 1);
                    v___x_2293_ = l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__4;
                    v___x_2294_ = l_Lean_ConstantInfo_levelParams(v_val_2292_);
                    leanh::lean_dec(v_val_2292_);
                    v___x_2295_ = leanh::lean_box(0);
                    v___x_2296_ =
                        l_List_mapTR_loop___at___00Lean_PrettyPrinter_ppConstNameWithInfos_spec__0(
                            v___x_2294_,
                            v___x_2295_,
                        );
                    v___x_2297_ = l_Lean_Expr_const___override(v_constName_2282_, v___x_2296_);
                    v___x_2298_ = leanh::lean_box(1);
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
                    leanh::lean_dec(v___x_2291_);
                    v_options_2300_ = leanh::lean_ctor_get(v_a_2285_, 2);
                    v___x_2301_ = lean_mk_syntax_ident(v_constName_2282_);
                    v___x_2302_ = leanh::lean_box(1);
                    leanh::lean_inc_ref(v_options_2300_);
                    v___x_2303_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2303_, 0, v_options_2300_);
                    leanh::lean_ctor_set(v___x_2303_, 1, v___x_2302_);
                    leanh::lean_ctor_set(v___x_2303_, 2, v___x_2302_);
                    v___x_2304_ = l_Lean_sanitizeSyntax(v___x_2301_, v___x_2303_);
                    v_fst_2305_ = leanh::lean_ctor_get(v___x_2304_, 0);
                    v_isSharedCheck_2330_ = (!leanh::lean_is_exclusive(v___x_2304_)) as u8;
                    if v_isSharedCheck_2330_ == 0 {
                        v_unused_2331_ = leanh::lean_ctor_get(v___x_2304_, 1);
                        leanh::lean_dec(v_unused_2331_);
                        v___x_2307_ = v___x_2304_;
                        v_isShared_2308_ = v_isSharedCheck_2330_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_2305_);
                        leanh::lean_dec(v___x_2304_);
                        v___x_2307_ = leanh::lean_box(0);
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
                if leanh::lean_obj_tag(v___x_2310_) == 0 {
                    v_a_2311_ = leanh::lean_ctor_get(v___x_2310_, 0);
                    v_isSharedCheck_2321_ = (!leanh::lean_is_exclusive(v___x_2310_)) as u8;
                    if v_isSharedCheck_2321_ == 0 {
                        v___x_2313_ = v___x_2310_;
                        v_isShared_2314_ = v_isSharedCheck_2321_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2311_);
                        leanh::lean_dec(v___x_2310_);
                        v___x_2313_ = leanh::lean_box(0);
                        v_isShared_2314_ = v_isSharedCheck_2321_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2307_);
                    v_a_2322_ = leanh::lean_ctor_get(v___x_2310_, 0);
                    v_isSharedCheck_2329_ = (!leanh::lean_is_exclusive(v___x_2310_)) as u8;
                    if v_isSharedCheck_2329_ == 0 {
                        v___x_2324_ = v___x_2310_;
                        v_isShared_2325_ = v_isSharedCheck_2329_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2322_);
                        leanh::lean_dec(v___x_2310_);
                        v___x_2324_ = leanh::lean_box(0);
                        v_isShared_2325_ = v_isSharedCheck_2329_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2308_ == 0 {
                    leanh::lean_ctor_set(v___x_2307_, 1, v___x_2302_);
                    leanh::lean_ctor_set(v___x_2307_, 0, v_a_2311_);
                    v___x_2316_ = v___x_2307_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2320_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2311_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2320_, 1, v___x_2302_);
                    v___x_2316_ = v_reuseFailAlloc_2320_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2314_ == 0 {
                    leanh::lean_ctor_set(v___x_2313_, 0, v___x_2316_);
                    v___x_2318_ = v___x_2313_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2319_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2316_);
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
                    v_reuseFailAlloc_2328_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
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
    mut v_constName_2332_: *mut leanh::LeanObject,
    mut v_a_2333_: *mut leanh::LeanObject,
    mut v_a_2334_: *mut leanh::LeanObject,
    mut v_a_2335_: *mut leanh::LeanObject,
    mut v_a_2336_: *mut leanh::LeanObject,
    mut v_a_2337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2338_ = l_Lean_PrettyPrinter_ppConstNameWithInfos(
        v_constName_2332_,
        v_a_2333_,
        v_a_2334_,
        v_a_2335_,
        v_a_2336_,
    );
    leanh::lean_dec(v_a_2336_);
    leanh::lean_dec_ref(v_a_2335_);
    leanh::lean_dec(v_a_2334_);
    leanh::lean_dec_ref(v_a_2333_);
    return v_res_2338_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_PrettyPrinter_ppExprLegacy_spec__0(
    mut v_opts_2339_: *mut leanh::LeanObject,
    mut v_opt_2340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_2341_ = leanh::lean_ctor_get(v_opt_2340_, 0);
    v_defValue_2342_ = leanh::lean_ctor_get(v_opt_2340_, 1);
    v_map_2343_ = leanh::lean_ctor_get(v_opts_2339_, 0);
    v___x_2344_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2343_,
            v_name_2341_,
        );
    if leanh::lean_obj_tag(v___x_2344_) == 0 {
        leanh::lean_inc(v_defValue_2342_);
        return v_defValue_2342_;
    } else {
        let mut v_val_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2345_ = leanh::lean_ctor_get(v___x_2344_, 0);
        leanh::lean_inc(v_val_2345_);
        leanh::lean_dec_ref_known(v___x_2344_, 1);
        if leanh::lean_obj_tag(v_val_2345_) == 3 {
            let mut v_v_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_2346_ = leanh::lean_ctor_get(v_val_2345_, 0);
            leanh::lean_inc(v_v_2346_);
            leanh::lean_dec_ref_known(v_val_2345_, 1);
            return v_v_2346_;
        } else {
            leanh::lean_dec(v_val_2345_);
            leanh::lean_inc(v_defValue_2342_);
            return v_defValue_2342_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_PrettyPrinter_ppExprLegacy_spec__0___boxed(
    mut v_opts_2347_: *mut leanh::LeanObject,
    mut v_opt_2348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2349_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_ppExprLegacy_spec__0(
        v_opts_2347_,
        v_opt_2348_,
    );
    leanh::lean_dec_ref(v_opt_2348_);
    leanh::lean_dec_ref(v_opts_2347_);
    return v_res_2349_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__1() -> u64 {
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: u64 = 0;
    v___x_2356_ = l_Lean_PrettyPrinter_ppExprLegacy___closed__0;
    v___x_2357_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2356_);
    return v___x_2357_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_2358_: u64 = 0;
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2358_ = leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__1),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__1_once),
        _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__1,
    );
    v___x_2359_ = l_Lean_PrettyPrinter_ppExprLegacy___closed__0;
    v___x_2360_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
    leanh::lean_ctor_set(v___x_2360_, 0, v___x_2359_);
    leanh::lean_ctor_set_uint64(
        v___x_2360_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2358_,
    );
    return v___x_2360_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2363_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2363_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2364_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__4),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__4_once),
        _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__4,
    );
    v___x_2365_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2365_, 0, v___x_2364_);
    return v___x_2365_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__6() -> *mut leanh::LeanObject
{
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2366_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__5),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__5_once),
        _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__5,
    );
    v___x_2367_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_2367_, 0, v___x_2366_);
    leanh::lean_ctor_set(v___x_2367_, 1, v___x_2366_);
    leanh::lean_ctor_set(v___x_2367_, 2, v___x_2366_);
    leanh::lean_ctor_set(v___x_2367_, 3, v___x_2366_);
    leanh::lean_ctor_set(v___x_2367_, 4, v___x_2366_);
    leanh::lean_ctor_set(v___x_2367_, 5, v___x_2366_);
    return v___x_2367_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__7() -> *mut leanh::LeanObject
{
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2368_ = leanh::lean_unsigned_to_nat(32);
    v___x_2369_ = lean_mk_empty_array_with_capacity(v___x_2368_);
    v___x_2370_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2370_, 0, v___x_2369_);
    return v___x_2370_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__8() -> *mut leanh::LeanObject
{
    let mut v___x_2371_: usize = 0;
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2371_ = 5usize;
    v___x_2372_ = leanh::lean_unsigned_to_nat(0);
    v___x_2373_ = leanh::lean_unsigned_to_nat(32);
    v___x_2374_ = lean_mk_empty_array_with_capacity(v___x_2373_);
    v___x_2375_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__7),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__7_once),
        _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__7,
    );
    v___x_2376_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_2376_, 0, v___x_2375_);
    leanh::lean_ctor_set(v___x_2376_, 1, v___x_2374_);
    leanh::lean_ctor_set(v___x_2376_, 2, v___x_2372_);
    leanh::lean_ctor_set(v___x_2376_, 3, v___x_2372_);
    leanh::lean_ctor_set_usize(v___x_2376_, 4, v___x_2371_);
    return v___x_2376_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__9() -> *mut leanh::LeanObject
{
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2377_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__5),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__5_once),
        _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__5,
    );
    v___x_2378_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_2378_, 0, v___x_2377_);
    leanh::lean_ctor_set(v___x_2378_, 1, v___x_2377_);
    leanh::lean_ctor_set(v___x_2378_, 2, v___x_2377_);
    leanh::lean_ctor_set(v___x_2378_, 3, v___x_2377_);
    leanh::lean_ctor_set(v___x_2378_, 4, v___x_2377_);
    return v___x_2378_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__10() -> *mut leanh::LeanObject
{
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2379_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__5),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__5_once),
        _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__5,
    );
    v___x_2380_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2380_, 0, v___x_2379_);
    leanh::lean_ctor_set(v___x_2380_, 1, v___x_2379_);
    return v___x_2380_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__11() -> *mut leanh::LeanObject
{
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2381_ = l_Lean_NameSet_empty;
    v___x_2382_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__8),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__8_once),
        _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__8,
    );
    v___x_2383_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2383_, 0, v___x_2382_);
    leanh::lean_ctor_set(v___x_2383_, 1, v___x_2382_);
    leanh::lean_ctor_set(v___x_2383_, 2, v___x_2381_);
    return v___x_2383_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__12() -> *mut leanh::LeanObject
{
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2384_ = leanh::lean_unsigned_to_nat(1);
    v___x_2385_ = l_Lean_firstFrontendMacroScope;
    v___x_2386_ = lean_nat_add(v___x_2385_, v___x_2384_);
    return v___x_2386_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__17() -> *mut leanh::LeanObject
{
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: u64 = 0;
    let mut v___x_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2397_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__8),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__8_once),
        _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__8,
    );
    v___x_2398_ = 0u64;
    v___x_2399_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
    leanh::lean_ctor_set(v___x_2399_, 0, v___x_2397_);
    leanh::lean_ctor_set_uint64(
        v___x_2399_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2398_,
    );
    return v___x_2399_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__18() -> *mut leanh::LeanObject
{
    let mut v___x_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: u8 = 0;
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2400_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__8),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__8_once),
        _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__8,
    );
    v___x_2401_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__5),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__5_once),
        _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__5,
    );
    v___x_2402_ = 1;
    v___x_2403_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
    leanh::lean_ctor_set(v___x_2403_, 0, v___x_2401_);
    leanh::lean_ctor_set(v___x_2403_, 1, v___x_2401_);
    leanh::lean_ctor_set(v___x_2403_, 2, v___x_2400_);
    leanh::lean_ctor_set_uint8(
        v___x_2403_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_2402_,
    );
    return v___x_2403_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__21() -> *mut leanh::LeanObject
{
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2406_ = l_Lean_Options_empty;
    v___x_2407_ = l_Lean_Core_getMaxHeartbeats(v___x_2406_);
    return v___x_2407_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__22() -> u8 {
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: u8 = 0;
    v___x_2408_ = l_Lean_diagnostics;
    v___x_2409_ = l_Lean_Options_empty;
    v___x_2410_ = l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(v___x_2409_, v___x_2408_);
    return v___x_2410_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__23() -> *mut leanh::LeanObject
{
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2411_ = l_Lean_maxRecDepth;
    v___x_2412_ = l_Lean_Options_empty;
    v___x_2413_ = l_Lean_Option_get___at___00Lean_PrettyPrinter_ppExprLegacy_spec__0(
        v___x_2412_,
        v___x_2411_,
    );
    return v___x_2413_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppExprLegacy(
    mut v_env_2414_: *mut leanh::LeanObject,
    mut v_mctx_2415_: *mut leanh::LeanObject,
    mut v_lctx_2416_: *mut leanh::LeanObject,
    mut v_opts_2417_: *mut leanh::LeanObject,
    mut v_e_2418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: u8 = 0;
    let mut v___x_2422_: u8 = 0;
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2446_: u8 = 0;
    let mut v___y_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2459_: u8 = 0;
    let mut v_inheritedTraceOptions_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2468_: u8 = 0;
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2474_: u8 = 0;
    let mut v_a_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2478_: u8 = 0;
    let mut v_msg_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2493_: u8 = 0;
    let mut v___y_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2496_: u8 = 0;
    let mut v___y_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2511_: u8 = 0;
    let mut v_inheritedTraceOptions_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2515_: u8 = 0;
    let mut v___y_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2519_: u8 = 0;
    let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2531_: u8 = 0;
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2537_: u8 = 0;
    let mut v_unused_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: u8 = 0;
    let mut v___y_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2569_: u8 = 0;
    let mut v_inheritedTraceOptions_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2573_: u8 = 0;
    let mut v_env_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: u8 = 0;
    let mut v___x_2580_: u8 = 0;
    let mut v_reuseFailAlloc_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2582_: u8 = 0;
    let mut v_unused_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2586_: u8 = 0;
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2598_: u8 = 0;
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2604_: u8 = 0;
    let mut v_unused_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2420_ = leanh::lean_box(1);
                v___x_2421_ = 0;
                v___x_2422_ = 1;
                v___x_2423_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__2_once),
                    _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__2,
                );
                v___x_2424_ = leanh::lean_unsigned_to_nat(0);
                v___x_2425_ = l_Lean_PrettyPrinter_ppExprLegacy___closed__3;
                v___x_2426_ = leanh::lean_box(0);
                v___x_2427_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_2427_, 0, v___x_2423_);
                leanh::lean_ctor_set(v___x_2427_, 1, v___x_2420_);
                leanh::lean_ctor_set(v___x_2427_, 2, v_lctx_2416_);
                leanh::lean_ctor_set(v___x_2427_, 3, v___x_2425_);
                leanh::lean_ctor_set(v___x_2427_, 4, v___x_2426_);
                leanh::lean_ctor_set(v___x_2427_, 5, v___x_2424_);
                leanh::lean_ctor_set(v___x_2427_, 6, v___x_2426_);
                leanh::lean_ctor_set_uint8(
                    v___x_2427_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v___x_2421_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2427_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v___x_2421_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2427_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v___x_2421_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2427_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v___x_2422_,
                );
                v___x_2428_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__6),
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__6_once),
                    _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__6,
                );
                v___x_2429_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__8),
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__8_once),
                    _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__8,
                );
                v___x_2430_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__9),
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__9_once),
                    _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__9,
                );
                v___x_2431_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__10),
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__10_once),
                    _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__10,
                );
                v___x_2432_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__11),
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__11_once),
                    _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__11,
                );
                v___x_2433_ = lean_io_get_num_heartbeats();
                v___x_2434_ = l_Lean_firstFrontendMacroScope;
                v___x_2435_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__12),
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__12_once),
                    _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__12,
                );
                v___x_2436_ = l_Lean_PrettyPrinter_ppExprLegacy___closed__15;
                v___x_2437_ = leanh::lean_box(0);
                v___x_2438_ = leanh::lean_box(0);
                v___x_2439_ = l_Lean_PrettyPrinter_ppExprLegacy___closed__16;
                v___x_2440_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__17),
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__17_once),
                    _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__17,
                );
                v___x_2441_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__18),
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__18_once),
                    _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__18,
                );
                v___x_2442_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                leanh::lean_ctor_set(v___x_2442_, 0, v_env_2414_);
                leanh::lean_ctor_set(v___x_2442_, 1, v___x_2435_);
                leanh::lean_ctor_set(v___x_2442_, 2, v___x_2436_);
                leanh::lean_ctor_set(v___x_2442_, 3, v___x_2439_);
                leanh::lean_ctor_set(v___x_2442_, 4, v___x_2440_);
                leanh::lean_ctor_set(v___x_2442_, 5, v___x_2431_);
                leanh::lean_ctor_set(v___x_2442_, 6, v___x_2432_);
                leanh::lean_ctor_set(v___x_2442_, 7, v___x_2441_);
                leanh::lean_ctor_set(v___x_2442_, 8, v___x_2425_);
                v___x_2443_ = lean_st_mk_ref(v___x_2442_);
                v___x_2539_ = l_Lean_inheritedTraceOptions;
                v___x_2540_ = lean_st_ref_get(v___x_2539_);
                v___x_2541_ = lean_st_ref_get(v___x_2443_);
                v___x_2542_ = l_Lean_PrettyPrinter_ppExprLegacy___closed__20;
                v___x_2543_ = l_Lean_instInhabitedFileMap_default;
                v___x_2544_ = l_Lean_Options_empty;
                v___x_2545_ = leanh::lean_unsigned_to_nat(1000);
                v___x_2546_ = leanh::lean_box(0);
                v___x_2547_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__21),
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__21_once),
                    _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__21,
                );
                v___x_2548_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_2548_, 0, v___x_2542_);
                leanh::lean_ctor_set(v___x_2548_, 1, v___x_2543_);
                leanh::lean_ctor_set(v___x_2548_, 2, v___x_2544_);
                leanh::lean_ctor_set(v___x_2548_, 3, v___x_2424_);
                leanh::lean_ctor_set(v___x_2548_, 4, v___x_2545_);
                leanh::lean_ctor_set(v___x_2548_, 5, v___x_2546_);
                leanh::lean_ctor_set(v___x_2548_, 6, v___x_2437_);
                leanh::lean_ctor_set(v___x_2548_, 7, v___x_2438_);
                leanh::lean_ctor_set(v___x_2548_, 8, v___x_2433_);
                leanh::lean_ctor_set(v___x_2548_, 9, v___x_2547_);
                leanh::lean_ctor_set(v___x_2548_, 10, v___x_2437_);
                leanh::lean_ctor_set(v___x_2548_, 11, v___x_2434_);
                leanh::lean_ctor_set(v___x_2548_, 12, v___x_2426_);
                leanh::lean_ctor_set(v___x_2548_, 13, v___x_2540_);
                leanh::lean_ctor_set_uint8(
                    v___x_2548_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v___x_2421_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2548_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v___x_2421_,
                );
                v_env_2549_ = leanh::lean_ctor_get(v___x_2541_, 0);
                leanh::lean_inc_ref(v_env_2549_);
                leanh::lean_dec(v___x_2541_);
                v___x_2550_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_2550_, 0, v_mctx_2415_);
                leanh::lean_ctor_set(v___x_2550_, 1, v___x_2428_);
                leanh::lean_ctor_set(v___x_2550_, 2, v___x_2420_);
                leanh::lean_ctor_set(v___x_2550_, 3, v___x_2429_);
                leanh::lean_ctor_set(v___x_2550_, 4, v___x_2430_);
                v___x_2551_ = l_Lean_diagnostics;
                v___x_2552_ = leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__22),
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__22_once),
                    _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__22,
                );
                v___x_2606_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2549_);
                leanh::lean_dec_ref(v_env_2549_);
                if v___x_2606_ == 0 {
                    if v___x_2552_ == 0 {
                        leanh::lean_inc(v___x_2443_);
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
                v___x_2463_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_2463_, 0, v_fileName_2448_);
                leanh::lean_ctor_set(v___x_2463_, 1, v_fileMap_2449_);
                leanh::lean_ctor_set(v___x_2463_, 2, v_opts_2417_);
                leanh::lean_ctor_set(v___x_2463_, 3, v_currRecDepth_2450_);
                leanh::lean_ctor_set(v___x_2463_, 4, v___x_2462_);
                leanh::lean_ctor_set(v___x_2463_, 5, v_ref_2451_);
                leanh::lean_ctor_set(v___x_2463_, 6, v_currNamespace_2452_);
                leanh::lean_ctor_set(v___x_2463_, 7, v_openDecls_2453_);
                leanh::lean_ctor_set(v___x_2463_, 8, v_initHeartbeats_2454_);
                leanh::lean_ctor_set(v___x_2463_, 9, v_maxHeartbeats_2455_);
                leanh::lean_ctor_set(v___x_2463_, 10, v_quotContext_2456_);
                leanh::lean_ctor_set(v___x_2463_, 11, v_currMacroScope_2457_);
                leanh::lean_ctor_set(v___x_2463_, 12, v_cancelTk_x3f_2458_);
                leanh::lean_ctor_set(v___x_2463_, 13, v_inheritedTraceOptions_2460_);
                leanh::lean_ctor_set_uint8(
                    v___x_2463_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v___y_2446_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2463_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_2459_,
                );
                v___x_2464_ = l_Lean_PrettyPrinter_ppExpr(
                    v_e_2418_,
                    v___x_2427_,
                    v___y_2445_,
                    v___x_2463_,
                    v___y_2461_,
                );
                leanh::lean_dec(v___y_2461_);
                leanh::lean_dec_ref_known(v___x_2463_, 14);
                leanh::lean_dec_ref_known(v___x_2427_, 7);
                if leanh::lean_obj_tag(v___x_2464_) == 0 {
                    v_a_2465_ = leanh::lean_ctor_get(v___x_2464_, 0);
                    v_isSharedCheck_2474_ = (!leanh::lean_is_exclusive(v___x_2464_)) as u8;
                    if v_isSharedCheck_2474_ == 0 {
                        v___x_2467_ = v___x_2464_;
                        v_isShared_2468_ = v_isSharedCheck_2474_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2465_);
                        leanh::lean_dec(v___x_2464_);
                        v___x_2467_ = leanh::lean_box(0);
                        v_isShared_2468_ = v_isSharedCheck_2474_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_2445_);
                    leanh::lean_dec(v___x_2443_);
                    v_a_2475_ = leanh::lean_ctor_get(v___x_2464_, 0);
                    v_isSharedCheck_2493_ = (!leanh::lean_is_exclusive(v___x_2464_)) as u8;
                    if v_isSharedCheck_2493_ == 0 {
                        v___x_2477_ = v___x_2464_;
                        v_isShared_2478_ = v_isSharedCheck_2493_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2475_);
                        leanh::lean_dec(v___x_2464_);
                        v___x_2477_ = leanh::lean_box(0);
                        v_isShared_2478_ = v_isSharedCheck_2493_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2469_ = lean_st_ref_get(v___y_2445_);
                leanh::lean_dec(v___y_2445_);
                leanh::lean_dec(v___x_2469_);
                v___x_2470_ = lean_st_ref_get(v___x_2443_);
                leanh::lean_dec(v___x_2443_);
                leanh::lean_dec(v___x_2470_);
                if v_isShared_2468_ == 0 {
                    v___x_2472_ = v___x_2467_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2473_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2465_);
                    v___x_2472_ = v_reuseFailAlloc_2473_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2472_;
            }
            4 => {
                if leanh::lean_obj_tag(v_a_2475_) == 0 {
                    v_msg_2479_ = leanh::lean_ctor_get(v_a_2475_, 1);
                    leanh::lean_inc_ref(v_msg_2479_);
                    leanh::lean_dec_ref_known(v_a_2475_, 2);
                    v___x_2480_ = l_Lean_MessageData_toString(v_msg_2479_);
                    v___x_2481_ = lean_mk_io_user_error(v___x_2480_);
                    if v_isShared_2478_ == 0 {
                        leanh::lean_ctor_set(v___x_2477_, 0, v___x_2481_);
                        v___x_2483_ = v___x_2477_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2484_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2481_);
                        v___x_2483_ = v_reuseFailAlloc_2484_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_id_2485_ = leanh::lean_ctor_get(v_a_2475_, 0);
                    leanh::lean_inc(v_id_2485_);
                    leanh::lean_dec_ref_known(v_a_2475_, 2);
                    v___x_2486_ = l_Lean_PrettyPrinter_ppExprLegacy___closed__19;
                    v___x_2487_ = l_Nat_reprFast(v_id_2485_);
                    v___x_2488_ = lean_string_append(v___x_2486_, v___x_2487_);
                    leanh::lean_dec_ref(v___x_2487_);
                    v___x_2489_ = lean_mk_io_user_error(v___x_2488_);
                    if v_isShared_2478_ == 0 {
                        leanh::lean_ctor_set(v___x_2477_, 0, v___x_2489_);
                        v___x_2491_ = v___x_2477_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2492_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2489_);
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
                v_fileName_2500_ = leanh::lean_ctor_get(v___y_2498_, 0);
                leanh::lean_inc_ref(v_fileName_2500_);
                v_fileMap_2501_ = leanh::lean_ctor_get(v___y_2498_, 1);
                leanh::lean_inc_ref(v_fileMap_2501_);
                v_currRecDepth_2502_ = leanh::lean_ctor_get(v___y_2498_, 3);
                leanh::lean_inc(v_currRecDepth_2502_);
                v_ref_2503_ = leanh::lean_ctor_get(v___y_2498_, 5);
                leanh::lean_inc(v_ref_2503_);
                v_currNamespace_2504_ = leanh::lean_ctor_get(v___y_2498_, 6);
                leanh::lean_inc(v_currNamespace_2504_);
                v_openDecls_2505_ = leanh::lean_ctor_get(v___y_2498_, 7);
                leanh::lean_inc(v_openDecls_2505_);
                v_initHeartbeats_2506_ = leanh::lean_ctor_get(v___y_2498_, 8);
                leanh::lean_inc(v_initHeartbeats_2506_);
                v_maxHeartbeats_2507_ = leanh::lean_ctor_get(v___y_2498_, 9);
                leanh::lean_inc(v_maxHeartbeats_2507_);
                v_quotContext_2508_ = leanh::lean_ctor_get(v___y_2498_, 10);
                leanh::lean_inc(v_quotContext_2508_);
                v_currMacroScope_2509_ = leanh::lean_ctor_get(v___y_2498_, 11);
                leanh::lean_inc(v_currMacroScope_2509_);
                v_cancelTk_x3f_2510_ = leanh::lean_ctor_get(v___y_2498_, 12);
                leanh::lean_inc(v_cancelTk_x3f_2510_);
                v_suppressElabErrors_2511_ = leanh::lean_ctor_get_uint8(
                    v___y_2498_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2512_ = leanh::lean_ctor_get(v___y_2498_, 13);
                leanh::lean_inc_ref(v_inheritedTraceOptions_2512_);
                leanh::lean_dec_ref(v___y_2498_);
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
                    v_env_2521_ = leanh::lean_ctor_get(v___x_2520_, 0);
                    v_nextMacroScope_2522_ = leanh::lean_ctor_get(v___x_2520_, 1);
                    v_ngen_2523_ = leanh::lean_ctor_get(v___x_2520_, 2);
                    v_auxDeclNGen_2524_ = leanh::lean_ctor_get(v___x_2520_, 3);
                    v_traceState_2525_ = leanh::lean_ctor_get(v___x_2520_, 4);
                    v_messages_2526_ = leanh::lean_ctor_get(v___x_2520_, 6);
                    v_infoState_2527_ = leanh::lean_ctor_get(v___x_2520_, 7);
                    v_snapshotTasks_2528_ = leanh::lean_ctor_get(v___x_2520_, 8);
                    v_isSharedCheck_2537_ = (!leanh::lean_is_exclusive(v___x_2520_)) as u8;
                    if v_isSharedCheck_2537_ == 0 {
                        v_unused_2538_ = leanh::lean_ctor_get(v___x_2520_, 5);
                        leanh::lean_dec(v_unused_2538_);
                        v___x_2530_ = v___x_2520_;
                        v_isShared_2531_ = v_isSharedCheck_2537_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_2528_);
                        leanh::lean_inc(v_infoState_2527_);
                        leanh::lean_inc(v_messages_2526_);
                        leanh::lean_inc(v_traceState_2525_);
                        leanh::lean_inc(v_auxDeclNGen_2524_);
                        leanh::lean_inc(v_ngen_2523_);
                        leanh::lean_inc(v_nextMacroScope_2522_);
                        leanh::lean_inc(v_env_2521_);
                        leanh::lean_dec(v___x_2520_);
                        v___x_2530_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_2530_, 5, v___x_2431_);
                    leanh::lean_ctor_set(v___x_2530_, 0, v___x_2532_);
                    v___x_2534_ = v___x_2530_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2536_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2532_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 1, v_nextMacroScope_2522_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 2, v_ngen_2523_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 3, v_auxDeclNGen_2524_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 4, v_traceState_2525_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 5, v___x_2431_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 6, v_messages_2526_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 7, v_infoState_2527_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2536_, 8, v_snapshotTasks_2528_);
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
                v_fileName_2558_ = leanh::lean_ctor_get(v___y_2554_, 0);
                v_fileMap_2559_ = leanh::lean_ctor_get(v___y_2554_, 1);
                v_currRecDepth_2560_ = leanh::lean_ctor_get(v___y_2554_, 3);
                v_ref_2561_ = leanh::lean_ctor_get(v___y_2554_, 5);
                v_currNamespace_2562_ = leanh::lean_ctor_get(v___y_2554_, 6);
                v_openDecls_2563_ = leanh::lean_ctor_get(v___y_2554_, 7);
                v_initHeartbeats_2564_ = leanh::lean_ctor_get(v___y_2554_, 8);
                v_maxHeartbeats_2565_ = leanh::lean_ctor_get(v___y_2554_, 9);
                v_quotContext_2566_ = leanh::lean_ctor_get(v___y_2554_, 10);
                v_currMacroScope_2567_ = leanh::lean_ctor_get(v___y_2554_, 11);
                v_cancelTk_x3f_2568_ = leanh::lean_ctor_get(v___y_2554_, 12);
                v_suppressElabErrors_2569_ = leanh::lean_ctor_get_uint8(
                    v___y_2554_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2570_ = leanh::lean_ctor_get(v___y_2554_, 13);
                v_isSharedCheck_2582_ = (!leanh::lean_is_exclusive(v___y_2554_)) as u8;
                if v_isSharedCheck_2582_ == 0 {
                    v_unused_2583_ = leanh::lean_ctor_get(v___y_2554_, 4);
                    leanh::lean_dec(v_unused_2583_);
                    v_unused_2584_ = leanh::lean_ctor_get(v___y_2554_, 2);
                    leanh::lean_dec(v_unused_2584_);
                    v___x_2572_ = v___y_2554_;
                    v_isShared_2573_ = v_isSharedCheck_2582_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_inc(v_inheritedTraceOptions_2570_);
                    leanh::lean_inc(v_cancelTk_x3f_2568_);
                    leanh::lean_inc(v_currMacroScope_2567_);
                    leanh::lean_inc(v_quotContext_2566_);
                    leanh::lean_inc(v_maxHeartbeats_2565_);
                    leanh::lean_inc(v_initHeartbeats_2564_);
                    leanh::lean_inc(v_openDecls_2563_);
                    leanh::lean_inc(v_currNamespace_2562_);
                    leanh::lean_inc(v_ref_2561_);
                    leanh::lean_inc(v_currRecDepth_2560_);
                    leanh::lean_inc(v_fileMap_2559_);
                    leanh::lean_inc(v_fileName_2558_);
                    leanh::lean_dec(v___y_2554_);
                    v___x_2572_ = leanh::lean_box(0);
                    v_isShared_2573_ = v_isSharedCheck_2582_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v_env_2574_ = leanh::lean_ctor_get(v___x_2557_, 0);
                leanh::lean_inc_ref(v_env_2574_);
                leanh::lean_dec(v___x_2557_);
                v___x_2575_ = l_Lean_maxRecDepth;
                v___x_2576_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__23),
                    core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_ppExprLegacy___closed__23_once),
                    _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__23,
                );
                leanh::lean_inc_ref(v_inheritedTraceOptions_2570_);
                leanh::lean_inc(v_cancelTk_x3f_2568_);
                leanh::lean_inc(v_currMacroScope_2567_);
                leanh::lean_inc(v_quotContext_2566_);
                leanh::lean_inc(v_maxHeartbeats_2565_);
                leanh::lean_inc(v_initHeartbeats_2564_);
                leanh::lean_inc(v_openDecls_2563_);
                leanh::lean_inc(v_currNamespace_2562_);
                leanh::lean_inc(v_ref_2561_);
                leanh::lean_inc(v_currRecDepth_2560_);
                leanh::lean_inc_ref(v_fileMap_2559_);
                leanh::lean_inc_ref(v_fileName_2558_);
                if v_isShared_2573_ == 0 {
                    leanh::lean_ctor_set(v___x_2572_, 4, v___x_2576_);
                    leanh::lean_ctor_set(v___x_2572_, 2, v___x_2544_);
                    v___x_2578_ = v___x_2572_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2581_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_fileName_2558_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_fileMap_2559_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 2, v___x_2544_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 3, v_currRecDepth_2560_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 4, v___x_2576_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 5, v_ref_2561_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 6, v_currNamespace_2562_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 7, v_openDecls_2563_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 8, v_initHeartbeats_2564_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 9, v_maxHeartbeats_2565_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 10, v_quotContext_2566_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 11, v_currMacroScope_2567_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2581_, 12, v_cancelTk_x3f_2568_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2581_,
                        13,
                        v_inheritedTraceOptions_2570_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2581_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_2569_,
                    );
                    v___x_2578_ = v_reuseFailAlloc_2581_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2578_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v___x_2552_,
                );
                v___x_2579_ = l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(v_opts_2417_, v___x_2551_);
                v___x_2580_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_2574_);
                leanh::lean_dec_ref(v_env_2574_);
                if v___x_2580_ == 0 {
                    if v___x_2579_ == 0 {
                        leanh::lean_dec_ref(v___x_2578_);
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
                        leanh::lean_dec_ref(v_inheritedTraceOptions_2570_);
                        leanh::lean_dec(v_cancelTk_x3f_2568_);
                        leanh::lean_dec(v_currMacroScope_2567_);
                        leanh::lean_dec(v_quotContext_2566_);
                        leanh::lean_dec(v_maxHeartbeats_2565_);
                        leanh::lean_dec(v_initHeartbeats_2564_);
                        leanh::lean_dec(v_openDecls_2563_);
                        leanh::lean_dec(v_currNamespace_2562_);
                        leanh::lean_dec(v_ref_2561_);
                        leanh::lean_dec(v_currRecDepth_2560_);
                        leanh::lean_dec_ref(v_fileMap_2559_);
                        leanh::lean_dec_ref(v_fileName_2558_);
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
                    leanh::lean_dec_ref(v_inheritedTraceOptions_2570_);
                    leanh::lean_dec(v_cancelTk_x3f_2568_);
                    leanh::lean_dec(v_currMacroScope_2567_);
                    leanh::lean_dec(v_quotContext_2566_);
                    leanh::lean_dec(v_maxHeartbeats_2565_);
                    leanh::lean_dec(v_initHeartbeats_2564_);
                    leanh::lean_dec(v_openDecls_2563_);
                    leanh::lean_dec(v_currNamespace_2562_);
                    leanh::lean_dec(v_ref_2561_);
                    leanh::lean_dec(v_currRecDepth_2560_);
                    leanh::lean_dec_ref(v_fileMap_2559_);
                    leanh::lean_dec_ref(v_fileName_2558_);
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
                    v_env_2588_ = leanh::lean_ctor_get(v___x_2587_, 0);
                    v_nextMacroScope_2589_ = leanh::lean_ctor_get(v___x_2587_, 1);
                    v_ngen_2590_ = leanh::lean_ctor_get(v___x_2587_, 2);
                    v_auxDeclNGen_2591_ = leanh::lean_ctor_get(v___x_2587_, 3);
                    v_traceState_2592_ = leanh::lean_ctor_get(v___x_2587_, 4);
                    v_messages_2593_ = leanh::lean_ctor_get(v___x_2587_, 6);
                    v_infoState_2594_ = leanh::lean_ctor_get(v___x_2587_, 7);
                    v_snapshotTasks_2595_ = leanh::lean_ctor_get(v___x_2587_, 8);
                    v_isSharedCheck_2604_ = (!leanh::lean_is_exclusive(v___x_2587_)) as u8;
                    if v_isSharedCheck_2604_ == 0 {
                        v_unused_2605_ = leanh::lean_ctor_get(v___x_2587_, 5);
                        leanh::lean_dec(v_unused_2605_);
                        v___x_2597_ = v___x_2587_;
                        v_isShared_2598_ = v_isSharedCheck_2604_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_2595_);
                        leanh::lean_inc(v_infoState_2594_);
                        leanh::lean_inc(v_messages_2593_);
                        leanh::lean_inc(v_traceState_2592_);
                        leanh::lean_inc(v_auxDeclNGen_2591_);
                        leanh::lean_inc(v_ngen_2590_);
                        leanh::lean_inc(v_nextMacroScope_2589_);
                        leanh::lean_inc(v_env_2588_);
                        leanh::lean_dec(v___x_2587_);
                        v___x_2597_ = leanh::lean_box(0);
                        v_isShared_2598_ = v_isSharedCheck_2604_;
                        state = 15;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v___x_2443_);
                    v___y_2554_ = v___x_2548_;
                    v___y_2555_ = v___x_2443_;
                    state = 11;
                    continue;
                }
            }
            15 => {
                v___x_2599_ = l_Lean_Kernel_enableDiag(v_env_2588_, v___x_2552_);
                if v_isShared_2598_ == 0 {
                    leanh::lean_ctor_set(v___x_2597_, 5, v___x_2431_);
                    leanh::lean_ctor_set(v___x_2597_, 0, v___x_2599_);
                    v___x_2601_ = v___x_2597_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2603_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2599_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2603_, 1, v_nextMacroScope_2589_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2603_, 2, v_ngen_2590_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2603_, 3, v_auxDeclNGen_2591_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2603_, 4, v_traceState_2592_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2603_, 5, v___x_2431_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2603_, 6, v_messages_2593_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2603_, 7, v_infoState_2594_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2603_, 8, v_snapshotTasks_2595_);
                    v___x_2601_ = v_reuseFailAlloc_2603_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_2602_ = lean_st_ref_set(v___x_2443_, v___x_2601_);
                leanh::lean_inc(v___x_2443_);
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
    mut v_env_2607_: *mut leanh::LeanObject,
    mut v_mctx_2608_: *mut leanh::LeanObject,
    mut v_lctx_2609_: *mut leanh::LeanObject,
    mut v_opts_2610_: *mut leanh::LeanObject,
    mut v_e_2611_: *mut leanh::LeanObject,
    mut v_a_2612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_l_2617_: *mut leanh::LeanObject,
    mut v_a_2618_: *mut leanh::LeanObject,
    mut v_a_2619_: *mut leanh::LeanObject,
    mut v_a_2620_: *mut leanh::LeanObject,
    mut v_a_2621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2631_: u8 = 0;
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2635_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2623_ = leanh::lean_unsigned_to_nat(0);
                v___x_2624_ = l_Lean_PrettyPrinter_delabLevel(
                    v_l_2617_,
                    v___x_2623_,
                    v_a_2618_,
                    v_a_2619_,
                    v_a_2620_,
                    v_a_2621_,
                );
                if leanh::lean_obj_tag(v___x_2624_) == 0 {
                    v_a_2625_ = leanh::lean_ctor_get(v___x_2624_, 0);
                    leanh::lean_inc(v_a_2625_);
                    leanh::lean_dec_ref_known(v___x_2624_, 1);
                    v___x_2626_ = l_Lean_PrettyPrinter_ppLevel___closed__1;
                    v___x_2627_ = l_Lean_PrettyPrinter_ppCategory(
                        v___x_2626_,
                        v_a_2625_,
                        v_a_2620_,
                        v_a_2621_,
                    );
                    return v___x_2627_;
                } else {
                    v_a_2628_ = leanh::lean_ctor_get(v___x_2624_, 0);
                    v_isSharedCheck_2635_ = (!leanh::lean_is_exclusive(v___x_2624_)) as u8;
                    if v_isSharedCheck_2635_ == 0 {
                        v___x_2630_ = v___x_2624_;
                        v_isShared_2631_ = v_isSharedCheck_2635_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2628_);
                        leanh::lean_dec(v___x_2624_);
                        v___x_2630_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2634_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
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
    mut v_l_2636_: *mut leanh::LeanObject,
    mut v_a_2637_: *mut leanh::LeanObject,
    mut v_a_2638_: *mut leanh::LeanObject,
    mut v_a_2639_: *mut leanh::LeanObject,
    mut v_a_2640_: *mut leanh::LeanObject,
    mut v_a_2641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2642_ =
        l_Lean_PrettyPrinter_ppLevel(v_l_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_);
    leanh::lean_dec(v_a_2640_);
    leanh::lean_dec_ref(v_a_2639_);
    leanh::lean_dec(v_a_2638_);
    leanh::lean_dec_ref(v_a_2637_);
    return v_res_2642_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppTactic(
    mut v_stx_2646_: *mut leanh::LeanObject,
    mut v_a_2647_: *mut leanh::LeanObject,
    mut v_a_2648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2650_ = l_Lean_PrettyPrinter_ppTactic___closed__1;
    v___x_2651_ = l_Lean_PrettyPrinter_ppCategory(v___x_2650_, v_stx_2646_, v_a_2647_, v_a_2648_);
    return v___x_2651_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppTactic___boxed(
    mut v_stx_2652_: *mut leanh::LeanObject,
    mut v_a_2653_: *mut leanh::LeanObject,
    mut v_a_2654_: *mut leanh::LeanObject,
    mut v_a_2655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2656_ = l_Lean_PrettyPrinter_ppTactic(v_stx_2652_, v_a_2653_, v_a_2654_);
    leanh::lean_dec(v_a_2654_);
    leanh::lean_dec_ref(v_a_2653_);
    return v_res_2656_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppCommand(
    mut v_stx_2660_: *mut leanh::LeanObject,
    mut v_a_2661_: *mut leanh::LeanObject,
    mut v_a_2662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2664_ = l_Lean_PrettyPrinter_ppCommand___closed__1;
    v___x_2665_ = l_Lean_PrettyPrinter_ppCategory(v___x_2664_, v_stx_2660_, v_a_2661_, v_a_2662_);
    return v___x_2665_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppCommand___boxed(
    mut v_stx_2666_: *mut leanh::LeanObject,
    mut v_a_2667_: *mut leanh::LeanObject,
    mut v_a_2668_: *mut leanh::LeanObject,
    mut v_a_2669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2670_ = l_Lean_PrettyPrinter_ppCommand(v_stx_2666_, v_a_2667_, v_a_2668_);
    leanh::lean_dec(v_a_2668_);
    leanh::lean_dec_ref(v_a_2667_);
    return v_res_2670_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppModule(
    mut v_stx_2673_: *mut leanh::LeanObject,
    mut v_a_2674_: *mut leanh::LeanObject,
    mut v_a_2675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2685_: u8 = 0;
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_2678_) == 0 {
                    v_a_2679_ = leanh::lean_ctor_get(v___x_2678_, 0);
                    leanh::lean_inc(v_a_2679_);
                    leanh::lean_dec_ref_known(v___x_2678_, 1);
                    v___x_2680_ = l_Lean_PrettyPrinter_ppModule___closed__1;
                    v___x_2681_ =
                        l_Lean_PrettyPrinter_format(v___x_2680_, v_a_2679_, v_a_2674_, v_a_2675_);
                    return v___x_2681_;
                } else {
                    v_a_2682_ = leanh::lean_ctor_get(v___x_2678_, 0);
                    v_isSharedCheck_2689_ = (!leanh::lean_is_exclusive(v___x_2678_)) as u8;
                    if v_isSharedCheck_2689_ == 0 {
                        v___x_2684_ = v___x_2678_;
                        v_isShared_2685_ = v_isSharedCheck_2689_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2682_);
                        leanh::lean_dec(v___x_2678_);
                        v___x_2684_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2688_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_a_2682_);
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
    mut v_stx_2690_: *mut leanh::LeanObject,
    mut v_a_2691_: *mut leanh::LeanObject,
    mut v_a_2692_: *mut leanh::LeanObject,
    mut v_a_2693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2694_ = l_Lean_PrettyPrinter_ppModule(v_stx_2690_, v_a_2691_, v_a_2692_);
    leanh::lean_dec(v_a_2692_);
    leanh::lean_dec_ref(v_a_2691_);
    return v_res_2694_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2695_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2695_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2696_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
    v___x_2697_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2697_, 0, v___x_2696_);
    return v___x_2697_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2698_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_2699_ = leanh::lean_unsigned_to_nat(0);
    v___x_2700_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_2700_, 0, v___x_2699_);
    leanh::lean_ctor_set(v___x_2700_, 1, v___x_2699_);
    leanh::lean_ctor_set(v___x_2700_, 2, v___x_2699_);
    leanh::lean_ctor_set(v___x_2700_, 3, v___x_2699_);
    leanh::lean_ctor_set(v___x_2700_, 4, v___x_2698_);
    leanh::lean_ctor_set(v___x_2700_, 5, v___x_2698_);
    leanh::lean_ctor_set(v___x_2700_, 6, v___x_2698_);
    leanh::lean_ctor_set(v___x_2700_, 7, v___x_2698_);
    leanh::lean_ctor_set(v___x_2700_, 8, v___x_2698_);
    leanh::lean_ctor_set(v___x_2700_, 9, v___x_2698_);
    return v___x_2700_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2701_ = leanh::lean_unsigned_to_nat(32);
    v___x_2702_ = lean_mk_empty_array_with_capacity(v___x_2701_);
    v___x_2703_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2703_, 0, v___x_2702_);
    return v___x_2703_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2704_: usize = 0;
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2704_ = 5usize;
    v___x_2705_ = leanh::lean_unsigned_to_nat(0);
    v___x_2706_ = leanh::lean_unsigned_to_nat(32);
    v___x_2707_ = lean_mk_empty_array_with_capacity(v___x_2706_);
    v___x_2708_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
    v___x_2709_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_2709_, 0, v___x_2708_);
    leanh::lean_ctor_set(v___x_2709_, 1, v___x_2707_);
    leanh::lean_ctor_set(v___x_2709_, 2, v___x_2705_);
    leanh::lean_ctor_set(v___x_2709_, 3, v___x_2705_);
    leanh::lean_ctor_set_usize(v___x_2709_, 4, v___x_2704_);
    return v___x_2709_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2710_ = leanh::lean_box(1);
    v___x_2711_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
    v___x_2712_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_2713_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2713_, 0, v___x_2712_);
    leanh::lean_ctor_set(v___x_2713_, 1, v___x_2711_);
    leanh::lean_ctor_set(v___x_2713_, 2, v___x_2710_);
    return v___x_2713_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2715_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6;
    v___x_2716_ = l_Lean_stringToMessageData(v___x_2715_);
    return v___x_2716_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2718_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8;
    v___x_2719_ = l_Lean_stringToMessageData(v___x_2718_);
    return v___x_2719_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2721_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10;
    v___x_2722_ = l_Lean_stringToMessageData(v___x_2721_);
    return v___x_2722_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2724_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12;
    v___x_2725_ = l_Lean_stringToMessageData(v___x_2724_);
    return v___x_2725_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2727_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14;
    v___x_2728_ = l_Lean_stringToMessageData(v___x_2727_);
    return v___x_2728_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2730_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16;
    v___x_2731_ = l_Lean_stringToMessageData(v___x_2730_);
    return v___x_2731_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2733_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18;
    v___x_2734_ = l_Lean_stringToMessageData(v___x_2733_);
    return v___x_2734_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_msg_2735_: *mut leanh::LeanObject,
    mut v_declHint_2736_: *mut leanh::LeanObject,
    mut v___y_2737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: u8 = 0;
    let mut v_isExporting_2742_: u8 = 0;
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: u8 = 0;
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2764_: u8 = 0;
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: u8 = 0;
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2796_: u8 = 0;
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2739_ = lean_st_ref_get(v___y_2737_);
                v_env_2740_ = leanh::lean_ctor_get(v___x_2739_, 0);
                leanh::lean_inc_ref(v_env_2740_);
                leanh::lean_dec(v___x_2739_);
                v___x_2741_ = l_Lean_Name_isAnonymous(v_declHint_2736_);
                if v___x_2741_ == 0 {
                    v_isExporting_2742_ = leanh::lean_ctor_get_uint8(
                        v_env_2740_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_2742_ == 0 {
                        leanh::lean_dec_ref(v_env_2740_);
                        leanh::lean_dec(v_declHint_2736_);
                        v___x_2743_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2743_, 0, v_msg_2735_);
                        return v___x_2743_;
                    } else {
                        leanh::lean_inc_ref(v_env_2740_);
                        v___x_2744_ = l_Lean_Environment_setExporting(v_env_2740_, v___x_2741_);
                        leanh::lean_inc(v_declHint_2736_);
                        leanh::lean_inc_ref(v___x_2744_);
                        v___x_2745_ = l_Lean_Environment_contains(
                            v___x_2744_,
                            v_declHint_2736_,
                            v_isExporting_2742_,
                        );
                        if v___x_2745_ == 0 {
                            leanh::lean_dec_ref(v___x_2744_);
                            leanh::lean_dec_ref(v_env_2740_);
                            leanh::lean_dec(v_declHint_2736_);
                            v___x_2746_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2746_, 0, v_msg_2735_);
                            return v___x_2746_;
                        } else {
                            v___x_2747_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
                            v___x_2748_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                            v___x_2749_ = l_Lean_Options_empty;
                            v___x_2750_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_2750_, 0, v___x_2744_);
                            leanh::lean_ctor_set(v___x_2750_, 1, v___x_2747_);
                            leanh::lean_ctor_set(v___x_2750_, 2, v___x_2748_);
                            leanh::lean_ctor_set(v___x_2750_, 3, v___x_2749_);
                            leanh::lean_inc(v_declHint_2736_);
                            v___x_2751_ =
                                l_Lean_MessageData_ofConstName(v_declHint_2736_, v___x_2741_);
                            v_c_2752_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_2752_, 0, v___x_2750_);
                            leanh::lean_ctor_set(v_c_2752_, 1, v___x_2751_);
                            v___x_2753_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_2740_,
                                v_declHint_2736_,
                            );
                            if leanh::lean_obj_tag(v___x_2753_) == 0 {
                                leanh::lean_dec_ref(v_env_2740_);
                                leanh::lean_dec(v_declHint_2736_);
                                v___x_2754_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                                v___x_2755_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2755_, 0, v___x_2754_);
                                leanh::lean_ctor_set(v___x_2755_, 1, v_c_2752_);
                                v___x_2756_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
                                v___x_2757_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2757_, 0, v___x_2755_);
                                leanh::lean_ctor_set(v___x_2757_, 1, v___x_2756_);
                                v___x_2758_ = l_Lean_MessageData_note(v___x_2757_);
                                v___x_2759_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2759_, 0, v_msg_2735_);
                                leanh::lean_ctor_set(v___x_2759_, 1, v___x_2758_);
                                v___x_2760_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_2760_, 0, v___x_2759_);
                                return v___x_2760_;
                            } else {
                                v_val_2761_ = leanh::lean_ctor_get(v___x_2753_, 0);
                                v_isSharedCheck_2796_ =
                                    (!leanh::lean_is_exclusive(v___x_2753_)) as u8;
                                if v_isSharedCheck_2796_ == 0 {
                                    v___x_2763_ = v___x_2753_;
                                    v_isShared_2764_ = v_isSharedCheck_2796_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_2761_);
                                    leanh::lean_dec(v___x_2753_);
                                    v___x_2763_ = leanh::lean_box(0);
                                    v_isShared_2764_ = v_isSharedCheck_2796_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_2740_);
                    leanh::lean_dec(v_declHint_2736_);
                    v___x_2797_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2797_, 0, v_msg_2735_);
                    return v___x_2797_;
                }
            }
            1 => {
                v___x_2765_ = leanh::lean_box(0);
                v___x_2766_ = l_Lean_Environment_header(v_env_2740_);
                leanh::lean_dec_ref(v_env_2740_);
                v___x_2767_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2766_);
                v_mod_2768_ = lean_array_get(v___x_2765_, v___x_2767_, v_val_2761_);
                leanh::lean_dec(v_val_2761_);
                leanh::lean_dec_ref(v___x_2767_);
                v___x_2769_ = l_Lean_isPrivateName(v_declHint_2736_);
                leanh::lean_dec(v_declHint_2736_);
                if v___x_2769_ == 0 {
                    v___x_2770_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
                    v___x_2771_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2771_, 0, v___x_2770_);
                    leanh::lean_ctor_set(v___x_2771_, 1, v_c_2752_);
                    v___x_2772_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
                    v___x_2773_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2773_, 0, v___x_2771_);
                    leanh::lean_ctor_set(v___x_2773_, 1, v___x_2772_);
                    v___x_2774_ = l_Lean_MessageData_ofName(v_mod_2768_);
                    v___x_2775_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2775_, 0, v___x_2773_);
                    leanh::lean_ctor_set(v___x_2775_, 1, v___x_2774_);
                    v___x_2776_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
                    v___x_2777_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2777_, 0, v___x_2775_);
                    leanh::lean_ctor_set(v___x_2777_, 1, v___x_2776_);
                    v___x_2778_ = l_Lean_MessageData_note(v___x_2777_);
                    v___x_2779_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2779_, 0, v_msg_2735_);
                    leanh::lean_ctor_set(v___x_2779_, 1, v___x_2778_);
                    if v_isShared_2764_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2763_, 0);
                        leanh::lean_ctor_set(v___x_2763_, 0, v___x_2779_);
                        v___x_2781_ = v___x_2763_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2782_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2779_);
                        v___x_2781_ = v_reuseFailAlloc_2782_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2783_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                    v___x_2784_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2784_, 0, v___x_2783_);
                    leanh::lean_ctor_set(v___x_2784_, 1, v_c_2752_);
                    v___x_2785_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
                    v___x_2786_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2786_, 0, v___x_2784_);
                    leanh::lean_ctor_set(v___x_2786_, 1, v___x_2785_);
                    v___x_2787_ = l_Lean_MessageData_ofName(v_mod_2768_);
                    v___x_2788_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2788_, 0, v___x_2786_);
                    leanh::lean_ctor_set(v___x_2788_, 1, v___x_2787_);
                    v___x_2789_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
                    v___x_2790_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2790_, 0, v___x_2788_);
                    leanh::lean_ctor_set(v___x_2790_, 1, v___x_2789_);
                    v___x_2791_ = l_Lean_MessageData_note(v___x_2790_);
                    v___x_2792_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2792_, 0, v_msg_2735_);
                    leanh::lean_ctor_set(v___x_2792_, 1, v___x_2791_);
                    if v_isShared_2764_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2763_, 0);
                        leanh::lean_ctor_set(v___x_2763_, 0, v___x_2792_);
                        v___x_2794_ = v___x_2763_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2795_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2792_);
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
    mut v_msg_2798_: *mut leanh::LeanObject,
    mut v_declHint_2799_: *mut leanh::LeanObject,
    mut v___y_2800_: *mut leanh::LeanObject,
    mut v___y_2801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2802_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2798_, v_declHint_2799_, v___y_2800_);
    leanh::lean_dec(v___y_2800_);
    return v_res_2802_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_msg_2803_: *mut leanh::LeanObject,
    mut v_declHint_2804_: *mut leanh::LeanObject,
    mut v___y_2805_: *mut leanh::LeanObject,
    mut v___y_2806_: *mut leanh::LeanObject,
    mut v___y_2807_: *mut leanh::LeanObject,
    mut v___y_2808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2814_: u8 = 0;
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2820_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2810_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_2803_, v_declHint_2804_, v___y_2808_);
                v_a_2811_ = leanh::lean_ctor_get(v___x_2810_, 0);
                v_isSharedCheck_2820_ = (!leanh::lean_is_exclusive(v___x_2810_)) as u8;
                if v_isSharedCheck_2820_ == 0 {
                    v___x_2813_ = v___x_2810_;
                    v_isShared_2814_ = v_isSharedCheck_2820_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2811_);
                    leanh::lean_dec(v___x_2810_);
                    v___x_2813_ = leanh::lean_box(0);
                    v_isShared_2814_ = v_isSharedCheck_2820_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2815_ = l_Lean_unknownIdentifierMessageTag;
                v___x_2816_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2816_, 0, v___x_2815_);
                leanh::lean_ctor_set(v___x_2816_, 1, v_a_2811_);
                if v_isShared_2814_ == 0 {
                    leanh::lean_ctor_set(v___x_2813_, 0, v___x_2816_);
                    v___x_2818_ = v___x_2813_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2819_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2819_, 0, v___x_2816_);
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
    mut v_msg_2821_: *mut leanh::LeanObject,
    mut v_declHint_2822_: *mut leanh::LeanObject,
    mut v___y_2823_: *mut leanh::LeanObject,
    mut v___y_2824_: *mut leanh::LeanObject,
    mut v___y_2825_: *mut leanh::LeanObject,
    mut v___y_2826_: *mut leanh::LeanObject,
    mut v___y_2827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2828_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2821_, v_declHint_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
    leanh::lean_dec(v___y_2826_);
    leanh::lean_dec_ref(v___y_2825_);
    leanh::lean_dec(v___y_2824_);
    leanh::lean_dec_ref(v___y_2823_);
    return v_res_2828_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(
    mut v_msgData_2829_: *mut leanh::LeanObject,
    mut v___y_2830_: *mut leanh::LeanObject,
    mut v___y_2831_: *mut leanh::LeanObject,
    mut v___y_2832_: *mut leanh::LeanObject,
    mut v___y_2833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2835_ = lean_st_ref_get(v___y_2833_);
    v_env_2836_ = leanh::lean_ctor_get(v___x_2835_, 0);
    leanh::lean_inc_ref(v_env_2836_);
    leanh::lean_dec(v___x_2835_);
    v___x_2837_ = lean_st_ref_get(v___y_2831_);
    v_mctx_2838_ = leanh::lean_ctor_get(v___x_2837_, 0);
    leanh::lean_inc_ref(v_mctx_2838_);
    leanh::lean_dec(v___x_2837_);
    v_lctx_2839_ = leanh::lean_ctor_get(v___y_2830_, 2);
    v_options_2840_ = leanh::lean_ctor_get(v___y_2832_, 2);
    leanh::lean_inc_ref(v_options_2840_);
    leanh::lean_inc_ref(v_lctx_2839_);
    v___x_2841_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2841_, 0, v_env_2836_);
    leanh::lean_ctor_set(v___x_2841_, 1, v_mctx_2838_);
    leanh::lean_ctor_set(v___x_2841_, 2, v_lctx_2839_);
    leanh::lean_ctor_set(v___x_2841_, 3, v_options_2840_);
    v___x_2842_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2842_, 0, v___x_2841_);
    leanh::lean_ctor_set(v___x_2842_, 1, v_msgData_2829_);
    v___x_2843_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2843_, 0, v___x_2842_);
    return v___x_2843_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(
    mut v_msgData_2844_: *mut leanh::LeanObject,
    mut v___y_2845_: *mut leanh::LeanObject,
    mut v___y_2846_: *mut leanh::LeanObject,
    mut v___y_2847_: *mut leanh::LeanObject,
    mut v___y_2848_: *mut leanh::LeanObject,
    mut v___y_2849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2850_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
    leanh::lean_dec(v___y_2848_);
    leanh::lean_dec_ref(v___y_2847_);
    leanh::lean_dec(v___y_2846_);
    leanh::lean_dec_ref(v___y_2845_);
    return v_res_2850_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_msg_2851_: *mut leanh::LeanObject,
    mut v___y_2852_: *mut leanh::LeanObject,
    mut v___y_2853_: *mut leanh::LeanObject,
    mut v___y_2854_: *mut leanh::LeanObject,
    mut v___y_2855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2862_: u8 = 0;
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2857_ = leanh::lean_ctor_get(v___y_2854_, 5);
                v___x_2858_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
                v_a_2859_ = leanh::lean_ctor_get(v___x_2858_, 0);
                v_isSharedCheck_2867_ = (!leanh::lean_is_exclusive(v___x_2858_)) as u8;
                if v_isSharedCheck_2867_ == 0 {
                    v___x_2861_ = v___x_2858_;
                    v_isShared_2862_ = v_isSharedCheck_2867_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2859_);
                    leanh::lean_dec(v___x_2858_);
                    v___x_2861_ = leanh::lean_box(0);
                    v_isShared_2862_ = v_isSharedCheck_2867_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2857_);
                v___x_2863_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2863_, 0, v_ref_2857_);
                leanh::lean_ctor_set(v___x_2863_, 1, v_a_2859_);
                if v_isShared_2862_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2861_, 1);
                    leanh::lean_ctor_set(v___x_2861_, 0, v___x_2863_);
                    v___x_2865_ = v___x_2861_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2866_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2866_, 0, v___x_2863_);
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
    mut v_msg_2868_: *mut leanh::LeanObject,
    mut v___y_2869_: *mut leanh::LeanObject,
    mut v___y_2870_: *mut leanh::LeanObject,
    mut v___y_2871_: *mut leanh::LeanObject,
    mut v___y_2872_: *mut leanh::LeanObject,
    mut v___y_2873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2874_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
    leanh::lean_dec(v___y_2872_);
    leanh::lean_dec_ref(v___y_2871_);
    leanh::lean_dec(v___y_2870_);
    leanh::lean_dec_ref(v___y_2869_);
    return v_res_2874_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_ref_2875_: *mut leanh::LeanObject,
    mut v_msg_2876_: *mut leanh::LeanObject,
    mut v___y_2877_: *mut leanh::LeanObject,
    mut v___y_2878_: *mut leanh::LeanObject,
    mut v___y_2879_: *mut leanh::LeanObject,
    mut v___y_2880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2894_: u8 = 0;
    let mut v_cancelTk_x3f_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2896_: u8 = 0;
    let mut v_inheritedTraceOptions_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_2882_ = leanh::lean_ctor_get(v___y_2879_, 0);
    v_fileMap_2883_ = leanh::lean_ctor_get(v___y_2879_, 1);
    v_options_2884_ = leanh::lean_ctor_get(v___y_2879_, 2);
    v_currRecDepth_2885_ = leanh::lean_ctor_get(v___y_2879_, 3);
    v_maxRecDepth_2886_ = leanh::lean_ctor_get(v___y_2879_, 4);
    v_ref_2887_ = leanh::lean_ctor_get(v___y_2879_, 5);
    v_currNamespace_2888_ = leanh::lean_ctor_get(v___y_2879_, 6);
    v_openDecls_2889_ = leanh::lean_ctor_get(v___y_2879_, 7);
    v_initHeartbeats_2890_ = leanh::lean_ctor_get(v___y_2879_, 8);
    v_maxHeartbeats_2891_ = leanh::lean_ctor_get(v___y_2879_, 9);
    v_quotContext_2892_ = leanh::lean_ctor_get(v___y_2879_, 10);
    v_currMacroScope_2893_ = leanh::lean_ctor_get(v___y_2879_, 11);
    v_diag_2894_ = leanh::lean_ctor_get_uint8(
        v___y_2879_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2895_ = leanh::lean_ctor_get(v___y_2879_, 12);
    v_suppressElabErrors_2896_ = leanh::lean_ctor_get_uint8(
        v___y_2879_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_2897_ = leanh::lean_ctor_get(v___y_2879_, 13);
    v_ref_2898_ = l_Lean_replaceRef(v_ref_2875_, v_ref_2887_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_2897_);
    leanh::lean_inc(v_cancelTk_x3f_2895_);
    leanh::lean_inc(v_currMacroScope_2893_);
    leanh::lean_inc(v_quotContext_2892_);
    leanh::lean_inc(v_maxHeartbeats_2891_);
    leanh::lean_inc(v_initHeartbeats_2890_);
    leanh::lean_inc(v_openDecls_2889_);
    leanh::lean_inc(v_currNamespace_2888_);
    leanh::lean_inc(v_maxRecDepth_2886_);
    leanh::lean_inc(v_currRecDepth_2885_);
    leanh::lean_inc_ref(v_options_2884_);
    leanh::lean_inc_ref(v_fileMap_2883_);
    leanh::lean_inc_ref(v_fileName_2882_);
    v___x_2899_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_2899_, 0, v_fileName_2882_);
    leanh::lean_ctor_set(v___x_2899_, 1, v_fileMap_2883_);
    leanh::lean_ctor_set(v___x_2899_, 2, v_options_2884_);
    leanh::lean_ctor_set(v___x_2899_, 3, v_currRecDepth_2885_);
    leanh::lean_ctor_set(v___x_2899_, 4, v_maxRecDepth_2886_);
    leanh::lean_ctor_set(v___x_2899_, 5, v_ref_2898_);
    leanh::lean_ctor_set(v___x_2899_, 6, v_currNamespace_2888_);
    leanh::lean_ctor_set(v___x_2899_, 7, v_openDecls_2889_);
    leanh::lean_ctor_set(v___x_2899_, 8, v_initHeartbeats_2890_);
    leanh::lean_ctor_set(v___x_2899_, 9, v_maxHeartbeats_2891_);
    leanh::lean_ctor_set(v___x_2899_, 10, v_quotContext_2892_);
    leanh::lean_ctor_set(v___x_2899_, 11, v_currMacroScope_2893_);
    leanh::lean_ctor_set(v___x_2899_, 12, v_cancelTk_x3f_2895_);
    leanh::lean_ctor_set(v___x_2899_, 13, v_inheritedTraceOptions_2897_);
    leanh::lean_ctor_set_uint8(
        v___x_2899_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_2894_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_2899_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_2896_,
    );
    v___x_2900_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2876_, v___y_2877_, v___y_2878_, v___x_2899_, v___y_2880_);
    leanh::lean_dec_ref_known(v___x_2899_, 14);
    return v___x_2900_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_ref_2901_: *mut leanh::LeanObject,
    mut v_msg_2902_: *mut leanh::LeanObject,
    mut v___y_2903_: *mut leanh::LeanObject,
    mut v___y_2904_: *mut leanh::LeanObject,
    mut v___y_2905_: *mut leanh::LeanObject,
    mut v___y_2906_: *mut leanh::LeanObject,
    mut v___y_2907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2908_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2901_, v_msg_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
    leanh::lean_dec(v___y_2906_);
    leanh::lean_dec_ref(v___y_2905_);
    leanh::lean_dec(v___y_2904_);
    leanh::lean_dec_ref(v___y_2903_);
    leanh::lean_dec(v_ref_2901_);
    return v_res_2908_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_2909_: *mut leanh::LeanObject,
    mut v_msg_2910_: *mut leanh::LeanObject,
    mut v_declHint_2911_: *mut leanh::LeanObject,
    mut v___y_2912_: *mut leanh::LeanObject,
    mut v___y_2913_: *mut leanh::LeanObject,
    mut v___y_2914_: *mut leanh::LeanObject,
    mut v___y_2915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2917_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_2910_, v_declHint_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
    v_a_2918_ = leanh::lean_ctor_get(v___x_2917_, 0);
    leanh::lean_inc(v_a_2918_);
    leanh::lean_dec_ref(v___x_2917_);
    v___x_2919_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_2909_, v_a_2918_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
    return v___x_2919_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_2920_: *mut leanh::LeanObject,
    mut v_msg_2921_: *mut leanh::LeanObject,
    mut v_declHint_2922_: *mut leanh::LeanObject,
    mut v___y_2923_: *mut leanh::LeanObject,
    mut v___y_2924_: *mut leanh::LeanObject,
    mut v___y_2925_: *mut leanh::LeanObject,
    mut v___y_2926_: *mut leanh::LeanObject,
    mut v___y_2927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2928_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2920_, v_msg_2921_, v_declHint_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
    leanh::lean_dec(v___y_2926_);
    leanh::lean_dec_ref(v___y_2925_);
    leanh::lean_dec(v___y_2924_);
    leanh::lean_dec_ref(v___y_2923_);
    leanh::lean_dec(v_ref_2920_);
    return v_res_2928_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2930_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_2931_ = l_Lean_stringToMessageData(v___x_2930_);
    return v___x_2931_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2933_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_2934_ = l_Lean_stringToMessageData(v___x_2933_);
    return v___x_2934_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg(
    mut v_ref_2935_: *mut leanh::LeanObject,
    mut v_constName_2936_: *mut leanh::LeanObject,
    mut v___y_2937_: *mut leanh::LeanObject,
    mut v___y_2938_: *mut leanh::LeanObject,
    mut v___y_2939_: *mut leanh::LeanObject,
    mut v___y_2940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: u8 = 0;
    let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2942_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_2943_ = 0;
    leanh::lean_inc(v_constName_2936_);
    v___x_2944_ = l_Lean_MessageData_ofConstName(v_constName_2936_, v___x_2943_);
    v___x_2945_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2945_, 0, v___x_2942_);
    leanh::lean_ctor_set(v___x_2945_, 1, v___x_2944_);
    v___x_2946_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_2947_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2947_, 0, v___x_2945_);
    leanh::lean_ctor_set(v___x_2947_, 1, v___x_2946_);
    v___x_2948_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_2935_, v___x_2947_, v_constName_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
    return v___x_2948_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_2949_: *mut leanh::LeanObject,
    mut v_constName_2950_: *mut leanh::LeanObject,
    mut v___y_2951_: *mut leanh::LeanObject,
    mut v___y_2952_: *mut leanh::LeanObject,
    mut v___y_2953_: *mut leanh::LeanObject,
    mut v___y_2954_: *mut leanh::LeanObject,
    mut v___y_2955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2956_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg(v_ref_2949_, v_constName_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
    leanh::lean_dec(v___y_2954_);
    leanh::lean_dec_ref(v___y_2953_);
    leanh::lean_dec(v___y_2952_);
    leanh::lean_dec_ref(v___y_2951_);
    leanh::lean_dec(v_ref_2949_);
    return v_res_2956_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg(
    mut v_constName_2957_: *mut leanh::LeanObject,
    mut v___y_2958_: *mut leanh::LeanObject,
    mut v___y_2959_: *mut leanh::LeanObject,
    mut v___y_2960_: *mut leanh::LeanObject,
    mut v___y_2961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_2963_ = leanh::lean_ctor_get(v___y_2960_, 5);
    v___x_2964_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg(v_ref_2963_, v_constName_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
    return v___x_2964_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg___boxed(
    mut v_constName_2965_: *mut leanh::LeanObject,
    mut v___y_2966_: *mut leanh::LeanObject,
    mut v___y_2967_: *mut leanh::LeanObject,
    mut v___y_2968_: *mut leanh::LeanObject,
    mut v___y_2969_: *mut leanh::LeanObject,
    mut v___y_2970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2971_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg(v_constName_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_);
    leanh::lean_dec(v___y_2969_);
    leanh::lean_dec_ref(v___y_2968_);
    leanh::lean_dec(v___y_2967_);
    leanh::lean_dec_ref(v___y_2966_);
    return v_res_2971_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0(
    mut v_constName_2972_: *mut leanh::LeanObject,
    mut v___y_2973_: *mut leanh::LeanObject,
    mut v___y_2974_: *mut leanh::LeanObject,
    mut v___y_2975_: *mut leanh::LeanObject,
    mut v___y_2976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: u8 = 0;
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2986_: u8 = 0;
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2990_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2978_ = lean_st_ref_get(v___y_2976_);
                v_env_2979_ = leanh::lean_ctor_get(v___x_2978_, 0);
                leanh::lean_inc_ref(v_env_2979_);
                leanh::lean_dec(v___x_2978_);
                v___x_2980_ = 0;
                leanh::lean_inc(v_constName_2972_);
                v___x_2981_ =
                    l_Lean_Environment_find_x3f(v_env_2979_, v_constName_2972_, v___x_2980_);
                if leanh::lean_obj_tag(v___x_2981_) == 0 {
                    v___x_2982_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg(v_constName_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
                    return v___x_2982_;
                } else {
                    leanh::lean_dec(v_constName_2972_);
                    v_val_2983_ = leanh::lean_ctor_get(v___x_2981_, 0);
                    v_isSharedCheck_2990_ = (!leanh::lean_is_exclusive(v___x_2981_)) as u8;
                    if v_isSharedCheck_2990_ == 0 {
                        v___x_2985_ = v___x_2981_;
                        v_isShared_2986_ = v_isSharedCheck_2990_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2983_);
                        leanh::lean_dec(v___x_2981_);
                        v___x_2985_ = leanh::lean_box(0);
                        v_isShared_2986_ = v_isSharedCheck_2990_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2986_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2985_, 0);
                    v___x_2988_ = v___x_2985_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2989_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_val_2983_);
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
    mut v_constName_2991_: *mut leanh::LeanObject,
    mut v___y_2992_: *mut leanh::LeanObject,
    mut v___y_2993_: *mut leanh::LeanObject,
    mut v___y_2994_: *mut leanh::LeanObject,
    mut v___y_2995_: *mut leanh::LeanObject,
    mut v___y_2996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2997_ = l_Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0(
        v_constName_2991_,
        v___y_2992_,
        v___y_2993_,
        v___y_2994_,
        v___y_2995_,
    );
    leanh::lean_dec(v___y_2995_);
    leanh::lean_dec_ref(v___y_2994_);
    leanh::lean_dec(v___y_2993_);
    leanh::lean_dec_ref(v___y_2992_);
    return v_res_2997_;
}
pub unsafe fn l_Lean_PrettyPrinter_ppSignature(
    mut v_c_3002_: *mut leanh::LeanObject,
    mut v_a_3003_: *mut leanh::LeanObject,
    mut v_a_3004_: *mut leanh::LeanObject,
    mut v_a_3005_: *mut leanh::LeanObject,
    mut v_a_3006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3012_: u8 = 0;
    let mut v_options_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: u8 = 0;
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3028_: u8 = 0;
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3033_: u8 = 0;
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3040_: u8 = 0;
    let mut v_a_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3044_: u8 = 0;
    let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3048_: u8 = 0;
    let mut v_isSharedCheck_3049_: u8 = 0;
    let mut v_a_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3053_: u8 = 0;
    let mut v___x_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3057_: u8 = 0;
    let mut v___x_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3070_: u8 = 0;
    let mut v_a_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3074_: u8 = 0;
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3078_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_c_3002_);
                v___x_3008_ = l_Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0(
                    v_c_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_,
                );
                if leanh::lean_obj_tag(v___x_3008_) == 0 {
                    v_a_3009_ = leanh::lean_ctor_get(v___x_3008_, 0);
                    v_isSharedCheck_3070_ = (!leanh::lean_is_exclusive(v___x_3008_)) as u8;
                    if v_isSharedCheck_3070_ == 0 {
                        v___x_3011_ = v___x_3008_;
                        v_isShared_3012_ = v_isSharedCheck_3070_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3009_);
                        leanh::lean_dec(v___x_3008_);
                        v___x_3011_ = leanh::lean_box(0);
                        v_isShared_3012_ = v_isSharedCheck_3070_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_c_3002_);
                    v_a_3071_ = leanh::lean_ctor_get(v___x_3008_, 0);
                    v_isSharedCheck_3078_ = (!leanh::lean_is_exclusive(v___x_3008_)) as u8;
                    if v_isSharedCheck_3078_ == 0 {
                        v___x_3073_ = v___x_3008_;
                        v_isShared_3074_ = v_isSharedCheck_3078_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3071_);
                        leanh::lean_dec(v___x_3008_);
                        v___x_3073_ = leanh::lean_box(0);
                        v_isShared_3074_ = v_isSharedCheck_3078_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v_options_3013_ = leanh::lean_ctor_get(v_a_3005_, 2);
                v___x_3014_ = l_Lean_ConstantInfo_levelParams(v_a_3009_);
                v___x_3015_ = leanh::lean_box(0);
                v___x_3016_ =
                    l_List_mapTR_loop___at___00Lean_PrettyPrinter_ppConstNameWithInfos_spec__0(
                        v___x_3014_,
                        v___x_3015_,
                    );
                v___x_3017_ = l_Lean_Expr_const___override(v_c_3002_, v___x_3016_);
                v___x_3018_ = l_Lean_pp_raw;
                v___x_3019_ = l_Lean_Option_get___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes_spec__0(v_options_3013_, v___x_3018_);
                if v___x_3019_ == 0 {
                    leanh::lean_del_object(v___x_3011_);
                    leanh::lean_dec(v_a_3009_);
                    v___x_3020_ = leanh::lean_box(1);
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
                    if leanh::lean_obj_tag(v___x_3022_) == 0 {
                        v_a_3023_ = leanh::lean_ctor_get(v___x_3022_, 0);
                        leanh::lean_inc(v_a_3023_);
                        leanh::lean_dec_ref_known(v___x_3022_, 1);
                        v_fst_3024_ = leanh::lean_ctor_get(v_a_3023_, 0);
                        v_snd_3025_ = leanh::lean_ctor_get(v_a_3023_, 1);
                        v_isSharedCheck_3049_ = (!leanh::lean_is_exclusive(v_a_3023_)) as u8;
                        if v_isSharedCheck_3049_ == 0 {
                            v___x_3027_ = v_a_3023_;
                            v_isShared_3028_ = v_isSharedCheck_3049_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_3025_);
                            leanh::lean_inc(v_fst_3024_);
                            leanh::lean_dec(v_a_3023_);
                            v___x_3027_ = leanh::lean_box(0);
                            v_isShared_3028_ = v_isSharedCheck_3049_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_3050_ = leanh::lean_ctor_get(v___x_3022_, 0);
                        v_isSharedCheck_3057_ =
                            (!leanh::lean_is_exclusive(v___x_3022_)) as u8;
                        if v_isSharedCheck_3057_ == 0 {
                            v___x_3052_ = v___x_3022_;
                            v_isShared_3053_ = v_isSharedCheck_3057_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3050_);
                            leanh::lean_dec(v___x_3022_);
                            v___x_3052_ = leanh::lean_box(0);
                            v_isShared_3053_ = v_isSharedCheck_3057_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v___x_3058_ = lean_expr_dbg_to_string(v___x_3017_);
                    leanh::lean_dec_ref(v___x_3017_);
                    v___x_3059_ = l_Lean_PrettyPrinter_ppSignature___closed__1;
                    v___x_3060_ = lean_string_append(v___x_3058_, v___x_3059_);
                    v___x_3061_ = l_Lean_ConstantInfo_type(v_a_3009_);
                    leanh::lean_dec(v_a_3009_);
                    v___x_3062_ = lean_expr_dbg_to_string(v___x_3061_);
                    leanh::lean_dec_ref(v___x_3061_);
                    v___x_3063_ = lean_string_append(v___x_3060_, v___x_3062_);
                    leanh::lean_dec_ref(v___x_3062_);
                    v___x_3064_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3064_, 0, v___x_3063_);
                    v___x_3065_ = leanh::lean_box(1);
                    v___x_3066_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3066_, 0, v___x_3064_);
                    leanh::lean_ctor_set(v___x_3066_, 1, v___x_3065_);
                    if v_isShared_3012_ == 0 {
                        leanh::lean_ctor_set(v___x_3011_, 0, v___x_3066_);
                        v___x_3068_ = v___x_3011_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3069_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3069_, 0, v___x_3066_);
                        v___x_3068_ = v_reuseFailAlloc_3069_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3029_ = l_Lean_PrettyPrinter_ppTerm(v_fst_3024_, v_a_3005_, v_a_3006_);
                if leanh::lean_obj_tag(v___x_3029_) == 0 {
                    v_a_3030_ = leanh::lean_ctor_get(v___x_3029_, 0);
                    v_isSharedCheck_3040_ = (!leanh::lean_is_exclusive(v___x_3029_)) as u8;
                    if v_isSharedCheck_3040_ == 0 {
                        v___x_3032_ = v___x_3029_;
                        v_isShared_3033_ = v_isSharedCheck_3040_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3030_);
                        leanh::lean_dec(v___x_3029_);
                        v___x_3032_ = leanh::lean_box(0);
                        v_isShared_3033_ = v_isSharedCheck_3040_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3027_);
                    leanh::lean_dec(v_snd_3025_);
                    v_a_3041_ = leanh::lean_ctor_get(v___x_3029_, 0);
                    v_isSharedCheck_3048_ = (!leanh::lean_is_exclusive(v___x_3029_)) as u8;
                    if v_isSharedCheck_3048_ == 0 {
                        v___x_3043_ = v___x_3029_;
                        v_isShared_3044_ = v_isSharedCheck_3048_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3041_);
                        leanh::lean_dec(v___x_3029_);
                        v___x_3043_ = leanh::lean_box(0);
                        v_isShared_3044_ = v_isSharedCheck_3048_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3028_ == 0 {
                    leanh::lean_ctor_set(v___x_3027_, 0, v_a_3030_);
                    v___x_3035_ = v___x_3027_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3039_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_3030_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3039_, 1, v_snd_3025_);
                    v___x_3035_ = v_reuseFailAlloc_3039_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3033_ == 0 {
                    leanh::lean_ctor_set(v___x_3032_, 0, v___x_3035_);
                    v___x_3037_ = v___x_3032_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3038_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3035_);
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
                    v_reuseFailAlloc_3047_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3041_);
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
                    v_reuseFailAlloc_3056_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3050_);
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
                    v_reuseFailAlloc_3077_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
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
    mut v_c_3079_: *mut leanh::LeanObject,
    mut v_a_3080_: *mut leanh::LeanObject,
    mut v_a_3081_: *mut leanh::LeanObject,
    mut v_a_3082_: *mut leanh::LeanObject,
    mut v_a_3083_: *mut leanh::LeanObject,
    mut v_a_3084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3085_ =
        l_Lean_PrettyPrinter_ppSignature(v_c_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_);
    leanh::lean_dec(v_a_3083_);
    leanh::lean_dec_ref(v_a_3082_);
    leanh::lean_dec(v_a_3081_);
    leanh::lean_dec_ref(v_a_3080_);
    return v_res_3085_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0(
    mut v_00_u03b1_3086_: *mut leanh::LeanObject,
    mut v_constName_3087_: *mut leanh::LeanObject,
    mut v___y_3088_: *mut leanh::LeanObject,
    mut v___y_3089_: *mut leanh::LeanObject,
    mut v___y_3090_: *mut leanh::LeanObject,
    mut v___y_3091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3093_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___redArg(v_constName_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
    return v___x_3093_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0___boxed(
    mut v_00_u03b1_3094_: *mut leanh::LeanObject,
    mut v_constName_3095_: *mut leanh::LeanObject,
    mut v___y_3096_: *mut leanh::LeanObject,
    mut v___y_3097_: *mut leanh::LeanObject,
    mut v___y_3098_: *mut leanh::LeanObject,
    mut v___y_3099_: *mut leanh::LeanObject,
    mut v___y_3100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3101_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0(v_00_u03b1_3094_, v_constName_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_);
    leanh::lean_dec(v___y_3099_);
    leanh::lean_dec_ref(v___y_3098_);
    leanh::lean_dec(v___y_3097_);
    leanh::lean_dec_ref(v___y_3096_);
    return v_res_3101_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1(
    mut v_00_u03b1_3102_: *mut leanh::LeanObject,
    mut v_ref_3103_: *mut leanh::LeanObject,
    mut v_constName_3104_: *mut leanh::LeanObject,
    mut v___y_3105_: *mut leanh::LeanObject,
    mut v___y_3106_: *mut leanh::LeanObject,
    mut v___y_3107_: *mut leanh::LeanObject,
    mut v___y_3108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3110_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___redArg(v_ref_3103_, v_constName_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
    return v___x_3110_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_3111_: *mut leanh::LeanObject,
    mut v_ref_3112_: *mut leanh::LeanObject,
    mut v_constName_3113_: *mut leanh::LeanObject,
    mut v___y_3114_: *mut leanh::LeanObject,
    mut v___y_3115_: *mut leanh::LeanObject,
    mut v___y_3116_: *mut leanh::LeanObject,
    mut v___y_3117_: *mut leanh::LeanObject,
    mut v___y_3118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3119_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1(v_00_u03b1_3111_, v_ref_3112_, v_constName_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
    leanh::lean_dec(v___y_3117_);
    leanh::lean_dec_ref(v___y_3116_);
    leanh::lean_dec(v___y_3115_);
    leanh::lean_dec_ref(v___y_3114_);
    leanh::lean_dec(v_ref_3112_);
    return v_res_3119_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_3120_: *mut leanh::LeanObject,
    mut v_ref_3121_: *mut leanh::LeanObject,
    mut v_msg_3122_: *mut leanh::LeanObject,
    mut v_declHint_3123_: *mut leanh::LeanObject,
    mut v___y_3124_: *mut leanh::LeanObject,
    mut v___y_3125_: *mut leanh::LeanObject,
    mut v___y_3126_: *mut leanh::LeanObject,
    mut v___y_3127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3129_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_3121_, v_msg_3122_, v_declHint_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
    return v___x_3129_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_3130_: *mut leanh::LeanObject,
    mut v_ref_3131_: *mut leanh::LeanObject,
    mut v_msg_3132_: *mut leanh::LeanObject,
    mut v_declHint_3133_: *mut leanh::LeanObject,
    mut v___y_3134_: *mut leanh::LeanObject,
    mut v___y_3135_: *mut leanh::LeanObject,
    mut v___y_3136_: *mut leanh::LeanObject,
    mut v___y_3137_: *mut leanh::LeanObject,
    mut v___y_3138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3139_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3130_, v_ref_3131_, v_msg_3132_, v_declHint_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
    leanh::lean_dec(v___y_3137_);
    leanh::lean_dec_ref(v___y_3136_);
    leanh::lean_dec(v___y_3135_);
    leanh::lean_dec_ref(v___y_3134_);
    leanh::lean_dec(v_ref_3131_);
    return v_res_3139_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_3140_: *mut leanh::LeanObject,
    mut v_declHint_3141_: *mut leanh::LeanObject,
    mut v___y_3142_: *mut leanh::LeanObject,
    mut v___y_3143_: *mut leanh::LeanObject,
    mut v___y_3144_: *mut leanh::LeanObject,
    mut v___y_3145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3147_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_3140_, v_declHint_3141_, v___y_3145_);
    return v___x_3147_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msg_3148_: *mut leanh::LeanObject,
    mut v_declHint_3149_: *mut leanh::LeanObject,
    mut v___y_3150_: *mut leanh::LeanObject,
    mut v___y_3151_: *mut leanh::LeanObject,
    mut v___y_3152_: *mut leanh::LeanObject,
    mut v___y_3153_: *mut leanh::LeanObject,
    mut v___y_3154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3155_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_3148_, v_declHint_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
    leanh::lean_dec(v___y_3153_);
    leanh::lean_dec_ref(v___y_3152_);
    leanh::lean_dec(v___y_3151_);
    leanh::lean_dec_ref(v___y_3150_);
    return v_res_3155_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b1_3156_: *mut leanh::LeanObject,
    mut v_ref_3157_: *mut leanh::LeanObject,
    mut v_msg_3158_: *mut leanh::LeanObject,
    mut v___y_3159_: *mut leanh::LeanObject,
    mut v___y_3160_: *mut leanh::LeanObject,
    mut v___y_3161_: *mut leanh::LeanObject,
    mut v___y_3162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3164_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_3157_, v_msg_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
    return v___x_3164_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_3165_: *mut leanh::LeanObject,
    mut v_ref_3166_: *mut leanh::LeanObject,
    mut v_msg_3167_: *mut leanh::LeanObject,
    mut v___y_3168_: *mut leanh::LeanObject,
    mut v___y_3169_: *mut leanh::LeanObject,
    mut v___y_3170_: *mut leanh::LeanObject,
    mut v___y_3171_: *mut leanh::LeanObject,
    mut v___y_3172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3173_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_3165_, v_ref_3166_, v_msg_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
    leanh::lean_dec(v___y_3171_);
    leanh::lean_dec_ref(v___y_3170_);
    leanh::lean_dec(v___y_3169_);
    leanh::lean_dec_ref(v___y_3168_);
    leanh::lean_dec(v_ref_3166_);
    return v_res_3173_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b1_3174_: *mut leanh::LeanObject,
    mut v_msg_3175_: *mut leanh::LeanObject,
    mut v___y_3176_: *mut leanh::LeanObject,
    mut v___y_3177_: *mut leanh::LeanObject,
    mut v___y_3178_: *mut leanh::LeanObject,
    mut v___y_3179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3181_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
    return v___x_3181_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b1_3182_: *mut leanh::LeanObject,
    mut v_msg_3183_: *mut leanh::LeanObject,
    mut v___y_3184_: *mut leanh::LeanObject,
    mut v___y_3185_: *mut leanh::LeanObject,
    mut v___y_3186_: *mut leanh::LeanObject,
    mut v___y_3187_: *mut leanh::LeanObject,
    mut v___y_3188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3189_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_ppSignature_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_3182_, v_msg_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
    leanh::lean_dec(v___y_3187_);
    leanh::lean_dec_ref(v___y_3186_);
    leanh::lean_dec(v___y_3185_);
    leanh::lean_dec_ref(v___y_3184_);
    return v_res_3189_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(
    mut v_x_3190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3197_: u8 = 0;
    let mut v___x_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3202_: u8 = 0;
    let mut v_a_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3207_: u8 = 0;
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3212_: u8 = 0;
    let mut v_a_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3216_: u8 = 0;
    let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3221_: u8 = 0;
    let mut v_a_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3226_: u8 = 0;
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3232_: u8 = 0;
    let mut v_a_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3237_: u8 = 0;
    let mut v___x_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3242_: u8 = 0;
    let mut v_data_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3248_: u8 = 0;
    let mut v___x_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3250_: usize = 0;
    let mut v___x_3251_: usize = 0;
    let mut v___x_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3256_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_3190_) {
                3 => {
                    v_a_3191_ = leanh::lean_ctor_get(v_x_3190_, 1);
                    leanh::lean_inc_ref(v_a_3191_);
                    leanh::lean_dec_ref_known(v_x_3190_, 2);
                    v_x_3190_ = v_a_3191_;
                    state = 0;
                    continue;
                }
                4 => {
                    v_a_3193_ = leanh::lean_ctor_get(v_x_3190_, 0);
                    v_a_3194_ = leanh::lean_ctor_get(v_x_3190_, 1);
                    v_isSharedCheck_3202_ = (!leanh::lean_is_exclusive(v_x_3190_)) as u8;
                    if v_isSharedCheck_3202_ == 0 {
                        v___x_3196_ = v_x_3190_;
                        v_isShared_3197_ = v_isSharedCheck_3202_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3194_);
                        leanh::lean_inc(v_a_3193_);
                        leanh::lean_dec(v_x_3190_);
                        v___x_3196_ = leanh::lean_box(0);
                        v_isShared_3197_ = v_isSharedCheck_3202_;
                        state = 1;
                        continue;
                    }
                }
                5 => {
                    v_a_3203_ = leanh::lean_ctor_get(v_x_3190_, 0);
                    v_a_3204_ = leanh::lean_ctor_get(v_x_3190_, 1);
                    v_isSharedCheck_3212_ = (!leanh::lean_is_exclusive(v_x_3190_)) as u8;
                    if v_isSharedCheck_3212_ == 0 {
                        v___x_3206_ = v_x_3190_;
                        v_isShared_3207_ = v_isSharedCheck_3212_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3204_);
                        leanh::lean_inc(v_a_3203_);
                        leanh::lean_dec(v_x_3190_);
                        v___x_3206_ = leanh::lean_box(0);
                        v_isShared_3207_ = v_isSharedCheck_3212_;
                        state = 3;
                        continue;
                    }
                }
                6 => {
                    v_a_3213_ = leanh::lean_ctor_get(v_x_3190_, 0);
                    v_isSharedCheck_3221_ = (!leanh::lean_is_exclusive(v_x_3190_)) as u8;
                    if v_isSharedCheck_3221_ == 0 {
                        v___x_3215_ = v_x_3190_;
                        v_isShared_3216_ = v_isSharedCheck_3221_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3213_);
                        leanh::lean_dec(v_x_3190_);
                        v___x_3215_ = leanh::lean_box(0);
                        v_isShared_3216_ = v_isSharedCheck_3221_;
                        state = 5;
                        continue;
                    }
                }
                7 => {
                    v_a_3222_ = leanh::lean_ctor_get(v_x_3190_, 0);
                    v_a_3223_ = leanh::lean_ctor_get(v_x_3190_, 1);
                    v_isSharedCheck_3232_ = (!leanh::lean_is_exclusive(v_x_3190_)) as u8;
                    if v_isSharedCheck_3232_ == 0 {
                        v___x_3225_ = v_x_3190_;
                        v_isShared_3226_ = v_isSharedCheck_3232_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3223_);
                        leanh::lean_inc(v_a_3222_);
                        leanh::lean_dec(v_x_3190_);
                        v___x_3225_ = leanh::lean_box(0);
                        v_isShared_3226_ = v_isSharedCheck_3232_;
                        state = 7;
                        continue;
                    }
                }
                8 => {
                    v_a_3233_ = leanh::lean_ctor_get(v_x_3190_, 0);
                    v_a_3234_ = leanh::lean_ctor_get(v_x_3190_, 1);
                    v_isSharedCheck_3242_ = (!leanh::lean_is_exclusive(v_x_3190_)) as u8;
                    if v_isSharedCheck_3242_ == 0 {
                        v___x_3236_ = v_x_3190_;
                        v_isShared_3237_ = v_isSharedCheck_3242_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3234_);
                        leanh::lean_inc(v_a_3233_);
                        leanh::lean_dec(v_x_3190_);
                        v___x_3236_ = leanh::lean_box(0);
                        v_isShared_3237_ = v_isSharedCheck_3242_;
                        state = 9;
                        continue;
                    }
                }
                9 => {
                    v_data_3243_ = leanh::lean_ctor_get(v_x_3190_, 0);
                    v_msg_3244_ = leanh::lean_ctor_get(v_x_3190_, 1);
                    v_children_3245_ = leanh::lean_ctor_get(v_x_3190_, 2);
                    v_isSharedCheck_3256_ = (!leanh::lean_is_exclusive(v_x_3190_)) as u8;
                    if v_isSharedCheck_3256_ == 0 {
                        v___x_3247_ = v_x_3190_;
                        v_isShared_3248_ = v_isSharedCheck_3256_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_children_3245_);
                        leanh::lean_inc(v_msg_3244_);
                        leanh::lean_inc(v_data_3243_);
                        leanh::lean_dec(v_x_3190_);
                        v___x_3247_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_3196_, 1, v___x_3198_);
                    v___x_3200_ = v___x_3196_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3201_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3193_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3201_, 1, v___x_3198_);
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
                    leanh::lean_ctor_set(v___x_3206_, 1, v___x_3208_);
                    v___x_3210_ = v___x_3206_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3211_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3203_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3211_, 1, v___x_3208_);
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
                    leanh::lean_ctor_set(v___x_3215_, 0, v___x_3217_);
                    v___x_3219_ = v___x_3215_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3220_ = leanh::lean_alloc_ctor(6, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3217_);
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
                    leanh::lean_ctor_set(v___x_3225_, 1, v___x_3228_);
                    leanh::lean_ctor_set(v___x_3225_, 0, v___x_3227_);
                    v___x_3230_ = v___x_3225_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3231_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___x_3227_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3231_, 1, v___x_3228_);
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
                    leanh::lean_ctor_set(v___x_3236_, 1, v___x_3238_);
                    v___x_3240_ = v___x_3236_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3241_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3233_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3241_, 1, v___x_3238_);
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
                    leanh::lean_ctor_set(v___x_3247_, 2, v___x_3252_);
                    leanh::lean_ctor_set(v___x_3247_, 1, v___x_3249_);
                    v___x_3254_ = v___x_3247_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3255_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_data_3243_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3255_, 1, v___x_3249_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3255_, 2, v___x_3252_);
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
    mut v_bs_3259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3260_: u8 = 0;
    let mut v_v_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: usize = 0;
    let mut v___x_3266_: usize = 0;
    let mut v___x_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3260_ = lean_usize_dec_lt(v_i_3258_, v_sz_3257_);
                if v___x_3260_ == 0 {
                    return v_bs_3259_;
                } else {
                    v_v_3261_ = lean_array_uget(v_bs_3259_, v_i_3258_);
                    v___x_3262_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_3269_: *mut leanh::LeanObject,
    mut v_i_3270_: *mut leanh::LeanObject,
    mut v_bs_3271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3272_: usize = 0;
    let mut v_i_boxed_3273_: usize = 0;
    let mut v_res_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3272_ = leanh::lean_unbox_usize(v_sz_3269_);
    leanh::lean_dec(v_sz_3269_);
    v_i_boxed_3273_ = leanh::lean_unbox_usize(v_i_3270_);
    leanh::lean_dec(v_i_3270_);
    v_res_3274_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0(v_sz_boxed_3272_, v_i_boxed_3273_, v_bs_3271_);
    return v_res_3274_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg___lam__0(
    mut v_throw_3275_: *mut leanh::LeanObject,
    mut v_x_3276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3281_: u8 = 0;
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3287_: u8 = 0;
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3276_) == 0 {
                    v_ref_3277_ = leanh::lean_ctor_get(v_x_3276_, 0);
                    v_msg_3278_ = leanh::lean_ctor_get(v_x_3276_, 1);
                    v_isSharedCheck_3287_ = (!leanh::lean_is_exclusive(v_x_3276_)) as u8;
                    if v_isSharedCheck_3287_ == 0 {
                        v___x_3280_ = v_x_3276_;
                        v_isShared_3281_ = v_isSharedCheck_3287_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_msg_3278_);
                        leanh::lean_inc(v_ref_3277_);
                        leanh::lean_dec(v_x_3276_);
                        v___x_3280_ = leanh::lean_box(0);
                        v_isShared_3281_ = v_isSharedCheck_3287_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3288_ = leanh::lean_apply_2(
                        v_throw_3275_,
                        leanh::lean_box(0),
                        v_x_3276_,
                    );
                    return v___x_3288_;
                }
            }
            1 => {
                v___x_3282_ =
                    l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_msg_3278_);
                if v_isShared_3281_ == 0 {
                    leanh::lean_ctor_set(v___x_3280_, 1, v___x_3282_);
                    v___x_3284_ = v___x_3280_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3286_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_ref_3277_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3286_, 1, v___x_3282_);
                    v___x_3284_ = v_reuseFailAlloc_3286_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3285_ = leanh::lean_apply_2(
                    v_throw_3275_,
                    leanh::lean_box(0),
                    v___x_3284_,
                );
                return v___x_3285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg(
    mut v_inst_3289_: *mut leanh::LeanObject,
    mut v_x_3290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_throw_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tryCatch_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_throw_3291_ = leanh::lean_ctor_get(v_inst_3289_, 0);
    leanh::lean_inc(v_throw_3291_);
    v_tryCatch_3292_ = leanh::lean_ctor_get(v_inst_3289_, 1);
    leanh::lean_inc(v_tryCatch_3292_);
    leanh::lean_dec_ref(v_inst_3289_);
    v___f_3293_ = leanh::lean_alloc_closure(
        l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3293_, 0, v_throw_3291_);
    v___x_3294_ = leanh::lean_apply_3(
        v_tryCatch_3292_,
        leanh::lean_box(0),
        v_x_3290_,
        v___f_3293_,
    );
    return v___x_3294_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext(
    mut v_00_u03b1_3295_: *mut leanh::LeanObject,
    mut v_m_3296_: *mut leanh::LeanObject,
    mut v_inst_3297_: *mut leanh::LeanObject,
    mut v_x_3298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3299_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg(
        v_inst_3297_,
        v_x_3298_,
    );
    return v___x_3299_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___redArg(
    mut v_x_3300_: *mut leanh::LeanObject,
    mut v___y_3301_: *mut leanh::LeanObject,
    mut v___y_3302_: *mut leanh::LeanObject,
    mut v___y_3303_: *mut leanh::LeanObject,
    mut v___y_3304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3309_: u8 = 0;
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3312_: u8 = 0;
    let mut v_ref_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3317_: u8 = 0;
    let mut v___x_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3325_: u8 = 0;
    let mut v_isSharedCheck_3326_: u8 = 0;
    let mut v_unused_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: u8 = 0;
    let mut v___x_3329_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_3304_);
                leanh::lean_inc_ref(v___y_3303_);
                leanh::lean_inc(v___y_3302_);
                leanh::lean_inc_ref(v___y_3301_);
                v___x_3306_ = leanh::lean_apply_5(
                    v_x_3300_,
                    v___y_3301_,
                    v___y_3302_,
                    v___y_3303_,
                    v___y_3304_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_3306_) == 0 {
                    return v___x_3306_;
                } else {
                    v_a_3307_ = leanh::lean_ctor_get(v___x_3306_, 0);
                    leanh::lean_inc(v_a_3307_);
                    v___x_3328_ = l_Lean_Exception_isInterrupt(v_a_3307_);
                    if v___x_3328_ == 0 {
                        leanh::lean_inc(v_a_3307_);
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
                    if leanh::lean_obj_tag(v_a_3307_) == 0 {
                        v_isSharedCheck_3326_ =
                            (!leanh::lean_is_exclusive(v___x_3306_)) as u8;
                        if v_isSharedCheck_3326_ == 0 {
                            v_unused_3327_ = leanh::lean_ctor_get(v___x_3306_, 0);
                            leanh::lean_dec(v_unused_3327_);
                            v___x_3311_ = v___x_3306_;
                            v_isShared_3312_ = v_isSharedCheck_3326_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_3306_);
                            v___x_3311_ = leanh::lean_box(0);
                            v_isShared_3312_ = v_isSharedCheck_3326_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3307_);
                        return v___x_3306_;
                    }
                } else {
                    leanh::lean_dec(v_a_3307_);
                    return v___x_3306_;
                }
            }
            2 => {
                v_ref_3313_ = leanh::lean_ctor_get(v_a_3307_, 0);
                v_msg_3314_ = leanh::lean_ctor_get(v_a_3307_, 1);
                v_isSharedCheck_3325_ = (!leanh::lean_is_exclusive(v_a_3307_)) as u8;
                if v_isSharedCheck_3325_ == 0 {
                    v___x_3316_ = v_a_3307_;
                    v_isShared_3317_ = v_isSharedCheck_3325_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_msg_3314_);
                    leanh::lean_inc(v_ref_3313_);
                    leanh::lean_dec(v_a_3307_);
                    v___x_3316_ = leanh::lean_box(0);
                    v_isShared_3317_ = v_isSharedCheck_3325_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3318_ =
                    l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_msg_3314_);
                if v_isShared_3317_ == 0 {
                    leanh::lean_ctor_set(v___x_3316_, 1, v___x_3318_);
                    v___x_3320_ = v___x_3316_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3324_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_ref_3313_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3324_, 1, v___x_3318_);
                    v___x_3320_ = v_reuseFailAlloc_3324_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3312_ == 0 {
                    leanh::lean_ctor_set(v___x_3311_, 0, v___x_3320_);
                    v___x_3322_ = v___x_3311_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3323_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3323_, 0, v___x_3320_);
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
    mut v_x_3330_: *mut leanh::LeanObject,
    mut v___y_3331_: *mut leanh::LeanObject,
    mut v___y_3332_: *mut leanh::LeanObject,
    mut v___y_3333_: *mut leanh::LeanObject,
    mut v___y_3334_: *mut leanh::LeanObject,
    mut v___y_3335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3336_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___redArg(v_x_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
    leanh::lean_dec(v___y_3334_);
    leanh::lean_dec_ref(v___y_3333_);
    leanh::lean_dec(v___y_3332_);
    leanh::lean_dec_ref(v___y_3331_);
    return v_res_3336_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_3337_: *mut leanh::LeanObject,
    mut v_x_3338_: *mut leanh::LeanObject,
    mut v___y_3339_: *mut leanh::LeanObject,
    mut v___y_3340_: *mut leanh::LeanObject,
    mut v___y_3341_: *mut leanh::LeanObject,
    mut v___y_3342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3344_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___redArg(v_x_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
    return v___x_3344_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_3345_: *mut leanh::LeanObject,
    mut v_x_3346_: *mut leanh::LeanObject,
    mut v___y_3347_: *mut leanh::LeanObject,
    mut v___y_3348_: *mut leanh::LeanObject,
    mut v___y_3349_: *mut leanh::LeanObject,
    mut v___y_3350_: *mut leanh::LeanObject,
    mut v___y_3351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3352_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0(v_00_u03b1_3345_, v_x_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
    leanh::lean_dec(v___y_3350_);
    leanh::lean_dec_ref(v___y_3349_);
    leanh::lean_dec(v___y_3348_);
    leanh::lean_dec_ref(v___y_3347_);
    return v_res_3352_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___redArg(
    mut v_x_3353_: *mut leanh::LeanObject,
    mut v___y_3354_: *mut leanh::LeanObject,
    mut v___y_3355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3360_: u8 = 0;
    let mut v___x_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3363_: u8 = 0;
    let mut v_ref_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3368_: u8 = 0;
    let mut v___x_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3376_: u8 = 0;
    let mut v_isSharedCheck_3377_: u8 = 0;
    let mut v_unused_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: u8 = 0;
    let mut v___x_3380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_3355_);
                leanh::lean_inc_ref(v___y_3354_);
                v___x_3357_ = leanh::lean_apply_3(
                    v_x_3353_,
                    v___y_3354_,
                    v___y_3355_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_3357_) == 0 {
                    return v___x_3357_;
                } else {
                    v_a_3358_ = leanh::lean_ctor_get(v___x_3357_, 0);
                    leanh::lean_inc(v_a_3358_);
                    v___x_3379_ = l_Lean_Exception_isInterrupt(v_a_3358_);
                    if v___x_3379_ == 0 {
                        leanh::lean_inc(v_a_3358_);
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
                    if leanh::lean_obj_tag(v_a_3358_) == 0 {
                        v_isSharedCheck_3377_ =
                            (!leanh::lean_is_exclusive(v___x_3357_)) as u8;
                        if v_isSharedCheck_3377_ == 0 {
                            v_unused_3378_ = leanh::lean_ctor_get(v___x_3357_, 0);
                            leanh::lean_dec(v_unused_3378_);
                            v___x_3362_ = v___x_3357_;
                            v_isShared_3363_ = v_isSharedCheck_3377_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_3357_);
                            v___x_3362_ = leanh::lean_box(0);
                            v_isShared_3363_ = v_isSharedCheck_3377_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3358_);
                        return v___x_3357_;
                    }
                } else {
                    leanh::lean_dec(v_a_3358_);
                    return v___x_3357_;
                }
            }
            2 => {
                v_ref_3364_ = leanh::lean_ctor_get(v_a_3358_, 0);
                v_msg_3365_ = leanh::lean_ctor_get(v_a_3358_, 1);
                v_isSharedCheck_3376_ = (!leanh::lean_is_exclusive(v_a_3358_)) as u8;
                if v_isSharedCheck_3376_ == 0 {
                    v___x_3367_ = v_a_3358_;
                    v_isShared_3368_ = v_isSharedCheck_3376_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_msg_3365_);
                    leanh::lean_inc(v_ref_3364_);
                    leanh::lean_dec(v_a_3358_);
                    v___x_3367_ = leanh::lean_box(0);
                    v_isShared_3368_ = v_isSharedCheck_3376_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3369_ =
                    l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(v_msg_3365_);
                if v_isShared_3368_ == 0 {
                    leanh::lean_ctor_set(v___x_3367_, 1, v___x_3369_);
                    v___x_3371_ = v___x_3367_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3375_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_ref_3364_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3375_, 1, v___x_3369_);
                    v___x_3371_ = v_reuseFailAlloc_3375_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3363_ == 0 {
                    leanh::lean_ctor_set(v___x_3362_, 0, v___x_3371_);
                    v___x_3373_ = v___x_3362_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3374_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3371_);
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
    mut v_x_3381_: *mut leanh::LeanObject,
    mut v___y_3382_: *mut leanh::LeanObject,
    mut v___y_3383_: *mut leanh::LeanObject,
    mut v___y_3384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3385_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___redArg(v_x_3381_, v___y_3382_, v___y_3383_);
    leanh::lean_dec(v___y_3383_);
    leanh::lean_dec_ref(v___y_3382_);
    return v_res_3385_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1(
    mut v_00_u03b1_3386_: *mut leanh::LeanObject,
    mut v_x_3387_: *mut leanh::LeanObject,
    mut v___y_3388_: *mut leanh::LeanObject,
    mut v___y_3389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3391_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___redArg(v_x_3387_, v___y_3388_, v___y_3389_);
    return v___x_3391_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___boxed(
    mut v_00_u03b1_3392_: *mut leanh::LeanObject,
    mut v_x_3393_: *mut leanh::LeanObject,
    mut v___y_3394_: *mut leanh::LeanObject,
    mut v___y_3395_: *mut leanh::LeanObject,
    mut v___y_3396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3397_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1(v_00_u03b1_3392_, v_x_3393_, v___y_3394_, v___y_3395_);
    leanh::lean_dec(v___y_3395_);
    leanh::lean_dec_ref(v___y_3394_);
    return v_res_3397_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(
    mut v_ctx_3399_: *mut leanh::LeanObject,
    mut v_e_3400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3402_ = leanh::lean_box(1);
    v___x_3403_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0___closed__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_;
    v___x_3404_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_ppExprWithInfos___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    leanh::lean_closure_set(v___x_3404_, 0, v_e_3400_);
    leanh::lean_closure_set(v___x_3404_, 1, v___x_3402_);
    leanh::lean_closure_set(v___x_3404_, 2, v___x_3403_);
    v___x_3405_ = leanh::lean_alloc_closure(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___boxed as *mut core::ffi::c_void, 7, 2);
    leanh::lean_closure_set(v___x_3405_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3405_, 1, v___x_3404_);
    v___x_3406_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_3399_, v___x_3405_);
    return v___x_3406_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(
    mut v_ctx_3407_: *mut leanh::LeanObject,
    mut v_e_3408_: *mut leanh::LeanObject,
    mut v___y_3409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3410_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__0_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(v_ctx_3407_, v_e_3408_);
    leanh::lean_dec_ref(v_ctx_3407_);
    return v_res_3410_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(
    mut v_ctx_3411_: *mut leanh::LeanObject,
    mut v_n_3412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3414_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_ppConstNameWithInfos___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_3414_, 0, v_n_3412_);
    v___x_3415_ = leanh::lean_alloc_closure(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___boxed as *mut core::ffi::c_void, 7, 2);
    leanh::lean_closure_set(v___x_3415_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3415_, 1, v___x_3414_);
    v___x_3416_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_3411_, v___x_3415_);
    return v___x_3416_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(
    mut v_ctx_3417_: *mut leanh::LeanObject,
    mut v_n_3418_: *mut leanh::LeanObject,
    mut v___y_3419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3420_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__1_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(v_ctx_3417_, v_n_3418_);
    leanh::lean_dec_ref(v_ctx_3417_);
    return v_res_3420_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(
    mut v_ctx_3421_: *mut leanh::LeanObject,
    mut v_l_3422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3424_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_ppLevel___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_3424_, 0, v_l_3422_);
    v___x_3425_ = leanh::lean_alloc_closure(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___boxed as *mut core::ffi::c_void, 7, 2);
    leanh::lean_closure_set(v___x_3425_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3425_, 1, v___x_3424_);
    v___x_3426_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_3421_, v___x_3425_);
    return v___x_3426_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(
    mut v_ctx_3427_: *mut leanh::LeanObject,
    mut v_l_3428_: *mut leanh::LeanObject,
    mut v___y_3429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3430_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__2_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(v_ctx_3427_, v_l_3428_);
    leanh::lean_dec_ref(v_ctx_3427_);
    return v_res_3430_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(
    mut v_ctx_3431_: *mut leanh::LeanObject,
    mut v_mvarId_3432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3434_ = leanh::lean_alloc_closure(
        l_Lean_Meta_ppGoal___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_3434_, 0, v_mvarId_3432_);
    v___x_3435_ = leanh::lean_alloc_closure(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__0___boxed as *mut core::ffi::c_void, 7, 2);
    leanh::lean_closure_set(v___x_3435_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3435_, 1, v___x_3434_);
    v___x_3436_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_3431_, v___x_3435_);
    return v___x_3436_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(
    mut v_ctx_3437_: *mut leanh::LeanObject,
    mut v_mvarId_3438_: *mut leanh::LeanObject,
    mut v___y_3439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3440_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__3_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(v_ctx_3437_, v_mvarId_3438_);
    leanh::lean_dec_ref(v_ctx_3437_);
    return v_res_3440_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(
    mut v_ctx_3441_: *mut leanh::LeanObject,
    mut v_stx_3442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3444_ = leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_ppTerm___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___x_3444_, 0, v_stx_3442_);
    v___x_3445_ = leanh::lean_alloc_closure(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___00__private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2__spec__1___boxed as *mut core::ffi::c_void, 5, 2);
    leanh::lean_closure_set(v___x_3445_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3445_, 1, v___x_3444_);
    v___x_3446_ = l_Lean_PPContext_runCoreM___redArg(v_ctx_3441_, v___x_3445_);
    return v___x_3446_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(
    mut v_ctx_3447_: *mut leanh::LeanObject,
    mut v_stx_3448_: *mut leanh::LeanObject,
    mut v___y_3449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3450_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___lam__4_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_(v_ctx_3447_, v_stx_3448_);
    leanh::lean_dec_ref(v_ctx_3447_);
    return v_res_3450_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3463_ = l_Lean_ppFnsRef;
    v___x_3464_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__5_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_;
    v___x_3465_ = lean_st_ref_set(v___x_3463_, v___x_3464_);
    v___x_3466_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3466_, 0, v___x_3465_);
    return v___x_3466_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2____boxed(
    mut v_a_3467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3468_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_();
    return v_res_3468_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: u8 = 0;
    let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3519_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_;
    v___x_3520_ = 0;
    v___x_3521_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn___closed__19_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_;
    v___x_3522_ = l_Lean_registerTraceClass(v___x_3519_, v___x_3520_, v___x_3521_);
    return v___x_3522_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2____boxed(
    mut v_a_3523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3524_ = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_();
    return v_res_3524_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3528_ = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
    v___x_3529_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_3530_ = l_Lean_PrettyPrinter_registerParserCompilers___closed__1;
    v___x_3531_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3531_, 0, v___x_3530_);
    leanh::lean_ctor_set(v___x_3531_, 1, v___x_3529_);
    leanh::lean_ctor_set(v___x_3531_, 2, v___x_3528_);
    return v___x_3531_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3535_ = l_Lean_PrettyPrinter_combinatorFormatterAttribute;
    v___x_3536_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3537_ = l_Lean_PrettyPrinter_registerParserCompilers___closed__4;
    v___x_3538_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3538_, 0, v___x_3537_);
    leanh::lean_ctor_set(v___x_3538_, 1, v___x_3536_);
    leanh::lean_ctor_set(v___x_3538_, 2, v___x_3535_);
    return v___x_3538_;
}
pub unsafe fn l_Lean_PrettyPrinter_registerParserCompilers() -> *mut leanh::LeanObject {
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3540_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_registerParserCompilers___closed__2),
        core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_registerParserCompilers___closed__2_once),
        _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__2,
    );
    v___x_3541_ = l_Lean_ParserCompiler_registerParserCompiler___redArg(v___x_3540_);
    if leanh::lean_obj_tag(v___x_3541_) == 0 {
        let mut v___x_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_3541_, 1);
        v___x_3542_ = leanh::lean_obj_once(
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
    mut v_a_3544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3545_ = l_Lean_PrettyPrinter_registerParserCompilers();
    return v_res_3545_;
}
pub unsafe fn _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3547_ = l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__0;
    v___x_3548_ = l_Lean_stringToMessageData(v___x_3547_);
    return v___x_3548_;
}
pub unsafe fn _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3550_ = l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__2;
    v___x_3551_ = l_Lean_stringToMessageData(v___x_3550_);
    return v___x_3551_;
}
pub unsafe fn l_Lean_MessageData_ofFormatWithInfosM___lam__0(
    mut v_fmt_3552_: *mut leanh::LeanObject,
    mut v_ctx_3553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3559_: u8 = 0;
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3563_: u8 = 0;
    let mut v_a_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3567_: u8 = 0;
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3577_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3555_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_3553_, v_fmt_3552_);
                if leanh::lean_obj_tag(v___x_3555_) == 0 {
                    v_a_3556_ = leanh::lean_ctor_get(v___x_3555_, 0);
                    v_isSharedCheck_3563_ = (!leanh::lean_is_exclusive(v___x_3555_)) as u8;
                    if v_isSharedCheck_3563_ == 0 {
                        v___x_3558_ = v___x_3555_;
                        v_isShared_3559_ = v_isSharedCheck_3563_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3556_);
                        leanh::lean_dec(v___x_3555_);
                        v___x_3558_ = leanh::lean_box(0);
                        v_isShared_3559_ = v_isSharedCheck_3563_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3564_ = leanh::lean_ctor_get(v___x_3555_, 0);
                    v_isSharedCheck_3577_ = (!leanh::lean_is_exclusive(v___x_3555_)) as u8;
                    if v_isSharedCheck_3577_ == 0 {
                        v___x_3566_ = v___x_3555_;
                        v_isShared_3567_ = v_isSharedCheck_3577_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3564_);
                        leanh::lean_dec(v___x_3555_);
                        v___x_3566_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3562_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3556_);
                    v___x_3561_ = v_reuseFailAlloc_3562_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3561_;
            }
            3 => {
                v___x_3568_ = leanh::lean_obj_once(
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
                    leanh::lean_ctor_set_tag(v___x_3566_, 3);
                    leanh::lean_ctor_set(v___x_3566_, 0, v___x_3569_);
                    v___x_3571_ = v___x_3566_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3576_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3576_, 0, v___x_3569_);
                    v___x_3571_ = v_reuseFailAlloc_3576_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3572_ = l_Lean_MessageData_ofFormat(v___x_3571_);
                v___x_3573_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3573_, 0, v___x_3568_);
                leanh::lean_ctor_set(v___x_3573_, 1, v___x_3572_);
                v___x_3574_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3_once
                    ),
                    _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3,
                );
                v___x_3575_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3575_, 0, v___x_3573_);
                leanh::lean_ctor_set(v___x_3575_, 1, v___x_3574_);
                return v___x_3575_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MessageData_ofFormatWithInfosM___lam__0___boxed(
    mut v_fmt_3578_: *mut leanh::LeanObject,
    mut v_ctx_3579_: *mut leanh::LeanObject,
    mut v___y_3580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3581_ = l_Lean_MessageData_ofFormatWithInfosM___lam__0(v_fmt_3578_, v_ctx_3579_);
    leanh::lean_dec_ref(v_ctx_3579_);
    return v_res_3581_;
}
pub unsafe fn l_Lean_MessageData_ofFormatWithInfosM___lam__1(
    mut v_x_3582_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3583_: u8 = 0;
    v___x_3583_ = 0;
    return v___x_3583_;
}
pub unsafe fn l_Lean_MessageData_ofFormatWithInfosM___lam__1___boxed(
    mut v_x_3584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3585_: u8 = 0;
    let mut v_r_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3585_ = l_Lean_MessageData_ofFormatWithInfosM___lam__1(v_x_3584_);
    leanh::lean_dec_ref(v_x_3584_);
    v_r_3586_ = leanh::lean_box((v_res_3585_) as usize);
    return v_r_3586_;
}
pub unsafe fn _init_l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3590_ = l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__1;
    v___x_3591_ = l_Lean_MessageData_ofFormat(v___x_3590_);
    return v___x_3591_;
}
pub unsafe fn l_Lean_MessageData_ofFormatWithInfosM___lam__2(
    mut v_x_3592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3594_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2),
        core::ptr::addr_of_mut!(l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2_once),
        _init_l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2,
    );
    return v___x_3594_;
}
pub unsafe fn l_Lean_MessageData_ofFormatWithInfosM___lam__2___boxed(
    mut v_x_3595_: *mut leanh::LeanObject,
    mut v___y_3596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3597_ = l_Lean_MessageData_ofFormatWithInfosM___lam__2(v_x_3595_);
    return v_res_3597_;
}
pub unsafe fn l_Lean_MessageData_ofFormatWithInfosM(
    mut v_fmt_3600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3601_ = leanh::lean_alloc_closure(
        l_Lean_MessageData_ofFormatWithInfosM___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_3601_, 0, v_fmt_3600_);
    v___f_3602_ = l_Lean_MessageData_ofFormatWithInfosM___closed__0;
    v___f_3603_ = l_Lean_MessageData_ofFormatWithInfosM___closed__1;
    v___x_3604_ = l_Lean_MessageData_lazy(v___f_3601_, v___f_3602_, v___f_3603_);
    return v___x_3604_;
}
pub unsafe fn l_panic___at___00Lean_MessageData_ofConst_spec__0(
    mut v___x_3605_: *mut leanh::LeanObject,
    mut v_msg_3606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3607_ = lean_panic_fn_borrowed(v___x_3605_, v_msg_3606_);
    return v___x_3607_;
}
pub unsafe fn l_panic___at___00Lean_MessageData_ofConst_spec__0___boxed(
    mut v___x_3608_: *mut leanh::LeanObject,
    mut v_msg_3609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3610_ = l_panic___at___00Lean_MessageData_ofConst_spec__0(v___x_3608_, v_msg_3609_);
    leanh::lean_dec_ref(v___x_3608_);
    return v_res_3610_;
}
pub unsafe fn _init_l_Lean_MessageData_ofConst___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3612_ = l_Lean_MessageData_ofConst___closed__0;
    v___x_3613_ = l_Lean_stringToMessageData(v___x_3612_);
    return v___x_3613_;
}
pub unsafe fn _init_l_Lean_MessageData_ofConst___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3614_ = leanh::lean_box(1);
    v___x_3615_ = l_Lean_MessageData_ofFormat(v___x_3614_);
    return v___x_3615_;
}
pub unsafe fn _init_l_Lean_MessageData_ofConst___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3616_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MessageData_ofConst___closed__2),
        core::ptr::addr_of_mut!(l_Lean_MessageData_ofConst___closed__2_once),
        _init_l_Lean_MessageData_ofConst___closed__2,
    );
    v___x_3617_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MessageData_ofConst___closed__1),
        core::ptr::addr_of_mut!(l_Lean_MessageData_ofConst___closed__1_once),
        _init_l_Lean_MessageData_ofConst___closed__1,
    );
    v___x_3618_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3618_, 0, v___x_3617_);
    leanh::lean_ctor_set(v___x_3618_, 1, v___x_3616_);
    return v___x_3618_;
}
pub unsafe fn _init_l_Lean_MessageData_ofConst___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3622_ = l_Lean_MessageData_ofConst___closed__6;
    v___x_3623_ = leanh::lean_unsigned_to_nat(4);
    v___x_3624_ = leanh::lean_unsigned_to_nat(156);
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
pub unsafe fn l_Lean_MessageData_ofConst(
    mut v_e_3628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3629_: u8 = 0;
    v___x_3629_ = l_Lean_Expr_isConst(v_e_3628_);
    if v___x_3629_ == 0 {
        let mut v___x_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3630_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_MessageData_ofConst___closed__3),
            core::ptr::addr_of_mut!(l_Lean_MessageData_ofConst___closed__3_once),
            _init_l_Lean_MessageData_ofConst___closed__3,
        );
        v___x_3631_ = l_Lean_MessageData_ofExpr(v_e_3628_);
        v___x_3632_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3632_, 0, v___x_3630_);
        leanh::lean_ctor_set(v___x_3632_, 1, v___x_3631_);
        v___x_3633_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_MessageData_ofConst___closed__7),
            core::ptr::addr_of_mut!(l_Lean_MessageData_ofConst___closed__7_once),
            _init_l_Lean_MessageData_ofConst___closed__7,
        );
        v___x_3634_ = lean_panic_fn_borrowed(v___x_3632_, v___x_3633_);
        leanh::lean_dec_ref_known(v___x_3632_, 2);
        return v___x_3634_;
    } else {
        let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_delab_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3635_ = l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1;
        v___x_3636_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
        leanh::lean_ctor_set_uint8(v___x_3636_, 0 as u32, v___x_3629_);
        v___x_3637_ = l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__3;
        v_delab_3638_ = leanh::lean_alloc_closure(
            l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___boxed as *mut core::ffi::c_void,
            11,
            4,
        );
        leanh::lean_closure_set(v_delab_3638_, 0, leanh::lean_box(0));
        leanh::lean_closure_set(v_delab_3638_, 1, v___x_3635_);
        leanh::lean_closure_set(v_delab_3638_, 2, v___x_3636_);
        leanh::lean_closure_set(v_delab_3638_, 3, v___x_3637_);
        v___x_3639_ = leanh::lean_box(1);
        v___x_3640_ = leanh::lean_alloc_closure(
            l_Lean_PrettyPrinter_ppExprWithInfos___boxed as *mut core::ffi::c_void,
            8,
            3,
        );
        leanh::lean_closure_set(v___x_3640_, 0, v_e_3628_);
        leanh::lean_closure_set(v___x_3640_, 1, v___x_3639_);
        leanh::lean_closure_set(v___x_3640_, 2, v_delab_3638_);
        v___x_3641_ = l_Lean_MessageData_ofFormatWithInfosM(v___x_3640_);
        return v___x_3641_;
    }
}
pub unsafe fn _init_l_Lean_MessageData_signature___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3643_ = l_Lean_MessageData_signature___lam__0___closed__0;
    v___x_3644_ = l_Lean_stringToMessageData(v___x_3643_);
    return v___x_3644_;
}
pub unsafe fn l_Lean_MessageData_signature___lam__0(
    mut v_c_3645_: *mut leanh::LeanObject,
    mut v_ctx_3646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3653_: u8 = 0;
    let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3657_: u8 = 0;
    let mut v_a_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3661_: u8 = 0;
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3675_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_c_3645_);
                v___x_3648_ = leanh::lean_alloc_closure(
                    l_Lean_PrettyPrinter_ppSignature___boxed as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___x_3648_, 0, v_c_3645_);
                v___x_3649_ = l_Lean_PPContext_runMetaM___redArg(v_ctx_3646_, v___x_3648_);
                if leanh::lean_obj_tag(v___x_3649_) == 0 {
                    leanh::lean_dec(v_c_3645_);
                    v_a_3650_ = leanh::lean_ctor_get(v___x_3649_, 0);
                    v_isSharedCheck_3657_ = (!leanh::lean_is_exclusive(v___x_3649_)) as u8;
                    if v_isSharedCheck_3657_ == 0 {
                        v___x_3652_ = v___x_3649_;
                        v_isShared_3653_ = v_isSharedCheck_3657_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3650_);
                        leanh::lean_dec(v___x_3649_);
                        v___x_3652_ = leanh::lean_box(0);
                        v_isShared_3653_ = v_isSharedCheck_3657_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3658_ = leanh::lean_ctor_get(v___x_3649_, 0);
                    v_isSharedCheck_3675_ = (!leanh::lean_is_exclusive(v___x_3649_)) as u8;
                    if v_isSharedCheck_3675_ == 0 {
                        v___x_3660_ = v___x_3649_;
                        v_isShared_3661_ = v_isSharedCheck_3675_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3658_);
                        leanh::lean_dec(v___x_3649_);
                        v___x_3660_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3656_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_a_3650_);
                    v___x_3655_ = v_reuseFailAlloc_3656_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3655_;
            }
            3 => {
                v___x_3662_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MessageData_signature___lam__0___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_MessageData_signature___lam__0___closed__1_once),
                    _init_l_Lean_MessageData_signature___lam__0___closed__1,
                );
                v___x_3663_ = lean_io_error_to_string(v_a_3658_);
                if v_isShared_3661_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3660_, 3);
                    leanh::lean_ctor_set(v___x_3660_, 0, v___x_3663_);
                    v___x_3665_ = v___x_3660_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3674_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3663_);
                    v___x_3665_ = v_reuseFailAlloc_3674_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3666_ = l_Lean_MessageData_ofFormat(v___x_3665_);
                v___x_3667_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3667_, 0, v___x_3662_);
                leanh::lean_ctor_set(v___x_3667_, 1, v___x_3666_);
                v___x_3668_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3_once
                    ),
                    _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3,
                );
                v___x_3669_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3669_, 0, v___x_3667_);
                leanh::lean_ctor_set(v___x_3669_, 1, v___x_3668_);
                v___x_3670_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MessageData_ofConst___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_MessageData_ofConst___closed__2_once),
                    _init_l_Lean_MessageData_ofConst___closed__2,
                );
                v___x_3671_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3671_, 0, v___x_3669_);
                leanh::lean_ctor_set(v___x_3671_, 1, v___x_3670_);
                v___x_3672_ = l_Lean_MessageData_ofName(v_c_3645_);
                v___x_3673_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3673_, 0, v___x_3671_);
                leanh::lean_ctor_set(v___x_3673_, 1, v___x_3672_);
                return v___x_3673_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MessageData_signature___lam__0___boxed(
    mut v_c_3676_: *mut leanh::LeanObject,
    mut v_ctx_3677_: *mut leanh::LeanObject,
    mut v___y_3678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3679_ = l_Lean_MessageData_signature___lam__0(v_c_3676_, v_ctx_3677_);
    leanh::lean_dec_ref(v_ctx_3677_);
    return v_res_3679_;
}
pub unsafe fn l_Lean_MessageData_signature(
    mut v_c_3680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3681_ = leanh::lean_alloc_closure(
        l_Lean_MessageData_signature___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_3681_, 0, v_c_3680_);
    v___f_3682_ = l_Lean_MessageData_ofFormatWithInfosM___closed__0;
    v___f_3683_ = l_Lean_MessageData_ofFormatWithInfosM___closed__1;
    v___x_3684_ = l_Lean_MessageData_lazy(v___f_3681_, v___f_3682_, v___f_3683_);
    return v___x_3684_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_PrettyPrinter(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Module(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ParserCompiler(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_NumObjs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ShareCommon(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_1740541145____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_PrettyPrinter_pp_exprSizes = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_PrettyPrinter_pp_exprSizes);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_4173001584____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_675687902____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l_Lean_PrettyPrinter_registerParserCompilers();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_PrettyPrinter(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_PrettyPrinter(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_PrettyPrinter_Delaborator_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_PrettyPrinter_Delaborator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Module(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_ParserCompiler(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_NumObjs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_ShareCommon(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_PrettyPrinter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_PrettyPrinter(builtin);
}
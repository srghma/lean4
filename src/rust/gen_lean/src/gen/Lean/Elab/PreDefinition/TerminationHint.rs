// Lean compiler output
// Module: Lean.Elab.PreDefinition.TerminationHint
// Imports: Lean.Parser.Term Lean.Parser.Term Init.Omega
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Format::Syntax::l_Lean_Syntax_formatStx;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNone, l_Lean_TSyntax_getId};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr4, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getKind,
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isSuffixOf;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Exception::l_Lean_throwErrorAt___redArg;
use crate::r#gen::Lean::Expr::l_Lean_Expr_getNumHeadLambdas;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_MessageLog_add, l_Lean_instBEqMessageSeverity_beq,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Parser::Term::{
    initialize_Lean_Parser_Term, runtime_initialize_Lean_Parser_Term,
};
use crate::ffi::lean_string_append;
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_mk_empty_array_with_capacity,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_string_dec_eq,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l_Lean_Elab_instInhabitedTerminationBy_default___closed__0_value:
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
static mut l_Lean_Elab_instInhabitedTerminationBy_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedTerminationBy_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instInhabitedTerminationBy_default___closed__1_value:
    crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 8) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_instInhabitedTerminationBy_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instInhabitedTerminationBy_default___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedTerminationBy_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedTerminationBy_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedTerminationBy_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedTerminationBy: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedTerminationBy_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instInhabitedDecreasingBy_default___closed__0_value:
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instInhabitedDecreasingBy_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedDecreasingBy_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedDecreasingBy_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedDecreasingBy_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedDecreasingBy: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedDecreasingBy_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedPartialFixpointType_default: u8 = 0;
pub static mut l_Lean_Elab_instInhabitedPartialFixpointType: u8 = 0;
pub static l_Lean_Elab_instInhabitedPartialFixpoint_default___closed__0_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instInhabitedPartialFixpoint_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedPartialFixpoint_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedPartialFixpoint_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedPartialFixpoint_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedPartialFixpoint: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedPartialFixpoint_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_instInhabitedTerminationHints_default___closed__0_value:
    crate::leanh::LeanCtorObject<6> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6
            + 0) as u16,
        other: 6,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instInhabitedTerminationHints_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedTerminationHints_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedTerminationHints_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedTerminationHints_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedTerminationHints: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedTerminationHints_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Elab_TerminationHints_none: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedTerminationHints_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__3_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__5_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_TerminationHints_ensureNone___closed__0_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        117, 110, 117, 115, 101, 100, 32, 116, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 32,
        104, 105, 110, 116, 115, 44, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 105, 115, 32,
        0,
    ],
};
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationHints_ensureNone___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationHints_ensureNone___closed__2_value:
    crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        117, 110, 117, 115, 101, 100, 32, 96, 112, 97, 114, 116, 105, 97, 108, 95, 102, 105, 120,
        112, 111, 105, 110, 116, 96, 44, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 105, 115,
        32, 0,
    ],
};
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationHints_ensureNone___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationHints_ensureNone___closed__4_value:
    crate::leanh::LeanStringObject<44> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 44,
    m_capacity: 44,
    m_length: 43,
    m_data: [
        117, 110, 117, 115, 101, 100, 32, 96, 99, 111, 105, 110, 100, 117, 99, 116, 105, 118, 101,
        95, 102, 105, 120, 112, 111, 105, 110, 116, 96, 44, 32, 102, 117, 110, 99, 116, 105, 111,
        110, 32, 105, 115, 32, 0,
    ],
};
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationHints_ensureNone___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationHints_ensureNone___closed__6_value:
    crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 42,
    m_capacity: 42,
    m_length: 41,
    m_data: [
        117, 110, 117, 115, 101, 100, 32, 96, 105, 110, 100, 117, 99, 116, 105, 118, 101, 95, 102,
        105, 120, 112, 111, 105, 110, 116, 96, 44, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32,
        105, 115, 32, 0,
    ],
};
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationHints_ensureNone___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationHints_ensureNone___closed__8_value:
    crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        117, 110, 117, 115, 101, 100, 32, 96, 100, 101, 99, 114, 101, 97, 115, 105, 110, 103, 95,
        98, 121, 96, 44, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 105, 115, 32, 0,
    ],
};
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationHints_ensureNone___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationHints_ensureNone___closed__10_value:
    crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        117, 110, 117, 115, 101, 100, 32, 96, 116, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110,
        95, 98, 121, 96, 44, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 105, 115, 32, 0,
    ],
};
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationHints_ensureNone___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationHints_ensureNone___closed__12_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        117, 110, 117, 115, 101, 100, 32, 96, 116, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110,
        95, 98, 121, 63, 96, 44, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 105, 115, 32, 0,
    ],
};
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationHints_ensureNone___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__0_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 0]};
static mut l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [111, 110, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 0]};
static mut l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__3_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_TerminationBy_checkVars___closed__0_value: crate::leanh::LeanStringObject<
    45,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 45,
    m_capacity: 45,
    m_length: 44,
    m_data: [
        32, 98, 111, 117, 110, 100, 32, 105, 110, 32, 96, 116, 101, 114, 109, 105, 110, 97, 116,
        105, 111, 110, 95, 98, 121, 96, 44, 32, 98, 117, 116, 32, 116, 104, 101, 32, 98, 111, 100,
        121, 32, 111, 102, 32, 0,
    ],
};
static mut l_Lean_Elab_TerminationBy_checkVars___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationBy_checkVars___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_TerminationBy_checkVars___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_TerminationBy_checkVars___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationBy_checkVars___closed__2_value: crate::leanh::LeanStringObject<
    13,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [32, 111, 110, 108, 121, 32, 98, 105, 110, 100, 115, 32, 0],
};
static mut l_Lean_Elab_TerminationBy_checkVars___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationBy_checkVars___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_TerminationBy_checkVars___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_TerminationBy_checkVars___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationBy_checkVars___closed__4_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [46, 0],
};
static mut l_Lean_Elab_TerminationBy_checkVars___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationBy_checkVars___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_TerminationBy_checkVars___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_TerminationBy_checkVars___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationBy_checkVars___closed__6_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [105, 100, 101, 110, 116, 0],
};
static mut l_Lean_Elab_TerminationBy_checkVars___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationBy_checkVars___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_TerminationBy_checkVars___closed__7_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_TerminationBy_checkVars___closed__6_value)
                as *mut crate::leanh::LeanObject,
            5117844058249666356 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_TerminationBy_checkVars___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationBy_checkVars___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_TerminationBy_checkVars___closed__8_value: crate::leanh::LeanStringObject<
    60,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 60,
    m_capacity: 60,
    m_length: 59,
    m_data: [
        32, 40, 83, 105, 110, 99, 101, 32, 76, 101, 97, 110, 32, 118, 52, 46, 54, 46, 48, 44, 32,
        116, 104, 101, 32, 96, 116, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 95, 98, 121,
        96, 32, 99, 108, 97, 117, 115, 101, 32, 110, 111, 32, 108, 111, 110, 103, 101, 114, 32, 0,
    ],
};
static mut l_Lean_Elab_TerminationBy_checkVars___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationBy_checkVars___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_TerminationBy_checkVars___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_TerminationBy_checkVars___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationBy_checkVars___closed__10_value: crate::leanh::LeanStringObject<
    33,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        101, 120, 112, 101, 99, 116, 115, 32, 116, 104, 101, 32, 102, 117, 110, 99, 116, 105, 111,
        110, 32, 110, 97, 109, 101, 32, 104, 101, 114, 101, 46, 41, 0,
    ],
};
static mut l_Lean_Elab_TerminationBy_checkVars___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationBy_checkVars___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_TerminationBy_checkVars___closed__11_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_TerminationBy_checkVars___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_TerminationBy_checkVars___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationBy_checkVars___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_TerminationBy_checkVars___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_TerminationBy_checkVars___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [100, 101, 99, 114, 101, 97, 115, 105, 110, 103, 66, 121, 0],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__1_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 96, 100, 101, 99, 114, 101, 97, 115,
        105, 110, 103, 95, 98, 121, 96, 32, 115, 121, 110, 116, 97, 120, 0,
    ],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        112, 97, 114, 116, 105, 97, 108, 70, 105, 120, 112, 111, 105, 110, 116, 0,
    ],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1_value:
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
        99, 111, 105, 110, 100, 117, 99, 116, 105, 118, 101, 70, 105, 120, 112, 111, 105, 110, 116,
        0,
    ],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        105, 110, 100, 117, 99, 116, 105, 118, 101, 70, 105, 120, 112, 111, 105, 110, 116, 0,
    ],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__0_value:
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
        116, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 66, 121, 0,
    ],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__1_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        116, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 66, 121, 63, 0,
    ],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__2_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 96, 116, 101, 114, 109, 105, 110, 97,
        116, 105, 111, 110, 95, 98, 121, 96, 32, 115, 121, 110, 116, 97, 120, 0,
    ],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__4_value:
    crate::leanh::LeanStringObject<49> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        110, 111, 32, 101, 120, 116, 114, 97, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115,
        32, 98, 111, 117, 110, 100, 115, 44, 32, 112, 108, 101, 97, 115, 101, 32, 111, 109, 105,
        116, 32, 116, 104, 101, 32, 96, 61, 62, 96, 0,
    ],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_elabTerminationHints___redArg___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_elabTerminationHints___redArg___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_elabTerminationHints___redArg___closed__2_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_elabTerminationHints___redArg___closed__3_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [115, 117, 102, 102, 105, 120, 0],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_elabTerminationHints___redArg___closed__4_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_elabTerminationHints___redArg___closed__4_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_elabTerminationHints___redArg___closed__4_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        7625897890118033792 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_elabTerminationHints___redArg___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8715860392475343861 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_elabTerminationHints___redArg___closed__5_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 84, 101, 114, 109, 105, 110, 97, 116,
        105, 111, 110, 46, 115, 117, 102, 102, 105, 120, 32, 115, 121, 110, 116, 97, 120, 58, 32,
        0,
    ],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_elabTerminationHints___redArg___closed__6_value:
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
    m_data: [32, 111, 102, 32, 107, 105, 110, 100, 32, 0],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_elabTerminationHints___redArg___closed__7_value:
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
    m_fun: l_Lean_Elab_elabTerminationHints___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_elabTerminationHints___redArg___closed__8_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_elabTerminationHints___redArg___closed__8_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__8_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_elabTerminationHints___redArg___closed__8_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__8_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        7625897890118033792 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_elabTerminationHints___redArg___closed__8_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__8_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__1_value)
            as *mut crate::leanh::LeanObject,
        12996790131644993504 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_elabTerminationHints___redArg___closed__9_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_elabTerminationHints___redArg___closed__9_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__9_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_elabTerminationHints___redArg___closed__9_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__9_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        7625897890118033792 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_elabTerminationHints___redArg___closed__9_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__9_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0_value)
            as *mut crate::leanh::LeanObject,
        3331099446614607828 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Elab_PartialFixpointType_ctorIdx(
    mut v_x_1167_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_1167_ {
        0 => {
            let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1168_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1168_;
        }
        1 => {
            let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1169_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1169_;
        }
        _ => {
            let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1170_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1170_;
        }
    }
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_ctorIdx___boxed(
    mut v_x_1171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_1172_: u8 = 0;
    let mut v_res_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1172_ = (crate::leanh::lean_unbox(v_x_1171_) as u8);
    v_res_1173_ = l_Lean_Elab_PartialFixpointType_ctorIdx(v_x_boxed_1172_);
    return v_res_1173_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_toCtorIdx(
    mut v_x_1174_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1175_ = l_Lean_Elab_PartialFixpointType_ctorIdx(v_x_1174_);
    return v___x_1175_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_toCtorIdx___boxed(
    mut v_x_1176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_1177_: u8 = 0;
    let mut v_res_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1177_ = (crate::leanh::lean_unbox(v_x_1176_) as u8);
    v_res_1178_ = l_Lean_Elab_PartialFixpointType_toCtorIdx(v_x_4__boxed_1177_);
    return v_res_1178_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_ctorElim___redArg(
    mut v_k_1179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1179_);
    return v_k_1179_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_ctorElim___redArg___boxed(
    mut v_k_1180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1181_ = l_Lean_Elab_PartialFixpointType_ctorElim___redArg(v_k_1180_);
    crate::leanh::lean_dec(v_k_1180_);
    return v_res_1181_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_ctorElim(
    mut v_motive_1182_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1183_: *mut crate::leanh::LeanObject,
    mut v_t_1184_: u8,
    mut v_h_1185_: *mut crate::leanh::LeanObject,
    mut v_k_1186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1186_);
    return v_k_1186_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_ctorElim___boxed(
    mut v_motive_1187_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1188_: *mut crate::leanh::LeanObject,
    mut v_t_1189_: *mut crate::leanh::LeanObject,
    mut v_h_1190_: *mut crate::leanh::LeanObject,
    mut v_k_1191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1192_: u8 = 0;
    let mut v_res_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1192_ = (crate::leanh::lean_unbox(v_t_1189_) as u8);
    v_res_1193_ = l_Lean_Elab_PartialFixpointType_ctorElim(
        v_motive_1187_,
        v_ctorIdx_1188_,
        v_t_boxed_1192_,
        v_h_1190_,
        v_k_1191_,
    );
    crate::leanh::lean_dec(v_k_1191_);
    crate::leanh::lean_dec(v_ctorIdx_1188_);
    return v_res_1193_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___redArg(
    mut v_partialFixpoint_1194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_partialFixpoint_1194_);
    return v_partialFixpoint_1194_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___redArg___boxed(
    mut v_partialFixpoint_1195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1196_ =
        l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___redArg(v_partialFixpoint_1195_);
    crate::leanh::lean_dec(v_partialFixpoint_1195_);
    return v_res_1196_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_partialFixpoint_elim(
    mut v_motive_1197_: *mut crate::leanh::LeanObject,
    mut v_t_1198_: u8,
    mut v_h_1199_: *mut crate::leanh::LeanObject,
    mut v_partialFixpoint_1200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_partialFixpoint_1200_);
    return v_partialFixpoint_1200_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___boxed(
    mut v_motive_1201_: *mut crate::leanh::LeanObject,
    mut v_t_1202_: *mut crate::leanh::LeanObject,
    mut v_h_1203_: *mut crate::leanh::LeanObject,
    mut v_partialFixpoint_1204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1205_: u8 = 0;
    let mut v_res_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1205_ = (crate::leanh::lean_unbox(v_t_1202_) as u8);
    v_res_1206_ = l_Lean_Elab_PartialFixpointType_partialFixpoint_elim(
        v_motive_1201_,
        v_t_boxed_1205_,
        v_h_1203_,
        v_partialFixpoint_1204_,
    );
    crate::leanh::lean_dec(v_partialFixpoint_1204_);
    return v_res_1206_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___redArg(
    mut v_coinductiveFixpoint_1207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_coinductiveFixpoint_1207_);
    return v_coinductiveFixpoint_1207_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___redArg___boxed(
    mut v_coinductiveFixpoint_1208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1209_ = l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___redArg(
        v_coinductiveFixpoint_1208_,
    );
    crate::leanh::lean_dec(v_coinductiveFixpoint_1208_);
    return v_res_1209_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim(
    mut v_motive_1210_: *mut crate::leanh::LeanObject,
    mut v_t_1211_: u8,
    mut v_h_1212_: *mut crate::leanh::LeanObject,
    mut v_coinductiveFixpoint_1213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_coinductiveFixpoint_1213_);
    return v_coinductiveFixpoint_1213_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___boxed(
    mut v_motive_1214_: *mut crate::leanh::LeanObject,
    mut v_t_1215_: *mut crate::leanh::LeanObject,
    mut v_h_1216_: *mut crate::leanh::LeanObject,
    mut v_coinductiveFixpoint_1217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1218_: u8 = 0;
    let mut v_res_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1218_ = (crate::leanh::lean_unbox(v_t_1215_) as u8);
    v_res_1219_ = l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim(
        v_motive_1214_,
        v_t_boxed_1218_,
        v_h_1216_,
        v_coinductiveFixpoint_1217_,
    );
    crate::leanh::lean_dec(v_coinductiveFixpoint_1217_);
    return v_res_1219_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___redArg(
    mut v_inductiveFixpoint_1220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inductiveFixpoint_1220_);
    return v_inductiveFixpoint_1220_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___redArg___boxed(
    mut v_inductiveFixpoint_1221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1222_ =
        l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___redArg(v_inductiveFixpoint_1221_);
    crate::leanh::lean_dec(v_inductiveFixpoint_1221_);
    return v_res_1222_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim(
    mut v_motive_1223_: *mut crate::leanh::LeanObject,
    mut v_t_1224_: u8,
    mut v_h_1225_: *mut crate::leanh::LeanObject,
    mut v_inductiveFixpoint_1226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inductiveFixpoint_1226_);
    return v_inductiveFixpoint_1226_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___boxed(
    mut v_motive_1227_: *mut crate::leanh::LeanObject,
    mut v_t_1228_: *mut crate::leanh::LeanObject,
    mut v_h_1229_: *mut crate::leanh::LeanObject,
    mut v_inductiveFixpoint_1230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1231_: u8 = 0;
    let mut v_res_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1231_ = (crate::leanh::lean_unbox(v_t_1228_) as u8);
    v_res_1232_ = l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim(
        v_motive_1227_,
        v_t_boxed_1231_,
        v_h_1229_,
        v_inductiveFixpoint_1230_,
    );
    crate::leanh::lean_dec(v_inductiveFixpoint_1230_);
    return v_res_1232_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedPartialFixpointType_default() -> u8 {
    let mut v___x_1233_: u8 = 0;
    v___x_1233_ = 0;
    return v___x_1233_;
}
pub unsafe fn _init_l_Lean_Elab_instInhabitedPartialFixpointType() -> u8 {
    let mut v___x_1234_: u8 = 0;
    v___x_1234_ = 0;
    return v___x_1234_;
}
pub unsafe fn l_Lean_Elab_isInductiveFixpoint(mut v_x_1247_: u8) -> u8 {
    if v_x_1247_ == 2 {
        let mut v___x_1248_: u8 = 0;
        v___x_1248_ = 1;
        return v___x_1248_;
    } else {
        let mut v___x_1249_: u8 = 0;
        v___x_1249_ = 0;
        return v___x_1249_;
    }
}
pub unsafe fn l_Lean_Elab_isInductiveFixpoint___boxed(
    mut v_x_1250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_21__boxed_1251_: u8 = 0;
    let mut v_res_1252_: u8 = 0;
    let mut v_r_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_21__boxed_1251_ = (crate::leanh::lean_unbox(v_x_1250_) as u8);
    v_res_1252_ = l_Lean_Elab_isInductiveFixpoint(v_x_21__boxed_1251_);
    v_r_1253_ = crate::leanh::lean_box((v_res_1252_) as usize);
    return v_r_1253_;
}
pub unsafe fn l_Lean_Elab_isCoinductiveFixpoint(mut v_x_1254_: u8) -> u8 {
    if v_x_1254_ == 1 {
        let mut v___x_1255_: u8 = 0;
        v___x_1255_ = 1;
        return v___x_1255_;
    } else {
        let mut v___x_1256_: u8 = 0;
        v___x_1256_ = 0;
        return v___x_1256_;
    }
}
pub unsafe fn l_Lean_Elab_isCoinductiveFixpoint___boxed(
    mut v_x_1257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_21__boxed_1258_: u8 = 0;
    let mut v_res_1259_: u8 = 0;
    let mut v_r_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_21__boxed_1258_ = (crate::leanh::lean_unbox(v_x_1257_) as u8);
    v_res_1259_ = l_Lean_Elab_isCoinductiveFixpoint(v_x_21__boxed_1258_);
    v_r_1260_ = crate::leanh::lean_box((v_res_1259_) as usize);
    return v_r_1260_;
}
pub unsafe fn l_Lean_Elab_isPartialFixpoint(mut v_x_1261_: u8) -> u8 {
    if v_x_1261_ == 0 {
        let mut v___x_1262_: u8 = 0;
        v___x_1262_ = 1;
        return v___x_1262_;
    } else {
        let mut v___x_1263_: u8 = 0;
        v___x_1263_ = 0;
        return v___x_1263_;
    }
}
pub unsafe fn l_Lean_Elab_isPartialFixpoint___boxed(
    mut v_x_1264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_21__boxed_1265_: u8 = 0;
    let mut v_res_1266_: u8 = 0;
    let mut v_r_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_21__boxed_1265_ = (crate::leanh::lean_unbox(v_x_1264_) as u8);
    v_res_1266_ = l_Lean_Elab_isPartialFixpoint(v_x_21__boxed_1265_);
    v_r_1267_ = crate::leanh::lean_box((v_res_1266_) as usize);
    return v_r_1267_;
}
pub unsafe fn l_Lean_Elab_isLatticeTheoretic(mut v_p_1268_: u8) -> u8 {
    let mut v___x_1269_: u8 = 0;
    v___x_1269_ = l_Lean_Elab_isInductiveFixpoint(v_p_1268_);
    if v___x_1269_ == 0 {
        let mut v___x_1270_: u8 = 0;
        v___x_1270_ = l_Lean_Elab_isCoinductiveFixpoint(v_p_1268_);
        return v___x_1270_;
    } else {
        return v___x_1269_;
    }
}
pub unsafe fn l_Lean_Elab_isLatticeTheoretic___boxed(
    mut v_p_1271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_boxed_1272_: u8 = 0;
    let mut v_res_1273_: u8 = 0;
    let mut v_r_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_p_boxed_1272_ = (crate::leanh::lean_unbox(v_p_1271_) as u8);
    v_res_1273_ = l_Lean_Elab_isLatticeTheoretic(v_p_boxed_1272_);
    v_r_1274_ = crate::leanh::lean_box((v_res_1273_) as usize);
    return v_r_1274_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1276_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1276_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1277_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0);
    v___x_1278_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1278_, 0, v___x_1277_);
    return v___x_1278_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1279_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1);
    v___x_1280_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1281_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1281_, 0, v___x_1280_);
    crate::leanh::lean_ctor_set(v___x_1281_, 1, v___x_1280_);
    crate::leanh::lean_ctor_set(v___x_1281_, 2, v___x_1280_);
    crate::leanh::lean_ctor_set(v___x_1281_, 3, v___x_1280_);
    crate::leanh::lean_ctor_set(v___x_1281_, 4, v___x_1279_);
    crate::leanh::lean_ctor_set(v___x_1281_, 5, v___x_1279_);
    crate::leanh::lean_ctor_set(v___x_1281_, 6, v___x_1279_);
    crate::leanh::lean_ctor_set(v___x_1281_, 7, v___x_1279_);
    crate::leanh::lean_ctor_set(v___x_1281_, 8, v___x_1279_);
    crate::leanh::lean_ctor_set(v___x_1281_, 9, v___x_1279_);
    return v___x_1281_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1282_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1283_ = lean_mk_empty_array_with_capacity(v___x_1282_);
    v___x_1284_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1284_, 0, v___x_1283_);
    return v___x_1284_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1285_: usize = 0;
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1285_ = 5usize;
    v___x_1286_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1287_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1288_ = lean_mk_empty_array_with_capacity(v___x_1287_);
    v___x_1289_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3);
    v___x_1290_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1290_, 0, v___x_1289_);
    crate::leanh::lean_ctor_set(v___x_1290_, 1, v___x_1288_);
    crate::leanh::lean_ctor_set(v___x_1290_, 2, v___x_1286_);
    crate::leanh::lean_ctor_set(v___x_1290_, 3, v___x_1286_);
    crate::leanh::lean_ctor_set_usize(v___x_1290_, 4, v___x_1285_);
    return v___x_1290_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1291_ = crate::leanh::lean_box(1);
    v___x_1292_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4);
    v___x_1293_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1);
    v___x_1294_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1294_, 0, v___x_1293_);
    crate::leanh::lean_ctor_set(v___x_1294_, 1, v___x_1292_);
    crate::leanh::lean_ctor_set(v___x_1294_, 2, v___x_1291_);
    return v___x_1294_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(
    mut v_msgData_1295_: *mut crate::leanh::LeanObject,
    mut v___y_1296_: *mut crate::leanh::LeanObject,
    mut v___y_1297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1299_ = lean_st_ref_get(v___y_1297_);
    v_env_1300_ = crate::leanh::lean_ctor_get(v___x_1299_, 0);
    crate::leanh::lean_inc_ref(v_env_1300_);
    crate::leanh::lean_dec(v___x_1299_);
    v_options_1301_ = crate::leanh::lean_ctor_get(v___y_1296_, 2);
    v___x_1302_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2);
    v___x_1303_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5);
    crate::leanh::lean_inc_ref(v_options_1301_);
    v___x_1304_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1304_, 0, v_env_1300_);
    crate::leanh::lean_ctor_set(v___x_1304_, 1, v___x_1302_);
    crate::leanh::lean_ctor_set(v___x_1304_, 2, v___x_1303_);
    crate::leanh::lean_ctor_set(v___x_1304_, 3, v_options_1301_);
    v___x_1305_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1305_, 0, v___x_1304_);
    crate::leanh::lean_ctor_set(v___x_1305_, 1, v_msgData_1295_);
    v___x_1306_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1306_, 0, v___x_1305_);
    return v___x_1306_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_1307_: *mut crate::leanh::LeanObject,
    mut v___y_1308_: *mut crate::leanh::LeanObject,
    mut v___y_1309_: *mut crate::leanh::LeanObject,
    mut v___y_1310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1311_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(v_msgData_1307_, v___y_1308_, v___y_1309_);
    crate::leanh::lean_dec(v___y_1309_);
    crate::leanh::lean_dec_ref(v___y_1308_);
    return v_res_1311_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0(
    mut v___y_1320_: u8,
    mut v_suppressElabErrors_1321_: u8,
    mut v_x_1322_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1322_) == 1 {
        let mut v_pre_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_1323_ = crate::leanh::lean_ctor_get(v_x_1322_, 0);
        match crate::leanh::lean_obj_tag(v_pre_1323_) {
            1 => {
                let mut v_pre_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_1324_ = crate::leanh::lean_ctor_get(v_pre_1323_, 0);
                match crate::leanh::lean_obj_tag(v_pre_1324_) {
                    0 => {
                        let mut v_str_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1328_: u8 = 0;
                        v_str_1325_ = crate::leanh::lean_ctor_get(v_x_1322_, 1);
                        v_str_1326_ = crate::leanh::lean_ctor_get(v_pre_1323_, 1);
                        v___x_1327_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__0;
                        v___x_1328_ = lean_string_dec_eq(v_str_1326_, v___x_1327_);
                        if v___x_1328_ == 0 {
                            let mut v___x_1329_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1330_: u8 = 0;
                            v___x_1329_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__1;
                            v___x_1330_ = lean_string_dec_eq(v_str_1326_, v___x_1329_);
                            if v___x_1330_ == 0 {
                                return v___y_1320_;
                            } else {
                                let mut v___x_1331_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1332_: u8 = 0;
                                v___x_1331_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__2;
                                v___x_1332_ = lean_string_dec_eq(v_str_1325_, v___x_1331_);
                                if v___x_1332_ == 0 {
                                    return v___y_1320_;
                                } else {
                                    return v_suppressElabErrors_1321_;
                                }
                            }
                        } else {
                            let mut v___x_1333_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1334_: u8 = 0;
                            v___x_1333_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__3;
                            v___x_1334_ = lean_string_dec_eq(v_str_1325_, v___x_1333_);
                            if v___x_1334_ == 0 {
                                return v___y_1320_;
                            } else {
                                return v_suppressElabErrors_1321_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_1335_ = crate::leanh::lean_ctor_get(v_pre_1324_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_1335_) == 0 {
                            let mut v_str_1336_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_1337_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_1338_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1339_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1340_: u8 = 0;
                            v_str_1336_ = crate::leanh::lean_ctor_get(v_x_1322_, 1);
                            v_str_1337_ = crate::leanh::lean_ctor_get(v_pre_1323_, 1);
                            v_str_1338_ = crate::leanh::lean_ctor_get(v_pre_1324_, 1);
                            v___x_1339_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__4;
                            v___x_1340_ = lean_string_dec_eq(v_str_1338_, v___x_1339_);
                            if v___x_1340_ == 0 {
                                return v___y_1320_;
                            } else {
                                let mut v___x_1341_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1342_: u8 = 0;
                                v___x_1341_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__5;
                                v___x_1342_ = lean_string_dec_eq(v_str_1337_, v___x_1341_);
                                if v___x_1342_ == 0 {
                                    return v___y_1320_;
                                } else {
                                    let mut v___x_1343_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1344_: u8 = 0;
                                    v___x_1343_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__6;
                                    v___x_1344_ = lean_string_dec_eq(v_str_1336_, v___x_1343_);
                                    if v___x_1344_ == 0 {
                                        return v___y_1320_;
                                    } else {
                                        return v_suppressElabErrors_1321_;
                                    }
                                }
                            }
                        } else {
                            return v___y_1320_;
                        }
                    }
                    _ => {
                        return v___y_1320_;
                    }
                }
            }
            0 => {
                let mut v_str_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1347_: u8 = 0;
                v_str_1345_ = crate::leanh::lean_ctor_get(v_x_1322_, 1);
                v___x_1346_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__7;
                v___x_1347_ = lean_string_dec_eq(v_str_1345_, v___x_1346_);
                if v___x_1347_ == 0 {
                    return v___y_1320_;
                } else {
                    return v_suppressElabErrors_1321_;
                }
            }
            _ => {
                return v___y_1320_;
            }
        }
    } else {
        return v___y_1320_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___boxed(
    mut v___y_1348_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_1349_: *mut crate::leanh::LeanObject,
    mut v_x_1350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3124__boxed_1351_: u8 = 0;
    let mut v_suppressElabErrors_boxed_1352_: u8 = 0;
    let mut v_res_1353_: u8 = 0;
    let mut v_r_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_3124__boxed_1351_ = (crate::leanh::lean_unbox(v___y_1348_) as u8);
    v_suppressElabErrors_boxed_1352_ = (crate::leanh::lean_unbox(v_suppressElabErrors_1349_) as u8);
    v_res_1353_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0(v___y_3124__boxed_1351_, v_suppressElabErrors_boxed_1352_, v_x_1350_);
    crate::leanh::lean_dec(v_x_1350_);
    v_r_1354_ = crate::leanh::lean_box((v_res_1353_) as usize);
    return v_r_1354_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(
    mut v_opts_1355_: *mut crate::leanh::LeanObject,
    mut v_opt_1356_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1357_ = crate::leanh::lean_ctor_get(v_opt_1356_, 0);
    v_defValue_1358_ = crate::leanh::lean_ctor_get(v_opt_1356_, 1);
    v_map_1359_ = crate::leanh::lean_ctor_get(v_opts_1355_, 0);
    v___x_1360_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1359_,
            v_name_1357_,
        );
    if crate::leanh::lean_obj_tag(v___x_1360_) == 0 {
        let mut v___x_1361_: u8 = 0;
        v___x_1361_ = (crate::leanh::lean_unbox(v_defValue_1358_) as u8);
        return v___x_1361_;
    } else {
        let mut v_val_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1362_ = crate::leanh::lean_ctor_get(v___x_1360_, 0);
        crate::leanh::lean_inc(v_val_1362_);
        crate::leanh::lean_dec_ref_known(v___x_1360_, 1);
        if crate::leanh::lean_obj_tag(v_val_1362_) == 1 {
            let mut v_v_1363_: u8 = 0;
            v_v_1363_ = crate::leanh::lean_ctor_get_uint8(v_val_1362_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_1362_, 0);
            return v_v_1363_;
        } else {
            let mut v___x_1364_: u8 = 0;
            crate::leanh::lean_dec(v_val_1362_);
            v___x_1364_ = (crate::leanh::lean_unbox(v_defValue_1358_) as u8);
            return v___x_1364_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2___boxed(
    mut v_opts_1365_: *mut crate::leanh::LeanObject,
    mut v_opt_1366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1367_: u8 = 0;
    let mut v_r_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1367_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(v_opts_1365_, v_opt_1366_);
    crate::leanh::lean_dec_ref(v_opt_1366_);
    crate::leanh::lean_dec_ref(v_opts_1365_);
    v_r_1368_ = crate::leanh::lean_box((v_res_1367_) as usize);
    return v_r_1368_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(
    mut v_ref_1370_: *mut crate::leanh::LeanObject,
    mut v_msgData_1371_: *mut crate::leanh::LeanObject,
    mut v_severity_1372_: u8,
    mut v_isSilent_1373_: u8,
    mut v___y_1374_: *mut crate::leanh::LeanObject,
    mut v___y_1375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1378_: u8 = 0;
    let mut v___y_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1384_: u8 = 0;
    let mut v___y_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1401_: u8 = 0;
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1412_: u8 = 0;
    let mut v___y_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1415_: u8 = 0;
    let mut v___y_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1418_: u8 = 0;
    let mut v___y_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1420_: u8 = 0;
    let mut v___y_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1427_: u8 = 0;
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: u8 = 0;
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1437_: u8 = 0;
    let mut v___y_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1440_: u8 = 0;
    let mut v___y_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1444_: u8 = 0;
    let mut v___y_1445_: u8 = 0;
    let mut v___y_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1451_: u8 = 0;
    let mut v___y_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1455_: u8 = 0;
    let mut v___y_1456_: u8 = 0;
    let mut v_ref_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: u8 = 0;
    let mut v___y_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1467_: u8 = 0;
    let mut v___y_1468_: u8 = 0;
    let mut v___y_1469_: u8 = 0;
    let mut v___y_1471_: u8 = 0;
    let mut v_fileName_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1476_: u8 = 0;
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: u8 = 0;
    let mut v___x_1481_: u8 = 0;
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: u8 = 0;
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: u8 = 0;
    let mut v___x_1487_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1461_ = 2;
                v___x_1486_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1372_, v___x_1461_);
                if v___x_1486_ == 0 {
                    v___y_1471_ = v___x_1486_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_1371_);
                    v___x_1487_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1371_);
                    v___y_1471_ = v___x_1487_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_1387_ = lean_st_ref_take(v___y_1386_);
                v_currNamespace_1388_ = crate::leanh::lean_ctor_get(v___y_1385_, 6);
                v_openDecls_1389_ = crate::leanh::lean_ctor_get(v___y_1385_, 7);
                v_env_1390_ = crate::leanh::lean_ctor_get(v___x_1387_, 0);
                v_nextMacroScope_1391_ = crate::leanh::lean_ctor_get(v___x_1387_, 1);
                v_ngen_1392_ = crate::leanh::lean_ctor_get(v___x_1387_, 2);
                v_auxDeclNGen_1393_ = crate::leanh::lean_ctor_get(v___x_1387_, 3);
                v_traceState_1394_ = crate::leanh::lean_ctor_get(v___x_1387_, 4);
                v_cache_1395_ = crate::leanh::lean_ctor_get(v___x_1387_, 5);
                v_messages_1396_ = crate::leanh::lean_ctor_get(v___x_1387_, 6);
                v_infoState_1397_ = crate::leanh::lean_ctor_get(v___x_1387_, 7);
                v_snapshotTasks_1398_ = crate::leanh::lean_ctor_get(v___x_1387_, 8);
                v_isSharedCheck_1412_ = (!crate::leanh::lean_is_exclusive(v___x_1387_)) as u8;
                if v_isSharedCheck_1412_ == 0 {
                    v___x_1400_ = v___x_1387_;
                    v_isShared_1401_ = v_isSharedCheck_1412_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1398_);
                    crate::leanh::lean_inc(v_infoState_1397_);
                    crate::leanh::lean_inc(v_messages_1396_);
                    crate::leanh::lean_inc(v_cache_1395_);
                    crate::leanh::lean_inc(v_traceState_1394_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1393_);
                    crate::leanh::lean_inc(v_ngen_1392_);
                    crate::leanh::lean_inc(v_nextMacroScope_1391_);
                    crate::leanh::lean_inc(v_env_1390_);
                    crate::leanh::lean_dec(v___x_1387_);
                    v___x_1400_ = crate::leanh::lean_box(0);
                    v_isShared_1401_ = v_isSharedCheck_1412_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_1389_);
                crate::leanh::lean_inc(v_currNamespace_1388_);
                v___x_1402_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1402_, 0, v_currNamespace_1388_);
                crate::leanh::lean_ctor_set(v___x_1402_, 1, v_openDecls_1389_);
                v___x_1403_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1403_, 0, v___x_1402_);
                crate::leanh::lean_ctor_set(v___x_1403_, 1, v___y_1383_);
                crate::leanh::lean_inc_ref(v___y_1382_);
                crate::leanh::lean_inc_ref(v___y_1379_);
                v___x_1404_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_1404_, 0, v___y_1379_);
                crate::leanh::lean_ctor_set(v___x_1404_, 1, v___y_1380_);
                crate::leanh::lean_ctor_set(v___x_1404_, 2, v___y_1381_);
                crate::leanh::lean_ctor_set(v___x_1404_, 3, v___y_1382_);
                crate::leanh::lean_ctor_set(v___x_1404_, 4, v___x_1403_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1404_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_1378_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1404_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_1384_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1404_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_1373_,
                );
                v___x_1405_ = l_Lean_MessageLog_add(v___x_1404_, v_messages_1396_);
                if v_isShared_1401_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1400_, 6, v___x_1405_);
                    v___x_1407_ = v___x_1400_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1411_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_env_1390_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_nextMacroScope_1391_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1411_, 2, v_ngen_1392_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1411_, 3, v_auxDeclNGen_1393_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1411_, 4, v_traceState_1394_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1411_, 5, v_cache_1395_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1411_, 6, v___x_1405_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1411_, 7, v_infoState_1397_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1411_, 8, v_snapshotTasks_1398_);
                    v___x_1407_ = v_reuseFailAlloc_1411_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1408_ = lean_st_ref_set(v___y_1386_, v___x_1407_);
                v___x_1409_ = crate::leanh::lean_box(0);
                v___x_1410_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1410_, 0, v___x_1409_);
                return v___x_1410_;
            }
            4 => {
                v___x_1422_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_1371_,
                    );
                v___x_1423_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(v___x_1422_, v___y_1374_, v___y_1375_);
                v_a_1424_ = crate::leanh::lean_ctor_get(v___x_1423_, 0);
                v_isSharedCheck_1437_ = (!crate::leanh::lean_is_exclusive(v___x_1423_)) as u8;
                if v_isSharedCheck_1437_ == 0 {
                    v___x_1426_ = v___x_1423_;
                    v_isShared_1427_ = v_isSharedCheck_1437_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1424_);
                    crate::leanh::lean_dec(v___x_1423_);
                    v___x_1426_ = crate::leanh::lean_box(0);
                    v_isShared_1427_ = v_isSharedCheck_1437_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_1416_, 2);
                v___x_1428_ = l_Lean_FileMap_toPosition(v___y_1416_, v___y_1419_);
                crate::leanh::lean_dec(v___y_1419_);
                v___x_1429_ = l_Lean_FileMap_toPosition(v___y_1416_, v___y_1421_);
                crate::leanh::lean_dec(v___y_1421_);
                v___x_1430_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1430_, 0, v___x_1429_);
                v___x_1431_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___closed__0;
                if v___y_1418_ == 0 {
                    crate::leanh::lean_del_object(v___x_1426_);
                    crate::leanh::lean_dec_ref(v___y_1414_);
                    v___y_1378_ = v___y_1415_;
                    v___y_1379_ = v___y_1417_;
                    v___y_1380_ = v___x_1428_;
                    v___y_1381_ = v___x_1430_;
                    v___y_1382_ = v___x_1431_;
                    v___y_1383_ = v_a_1424_;
                    v___y_1384_ = v___y_1420_;
                    v___y_1385_ = v___y_1374_;
                    v___y_1386_ = v___y_1375_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1424_);
                    v___x_1432_ = l_Lean_MessageData_hasTag(v___y_1414_, v_a_1424_);
                    if v___x_1432_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1430_, 1);
                        crate::leanh::lean_dec_ref(v___x_1428_);
                        crate::leanh::lean_dec(v_a_1424_);
                        v___x_1433_ = crate::leanh::lean_box(0);
                        if v_isShared_1427_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1426_, 0, v___x_1433_);
                            v___x_1435_ = v___x_1426_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_1436_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1433_);
                            v___x_1435_ = v_reuseFailAlloc_1436_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1426_);
                        v___y_1378_ = v___y_1415_;
                        v___y_1379_ = v___y_1417_;
                        v___y_1380_ = v___x_1428_;
                        v___y_1381_ = v___x_1430_;
                        v___y_1382_ = v___x_1431_;
                        v___y_1383_ = v_a_1424_;
                        v___y_1384_ = v___y_1420_;
                        v___y_1385_ = v___y_1374_;
                        v___y_1386_ = v___y_1375_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_1435_;
            }
            7 => {
                v___x_1447_ = l_Lean_Syntax_getTailPos_x3f(v___y_1443_, v___y_1440_);
                crate::leanh::lean_dec(v___y_1443_);
                if crate::leanh::lean_obj_tag(v___x_1447_) == 0 {
                    crate::leanh::lean_inc(v___y_1446_);
                    v___y_1414_ = v___y_1439_;
                    v___y_1415_ = v___y_1440_;
                    v___y_1416_ = v___y_1441_;
                    v___y_1417_ = v___y_1442_;
                    v___y_1418_ = v___y_1444_;
                    v___y_1419_ = v___y_1446_;
                    v___y_1420_ = v___y_1445_;
                    v___y_1421_ = v___y_1446_;
                    state = 4;
                    continue;
                } else {
                    v_val_1448_ = crate::leanh::lean_ctor_get(v___x_1447_, 0);
                    crate::leanh::lean_inc(v_val_1448_);
                    crate::leanh::lean_dec_ref_known(v___x_1447_, 1);
                    v___y_1414_ = v___y_1439_;
                    v___y_1415_ = v___y_1440_;
                    v___y_1416_ = v___y_1441_;
                    v___y_1417_ = v___y_1442_;
                    v___y_1418_ = v___y_1444_;
                    v___y_1419_ = v___y_1446_;
                    v___y_1420_ = v___y_1445_;
                    v___y_1421_ = v_val_1448_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_1457_ = l_Lean_replaceRef(v_ref_1370_, v___y_1452_);
                v___x_1458_ = l_Lean_Syntax_getPos_x3f(v_ref_1457_, v___y_1451_);
                if crate::leanh::lean_obj_tag(v___x_1458_) == 0 {
                    v___x_1459_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1439_ = v___y_1450_;
                    v___y_1440_ = v___y_1451_;
                    v___y_1441_ = v___y_1453_;
                    v___y_1442_ = v___y_1454_;
                    v___y_1443_ = v_ref_1457_;
                    v___y_1444_ = v___y_1455_;
                    v___y_1445_ = v___y_1456_;
                    v___y_1446_ = v___x_1459_;
                    state = 7;
                    continue;
                } else {
                    v_val_1460_ = crate::leanh::lean_ctor_get(v___x_1458_, 0);
                    crate::leanh::lean_inc(v_val_1460_);
                    crate::leanh::lean_dec_ref_known(v___x_1458_, 1);
                    v___y_1439_ = v___y_1450_;
                    v___y_1440_ = v___y_1451_;
                    v___y_1441_ = v___y_1453_;
                    v___y_1442_ = v___y_1454_;
                    v___y_1443_ = v_ref_1457_;
                    v___y_1444_ = v___y_1455_;
                    v___y_1445_ = v___y_1456_;
                    v___y_1446_ = v_val_1460_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_1469_ == 0 {
                    v___y_1450_ = v___y_1466_;
                    v___y_1451_ = v___y_1468_;
                    v___y_1452_ = v___y_1463_;
                    v___y_1453_ = v___y_1464_;
                    v___y_1454_ = v___y_1465_;
                    v___y_1455_ = v___y_1467_;
                    v___y_1456_ = v_severity_1372_;
                    state = 8;
                    continue;
                } else {
                    v___y_1450_ = v___y_1466_;
                    v___y_1451_ = v___y_1468_;
                    v___y_1452_ = v___y_1463_;
                    v___y_1453_ = v___y_1464_;
                    v___y_1454_ = v___y_1465_;
                    v___y_1455_ = v___y_1467_;
                    v___y_1456_ = v___x_1461_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_1471_ == 0 {
                    v_fileName_1472_ = crate::leanh::lean_ctor_get(v___y_1374_, 0);
                    v_fileMap_1473_ = crate::leanh::lean_ctor_get(v___y_1374_, 1);
                    v_options_1474_ = crate::leanh::lean_ctor_get(v___y_1374_, 2);
                    v_ref_1475_ = crate::leanh::lean_ctor_get(v___y_1374_, 5);
                    v_suppressElabErrors_1476_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_1374_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_1477_ = crate::leanh::lean_box((v___y_1471_) as usize);
                    v___x_1478_ = crate::leanh::lean_box((v_suppressElabErrors_1476_) as usize);
                    v___f_1479_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_1479_, 0, v___x_1477_);
                    crate::leanh::lean_closure_set(v___f_1479_, 1, v___x_1478_);
                    v___x_1480_ = 1;
                    v___x_1481_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1372_, v___x_1480_);
                    if v___x_1481_ == 0 {
                        v___y_1463_ = v_ref_1475_;
                        v___y_1464_ = v_fileMap_1473_;
                        v___y_1465_ = v_fileName_1472_;
                        v___y_1466_ = v___f_1479_;
                        v___y_1467_ = v_suppressElabErrors_1476_;
                        v___y_1468_ = v___y_1471_;
                        v___y_1469_ = v___x_1481_;
                        state = 9;
                        continue;
                    } else {
                        v___x_1482_ = l_Lean_warningAsError;
                        v___x_1483_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(v_options_1474_, v___x_1482_);
                        v___y_1463_ = v_ref_1475_;
                        v___y_1464_ = v_fileMap_1473_;
                        v___y_1465_ = v_fileName_1472_;
                        v___y_1466_ = v___f_1479_;
                        v___y_1467_ = v_suppressElabErrors_1476_;
                        v___y_1468_ = v___y_1471_;
                        v___y_1469_ = v___x_1483_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_1371_);
                    v___x_1484_ = crate::leanh::lean_box(0);
                    v___x_1485_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1485_, 0, v___x_1484_);
                    return v___x_1485_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___boxed(
    mut v_ref_1488_: *mut crate::leanh::LeanObject,
    mut v_msgData_1489_: *mut crate::leanh::LeanObject,
    mut v_severity_1490_: *mut crate::leanh::LeanObject,
    mut v_isSilent_1491_: *mut crate::leanh::LeanObject,
    mut v___y_1492_: *mut crate::leanh::LeanObject,
    mut v___y_1493_: *mut crate::leanh::LeanObject,
    mut v___y_1494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_1495_: u8 = 0;
    let mut v_isSilent_boxed_1496_: u8 = 0;
    let mut v_res_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_1495_ = (crate::leanh::lean_unbox(v_severity_1490_) as u8);
    v_isSilent_boxed_1496_ = (crate::leanh::lean_unbox(v_isSilent_1491_) as u8);
    v_res_1497_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(v_ref_1488_, v_msgData_1489_, v_severity_boxed_1495_, v_isSilent_boxed_1496_, v___y_1492_, v___y_1493_);
    crate::leanh::lean_dec(v___y_1493_);
    crate::leanh::lean_dec_ref(v___y_1492_);
    crate::leanh::lean_dec(v_ref_1488_);
    return v_res_1497_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(
    mut v_ref_1498_: *mut crate::leanh::LeanObject,
    mut v_msgData_1499_: *mut crate::leanh::LeanObject,
    mut v___y_1500_: *mut crate::leanh::LeanObject,
    mut v___y_1501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1503_: u8 = 0;
    let mut v___x_1504_: u8 = 0;
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1503_ = 1;
    v___x_1504_ = 0;
    v___x_1505_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(v_ref_1498_, v_msgData_1499_, v___x_1503_, v___x_1504_, v___y_1500_, v___y_1501_);
    return v___x_1505_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0___boxed(
    mut v_ref_1506_: *mut crate::leanh::LeanObject,
    mut v_msgData_1507_: *mut crate::leanh::LeanObject,
    mut v___y_1508_: *mut crate::leanh::LeanObject,
    mut v___y_1509_: *mut crate::leanh::LeanObject,
    mut v___y_1510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1511_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(
        v_ref_1506_,
        v_msgData_1507_,
        v___y_1508_,
        v___y_1509_,
    );
    crate::leanh::lean_dec(v___y_1509_);
    crate::leanh::lean_dec_ref(v___y_1508_);
    crate::leanh::lean_dec(v_ref_1506_);
    return v_res_1511_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationHints_ensureNone___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1513_ = l_Lean_Elab_TerminationHints_ensureNone___closed__0;
    v___x_1514_ = l_Lean_stringToMessageData(v___x_1513_);
    return v___x_1514_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationHints_ensureNone___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1516_ = l_Lean_Elab_TerminationHints_ensureNone___closed__2;
    v___x_1517_ = l_Lean_stringToMessageData(v___x_1516_);
    return v___x_1517_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationHints_ensureNone___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1519_ = l_Lean_Elab_TerminationHints_ensureNone___closed__4;
    v___x_1520_ = l_Lean_stringToMessageData(v___x_1519_);
    return v___x_1520_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationHints_ensureNone___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1522_ = l_Lean_Elab_TerminationHints_ensureNone___closed__6;
    v___x_1523_ = l_Lean_stringToMessageData(v___x_1522_);
    return v___x_1523_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationHints_ensureNone___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1525_ = l_Lean_Elab_TerminationHints_ensureNone___closed__8;
    v___x_1526_ = l_Lean_stringToMessageData(v___x_1525_);
    return v___x_1526_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationHints_ensureNone___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1528_ = l_Lean_Elab_TerminationHints_ensureNone___closed__10;
    v___x_1529_ = l_Lean_stringToMessageData(v___x_1528_);
    return v___x_1529_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationHints_ensureNone___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1531_ = l_Lean_Elab_TerminationHints_ensureNone___closed__12;
    v___x_1532_ = l_Lean_stringToMessageData(v___x_1531_);
    return v___x_1532_;
}
pub unsafe fn l_Lean_Elab_TerminationHints_ensureNone(
    mut v_hints_1533_: *mut crate::leanh::LeanObject,
    mut v_reason_1534_: *mut crate::leanh::LeanObject,
    mut v_a_1535_: *mut crate::leanh::LeanObject,
    mut v_a_1536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_terminationBy_x3f_x3f_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_terminationBy_x3f_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_partialFixpoint_x3f_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decreasingBy_x3f_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fixpointType_1553_: u8 = 0;
    let mut v_ref_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1573_: u8 = 0;
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1580_: u8 = 0;
    let mut v_unused_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1538_ = crate::leanh::lean_ctor_get(v_hints_1533_, 0);
                crate::leanh::lean_inc(v_ref_1538_);
                v_terminationBy_x3f_x3f_1539_ = crate::leanh::lean_ctor_get(v_hints_1533_, 1);
                crate::leanh::lean_inc(v_terminationBy_x3f_x3f_1539_);
                v_terminationBy_x3f_1540_ = crate::leanh::lean_ctor_get(v_hints_1533_, 2);
                crate::leanh::lean_inc(v_terminationBy_x3f_1540_);
                v_partialFixpoint_x3f_1541_ = crate::leanh::lean_ctor_get(v_hints_1533_, 3);
                crate::leanh::lean_inc(v_partialFixpoint_x3f_1541_);
                v_decreasingBy_x3f_1542_ = crate::leanh::lean_ctor_get(v_hints_1533_, 4);
                crate::leanh::lean_inc(v_decreasingBy_x3f_1542_);
                crate::leanh::lean_dec_ref(v_hints_1533_);
                if crate::leanh::lean_obj_tag(v_terminationBy_x3f_x3f_1539_) == 0 {
                    if crate::leanh::lean_obj_tag(v_terminationBy_x3f_1540_) == 0 {
                        if crate::leanh::lean_obj_tag(v_decreasingBy_x3f_1542_) == 0 {
                            crate::leanh::lean_dec(v_ref_1538_);
                            if crate::leanh::lean_obj_tag(v_partialFixpoint_x3f_1541_) == 0 {
                                crate::leanh::lean_dec_ref(v_reason_1534_);
                                v___x_1550_ = crate::leanh::lean_box(0);
                                v___x_1551_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1551_, 0, v___x_1550_);
                                return v___x_1551_;
                            } else {
                                v_val_1552_ =
                                    crate::leanh::lean_ctor_get(v_partialFixpoint_x3f_1541_, 0);
                                crate::leanh::lean_inc(v_val_1552_);
                                crate::leanh::lean_dec_ref_known(v_partialFixpoint_x3f_1541_, 1);
                                v_fixpointType_1553_ = crate::leanh::lean_ctor_get_uint8(
                                    v_val_1552_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2)
                                        as u32,
                                );
                                match v_fixpointType_1553_ {
                                    0 => {
                                        v_ref_1554_ = crate::leanh::lean_ctor_get(v_val_1552_, 0);
                                        crate::leanh::lean_inc(v_ref_1554_);
                                        crate::leanh::lean_dec(v_val_1552_);
                                        v___x_1555_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_TerminationHints_ensureNone___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_TerminationHints_ensureNone___closed__3_once), _init_l_Lean_Elab_TerminationHints_ensureNone___closed__3);
                                        v___x_1556_ = l_Lean_stringToMessageData(v_reason_1534_);
                                        v___x_1557_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_1557_, 0, v___x_1555_);
                                        crate::leanh::lean_ctor_set(v___x_1557_, 1, v___x_1556_);
                                        v___x_1558_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_1554_, v___x_1557_, v_a_1535_, v_a_1536_);
                                        crate::leanh::lean_dec(v_ref_1554_);
                                        return v___x_1558_;
                                    }
                                    1 => {
                                        v_ref_1559_ = crate::leanh::lean_ctor_get(v_val_1552_, 0);
                                        crate::leanh::lean_inc(v_ref_1559_);
                                        crate::leanh::lean_dec(v_val_1552_);
                                        v___x_1560_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_TerminationHints_ensureNone___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_TerminationHints_ensureNone___closed__5_once), _init_l_Lean_Elab_TerminationHints_ensureNone___closed__5);
                                        v___x_1561_ = l_Lean_stringToMessageData(v_reason_1534_);
                                        v___x_1562_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_1562_, 0, v___x_1560_);
                                        crate::leanh::lean_ctor_set(v___x_1562_, 1, v___x_1561_);
                                        v___x_1563_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_1559_, v___x_1562_, v_a_1535_, v_a_1536_);
                                        crate::leanh::lean_dec(v_ref_1559_);
                                        return v___x_1563_;
                                    }
                                    _ => {
                                        v_ref_1564_ = crate::leanh::lean_ctor_get(v_val_1552_, 0);
                                        crate::leanh::lean_inc(v_ref_1564_);
                                        crate::leanh::lean_dec(v_val_1552_);
                                        v___x_1565_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_TerminationHints_ensureNone___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_TerminationHints_ensureNone___closed__7_once), _init_l_Lean_Elab_TerminationHints_ensureNone___closed__7);
                                        v___x_1566_ = l_Lean_stringToMessageData(v_reason_1534_);
                                        v___x_1567_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_1567_, 0, v___x_1565_);
                                        crate::leanh::lean_ctor_set(v___x_1567_, 1, v___x_1566_);
                                        v___x_1568_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_1564_, v___x_1567_, v_a_1535_, v_a_1536_);
                                        crate::leanh::lean_dec(v_ref_1564_);
                                        return v___x_1568_;
                                    }
                                }
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v_partialFixpoint_x3f_1541_) == 0 {
                                crate::leanh::lean_dec(v_ref_1538_);
                                v_val_1569_ =
                                    crate::leanh::lean_ctor_get(v_decreasingBy_x3f_1542_, 0);
                                crate::leanh::lean_inc(v_val_1569_);
                                crate::leanh::lean_dec_ref_known(v_decreasingBy_x3f_1542_, 1);
                                v_ref_1570_ = crate::leanh::lean_ctor_get(v_val_1569_, 0);
                                v_isSharedCheck_1580_ =
                                    (!crate::leanh::lean_is_exclusive(v_val_1569_)) as u8;
                                if v_isSharedCheck_1580_ == 0 {
                                    v_unused_1581_ = crate::leanh::lean_ctor_get(v_val_1569_, 1);
                                    crate::leanh::lean_dec(v_unused_1581_);
                                    v___x_1572_ = v_val_1569_;
                                    v_isShared_1573_ = v_isSharedCheck_1580_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_ref_1570_);
                                    crate::leanh::lean_dec(v_val_1569_);
                                    v___x_1572_ = crate::leanh::lean_box(0);
                                    v_isShared_1573_ = v_isSharedCheck_1580_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_decreasingBy_x3f_1542_, 1);
                                crate::leanh::lean_dec(v_partialFixpoint_x3f_1541_);
                                v___y_1544_ = v_a_1535_;
                                v___y_1545_ = v_a_1536_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v_decreasingBy_x3f_1542_) == 0 {
                            if crate::leanh::lean_obj_tag(v_partialFixpoint_x3f_1541_) == 0 {
                                crate::leanh::lean_dec(v_ref_1538_);
                                v_val_1582_ =
                                    crate::leanh::lean_ctor_get(v_terminationBy_x3f_1540_, 0);
                                crate::leanh::lean_inc(v_val_1582_);
                                crate::leanh::lean_dec_ref_known(v_terminationBy_x3f_1540_, 1);
                                v_ref_1583_ = crate::leanh::lean_ctor_get(v_val_1582_, 0);
                                crate::leanh::lean_inc(v_ref_1583_);
                                crate::leanh::lean_dec(v_val_1582_);
                                v___x_1584_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_TerminationHints_ensureNone___closed__11
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_TerminationHints_ensureNone___closed__11_once
                                    ),
                                    _init_l_Lean_Elab_TerminationHints_ensureNone___closed__11,
                                );
                                v___x_1585_ = l_Lean_stringToMessageData(v_reason_1534_);
                                v___x_1586_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1586_, 0, v___x_1584_);
                                crate::leanh::lean_ctor_set(v___x_1586_, 1, v___x_1585_);
                                v___x_1587_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_1583_, v___x_1586_, v_a_1535_, v_a_1536_);
                                crate::leanh::lean_dec(v_ref_1583_);
                                return v___x_1587_;
                            } else {
                                crate::leanh::lean_dec_ref_known(v_terminationBy_x3f_1540_, 1);
                                crate::leanh::lean_dec(v_partialFixpoint_x3f_1541_);
                                v___y_1544_ = v_a_1535_;
                                v___y_1545_ = v_a_1536_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_terminationBy_x3f_1540_, 1);
                            crate::leanh::lean_dec(v_decreasingBy_x3f_1542_);
                            crate::leanh::lean_dec(v_partialFixpoint_x3f_1541_);
                            v___y_1544_ = v_a_1535_;
                            v___y_1545_ = v_a_1536_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_terminationBy_x3f_1540_) == 0 {
                        if crate::leanh::lean_obj_tag(v_decreasingBy_x3f_1542_) == 0 {
                            if crate::leanh::lean_obj_tag(v_partialFixpoint_x3f_1541_) == 0 {
                                crate::leanh::lean_dec(v_ref_1538_);
                                v_val_1588_ =
                                    crate::leanh::lean_ctor_get(v_terminationBy_x3f_x3f_1539_, 0);
                                crate::leanh::lean_inc(v_val_1588_);
                                crate::leanh::lean_dec_ref_known(v_terminationBy_x3f_x3f_1539_, 1);
                                v___x_1589_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_TerminationHints_ensureNone___closed__13
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_TerminationHints_ensureNone___closed__13_once
                                    ),
                                    _init_l_Lean_Elab_TerminationHints_ensureNone___closed__13,
                                );
                                v___x_1590_ = l_Lean_stringToMessageData(v_reason_1534_);
                                v___x_1591_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1591_, 0, v___x_1589_);
                                crate::leanh::lean_ctor_set(v___x_1591_, 1, v___x_1590_);
                                v___x_1592_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_val_1588_, v___x_1591_, v_a_1535_, v_a_1536_);
                                crate::leanh::lean_dec(v_val_1588_);
                                return v___x_1592_;
                            } else {
                                crate::leanh::lean_dec_ref_known(v_terminationBy_x3f_x3f_1539_, 1);
                                crate::leanh::lean_dec(v_partialFixpoint_x3f_1541_);
                                v___y_1544_ = v_a_1535_;
                                v___y_1545_ = v_a_1536_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_terminationBy_x3f_x3f_1539_, 1);
                            crate::leanh::lean_dec(v_decreasingBy_x3f_1542_);
                            crate::leanh::lean_dec(v_partialFixpoint_x3f_1541_);
                            v___y_1544_ = v_a_1535_;
                            v___y_1545_ = v_a_1536_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_terminationBy_x3f_x3f_1539_, 1);
                        crate::leanh::lean_dec(v_decreasingBy_x3f_1542_);
                        crate::leanh::lean_dec(v_partialFixpoint_x3f_1541_);
                        crate::leanh::lean_dec(v_terminationBy_x3f_1540_);
                        v___y_1544_ = v_a_1535_;
                        v___y_1545_ = v_a_1536_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1546_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_TerminationHints_ensureNone___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_TerminationHints_ensureNone___closed__1_once
                    ),
                    _init_l_Lean_Elab_TerminationHints_ensureNone___closed__1,
                );
                v___x_1547_ = l_Lean_stringToMessageData(v_reason_1534_);
                v___x_1548_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1548_, 0, v___x_1546_);
                crate::leanh::lean_ctor_set(v___x_1548_, 1, v___x_1547_);
                v___x_1549_ =
                    l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(
                        v_ref_1538_,
                        v___x_1548_,
                        v___y_1544_,
                        v___y_1545_,
                    );
                crate::leanh::lean_dec(v_ref_1538_);
                return v___x_1549_;
            }
            2 => {
                v___x_1574_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_TerminationHints_ensureNone___closed__9),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_TerminationHints_ensureNone___closed__9_once
                    ),
                    _init_l_Lean_Elab_TerminationHints_ensureNone___closed__9,
                );
                v___x_1575_ = l_Lean_stringToMessageData(v_reason_1534_);
                if v_isShared_1573_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1572_, 7);
                    crate::leanh::lean_ctor_set(v___x_1572_, 1, v___x_1575_);
                    crate::leanh::lean_ctor_set(v___x_1572_, 0, v___x_1574_);
                    v___x_1577_ = v___x_1572_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1579_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1574_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1579_, 1, v___x_1575_);
                    v___x_1577_ = v_reuseFailAlloc_1579_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1578_ =
                    l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(
                        v_ref_1570_,
                        v___x_1577_,
                        v_a_1535_,
                        v_a_1536_,
                    );
                crate::leanh::lean_dec(v_ref_1570_);
                return v___x_1578_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_TerminationHints_ensureNone___boxed(
    mut v_hints_1593_: *mut crate::leanh::LeanObject,
    mut v_reason_1594_: *mut crate::leanh::LeanObject,
    mut v_a_1595_: *mut crate::leanh::LeanObject,
    mut v_a_1596_: *mut crate::leanh::LeanObject,
    mut v_a_1597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1598_ = l_Lean_Elab_TerminationHints_ensureNone(
        v_hints_1593_,
        v_reason_1594_,
        v_a_1595_,
        v_a_1596_,
    );
    crate::leanh::lean_dec(v_a_1596_);
    crate::leanh::lean_dec_ref(v_a_1595_);
    return v_res_1598_;
}
pub unsafe fn l_Lean_Elab_TerminationHints_isNotNone(
    mut v_hints_1599_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_terminationBy_x3f_x3f_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_terminationBy_x3f_x3f_1600_ = crate::leanh::lean_ctor_get(v_hints_1599_, 1);
    if crate::leanh::lean_obj_tag(v_terminationBy_x3f_x3f_1600_) == 0 {
        let mut v_terminationBy_x3f_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_terminationBy_x3f_1601_ = crate::leanh::lean_ctor_get(v_hints_1599_, 2);
        if crate::leanh::lean_obj_tag(v_terminationBy_x3f_1601_) == 0 {
            let mut v_decreasingBy_x3f_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_decreasingBy_x3f_1602_ = crate::leanh::lean_ctor_get(v_hints_1599_, 4);
            if crate::leanh::lean_obj_tag(v_decreasingBy_x3f_1602_) == 0 {
                let mut v_partialFixpoint_x3f_1603_: *mut crate::leanh::LeanObject =
                    core::ptr::null_mut();
                v_partialFixpoint_x3f_1603_ = crate::leanh::lean_ctor_get(v_hints_1599_, 3);
                if crate::leanh::lean_obj_tag(v_partialFixpoint_x3f_1603_) == 0 {
                    let mut v___x_1604_: u8 = 0;
                    v___x_1604_ = 0;
                    return v___x_1604_;
                } else {
                    let mut v___x_1605_: u8 = 0;
                    v___x_1605_ = 1;
                    return v___x_1605_;
                }
            } else {
                let mut v___x_1606_: u8 = 0;
                v___x_1606_ = 1;
                return v___x_1606_;
            }
        } else {
            let mut v___x_1607_: u8 = 0;
            v___x_1607_ = 1;
            return v___x_1607_;
        }
    } else {
        let mut v___x_1608_: u8 = 0;
        v___x_1608_ = 1;
        return v___x_1608_;
    }
}
pub unsafe fn l_Lean_Elab_TerminationHints_isNotNone___boxed(
    mut v_hints_1609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1610_: u8 = 0;
    let mut v_r_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1610_ = l_Lean_Elab_TerminationHints_isNotNone(v_hints_1609_);
    crate::leanh::lean_dec_ref(v_hints_1609_);
    v_r_1611_ = crate::leanh::lean_box((v_res_1610_) as usize);
    return v_r_1611_;
}
pub unsafe fn l_Lean_Elab_TerminationHints_rememberExtraParams(
    mut v_headerParams_1612_: *mut crate::leanh::LeanObject,
    mut v_hints_1613_: *mut crate::leanh::LeanObject,
    mut v_value_1614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_terminationBy_x3f_x3f_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_terminationBy_x3f_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_partialFixpoint_x3f_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decreasingBy_x3f_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1622_: u8 = 0;
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1628_: u8 = 0;
    let mut v_unused_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1615_ = crate::leanh::lean_ctor_get(v_hints_1613_, 0);
                v_terminationBy_x3f_x3f_1616_ = crate::leanh::lean_ctor_get(v_hints_1613_, 1);
                v_terminationBy_x3f_1617_ = crate::leanh::lean_ctor_get(v_hints_1613_, 2);
                v_partialFixpoint_x3f_1618_ = crate::leanh::lean_ctor_get(v_hints_1613_, 3);
                v_decreasingBy_x3f_1619_ = crate::leanh::lean_ctor_get(v_hints_1613_, 4);
                v_isSharedCheck_1628_ = (!crate::leanh::lean_is_exclusive(v_hints_1613_)) as u8;
                if v_isSharedCheck_1628_ == 0 {
                    v_unused_1629_ = crate::leanh::lean_ctor_get(v_hints_1613_, 5);
                    crate::leanh::lean_dec(v_unused_1629_);
                    v___x_1621_ = v_hints_1613_;
                    v_isShared_1622_ = v_isSharedCheck_1628_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_decreasingBy_x3f_1619_);
                    crate::leanh::lean_inc(v_partialFixpoint_x3f_1618_);
                    crate::leanh::lean_inc(v_terminationBy_x3f_1617_);
                    crate::leanh::lean_inc(v_terminationBy_x3f_x3f_1616_);
                    crate::leanh::lean_inc(v_ref_1615_);
                    crate::leanh::lean_dec(v_hints_1613_);
                    v___x_1621_ = crate::leanh::lean_box(0);
                    v_isShared_1622_ = v_isSharedCheck_1628_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1623_ = l_Lean_Expr_getNumHeadLambdas(v_value_1614_);
                v___x_1624_ = lean_nat_sub(v___x_1623_, v_headerParams_1612_);
                crate::leanh::lean_dec(v___x_1623_);
                if v_isShared_1622_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1621_, 5, v___x_1624_);
                    v___x_1626_ = v___x_1621_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1627_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_ref_1615_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1627_,
                        1,
                        v_terminationBy_x3f_x3f_1616_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1627_,
                        2,
                        v_terminationBy_x3f_1617_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1627_,
                        3,
                        v_partialFixpoint_x3f_1618_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1627_,
                        4,
                        v_decreasingBy_x3f_1619_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1627_, 5, v___x_1624_);
                    v___x_1626_ = v_reuseFailAlloc_1627_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1626_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_TerminationHints_rememberExtraParams___boxed(
    mut v_headerParams_1630_: *mut crate::leanh::LeanObject,
    mut v_hints_1631_: *mut crate::leanh::LeanObject,
    mut v_value_1632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1633_ = l_Lean_Elab_TerminationHints_rememberExtraParams(
        v_headerParams_1630_,
        v_hints_1631_,
        v_value_1632_,
    );
    crate::leanh::lean_dec_ref(v_value_1632_);
    crate::leanh::lean_dec(v_headerParams_1630_);
    return v_res_1633_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1635_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__0;
    v___x_1636_ = l_Lean_stringToMessageData(v___x_1635_);
    return v___x_1636_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1640_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__3;
    v___x_1641_ = l_Lean_MessageData_ofFormat(v___x_1640_);
    return v___x_1641_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(
    mut v_a_1642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: u8 = 0;
    v___x_1643_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1644_ = lean_nat_dec_eq(v_a_1642_, v___x_1643_);
    if v___x_1644_ == 0 {
        let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1645_ = l_Nat_reprFast(v_a_1642_);
        v___x_1646_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1646_, 0, v___x_1645_);
        v___x_1647_ = l_Lean_MessageData_ofFormat(v___x_1646_);
        v___x_1648_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1_once), _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1);
        v___x_1649_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1649_, 0, v___x_1647_);
        crate::leanh::lean_ctor_set(v___x_1649_, 1, v___x_1648_);
        return v___x_1649_;
    } else {
        let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_a_1642_);
        v___x_1650_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4_once), _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4);
        return v___x_1650_;
    }
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(
    mut v_msgData_1651_: *mut crate::leanh::LeanObject,
    mut v___y_1652_: *mut crate::leanh::LeanObject,
    mut v___y_1653_: *mut crate::leanh::LeanObject,
    mut v___y_1654_: *mut crate::leanh::LeanObject,
    mut v___y_1655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1657_ = lean_st_ref_get(v___y_1655_);
    v_env_1658_ = crate::leanh::lean_ctor_get(v___x_1657_, 0);
    crate::leanh::lean_inc_ref(v_env_1658_);
    crate::leanh::lean_dec(v___x_1657_);
    v___x_1659_ = lean_st_ref_get(v___y_1653_);
    v_mctx_1660_ = crate::leanh::lean_ctor_get(v___x_1659_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1660_);
    crate::leanh::lean_dec(v___x_1659_);
    v_lctx_1661_ = crate::leanh::lean_ctor_get(v___y_1652_, 2);
    v_options_1662_ = crate::leanh::lean_ctor_get(v___y_1654_, 2);
    crate::leanh::lean_inc_ref(v_options_1662_);
    crate::leanh::lean_inc_ref(v_lctx_1661_);
    v___x_1663_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1663_, 0, v_env_1658_);
    crate::leanh::lean_ctor_set(v___x_1663_, 1, v_mctx_1660_);
    crate::leanh::lean_ctor_set(v___x_1663_, 2, v_lctx_1661_);
    crate::leanh::lean_ctor_set(v___x_1663_, 3, v_options_1662_);
    v___x_1664_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1664_, 0, v___x_1663_);
    crate::leanh::lean_ctor_set(v___x_1664_, 1, v_msgData_1651_);
    v___x_1665_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1665_, 0, v___x_1664_);
    return v___x_1665_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_1666_: *mut crate::leanh::LeanObject,
    mut v___y_1667_: *mut crate::leanh::LeanObject,
    mut v___y_1668_: *mut crate::leanh::LeanObject,
    mut v___y_1669_: *mut crate::leanh::LeanObject,
    mut v___y_1670_: *mut crate::leanh::LeanObject,
    mut v___y_1671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1672_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(v_msgData_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
    crate::leanh::lean_dec(v___y_1670_);
    crate::leanh::lean_dec_ref(v___y_1669_);
    crate::leanh::lean_dec(v___y_1668_);
    crate::leanh::lean_dec_ref(v___y_1667_);
    return v_res_1672_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(
    mut v_msg_1673_: *mut crate::leanh::LeanObject,
    mut v___y_1674_: *mut crate::leanh::LeanObject,
    mut v___y_1675_: *mut crate::leanh::LeanObject,
    mut v___y_1676_: *mut crate::leanh::LeanObject,
    mut v___y_1677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1684_: u8 = 0;
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1689_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1679_ = crate::leanh::lean_ctor_get(v___y_1676_, 5);
                v___x_1680_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(v_msg_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
                v_a_1681_ = crate::leanh::lean_ctor_get(v___x_1680_, 0);
                v_isSharedCheck_1689_ = (!crate::leanh::lean_is_exclusive(v___x_1680_)) as u8;
                if v_isSharedCheck_1689_ == 0 {
                    v___x_1683_ = v___x_1680_;
                    v_isShared_1684_ = v_isSharedCheck_1689_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1681_);
                    crate::leanh::lean_dec(v___x_1680_);
                    v___x_1683_ = crate::leanh::lean_box(0);
                    v_isShared_1684_ = v_isSharedCheck_1689_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1679_);
                v___x_1685_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1685_, 0, v_ref_1679_);
                crate::leanh::lean_ctor_set(v___x_1685_, 1, v_a_1681_);
                if v_isShared_1684_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1683_, 1);
                    crate::leanh::lean_ctor_set(v___x_1683_, 0, v___x_1685_);
                    v___x_1687_ = v___x_1683_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1688_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1685_);
                    v___x_1687_ = v_reuseFailAlloc_1688_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1687_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg___boxed(
    mut v_msg_1690_: *mut crate::leanh::LeanObject,
    mut v___y_1691_: *mut crate::leanh::LeanObject,
    mut v___y_1692_: *mut crate::leanh::LeanObject,
    mut v___y_1693_: *mut crate::leanh::LeanObject,
    mut v___y_1694_: *mut crate::leanh::LeanObject,
    mut v___y_1695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1696_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
    crate::leanh::lean_dec(v___y_1694_);
    crate::leanh::lean_dec_ref(v___y_1693_);
    crate::leanh::lean_dec(v___y_1692_);
    crate::leanh::lean_dec_ref(v___y_1691_);
    return v_res_1696_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(
    mut v_ref_1697_: *mut crate::leanh::LeanObject,
    mut v_msg_1698_: *mut crate::leanh::LeanObject,
    mut v___y_1699_: *mut crate::leanh::LeanObject,
    mut v___y_1700_: *mut crate::leanh::LeanObject,
    mut v___y_1701_: *mut crate::leanh::LeanObject,
    mut v___y_1702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1716_: u8 = 0;
    let mut v_cancelTk_x3f_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1718_: u8 = 0;
    let mut v_inheritedTraceOptions_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1704_ = crate::leanh::lean_ctor_get(v___y_1701_, 0);
    v_fileMap_1705_ = crate::leanh::lean_ctor_get(v___y_1701_, 1);
    v_options_1706_ = crate::leanh::lean_ctor_get(v___y_1701_, 2);
    v_currRecDepth_1707_ = crate::leanh::lean_ctor_get(v___y_1701_, 3);
    v_maxRecDepth_1708_ = crate::leanh::lean_ctor_get(v___y_1701_, 4);
    v_ref_1709_ = crate::leanh::lean_ctor_get(v___y_1701_, 5);
    v_currNamespace_1710_ = crate::leanh::lean_ctor_get(v___y_1701_, 6);
    v_openDecls_1711_ = crate::leanh::lean_ctor_get(v___y_1701_, 7);
    v_initHeartbeats_1712_ = crate::leanh::lean_ctor_get(v___y_1701_, 8);
    v_maxHeartbeats_1713_ = crate::leanh::lean_ctor_get(v___y_1701_, 9);
    v_quotContext_1714_ = crate::leanh::lean_ctor_get(v___y_1701_, 10);
    v_currMacroScope_1715_ = crate::leanh::lean_ctor_get(v___y_1701_, 11);
    v_diag_1716_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1701_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1717_ = crate::leanh::lean_ctor_get(v___y_1701_, 12);
    v_suppressElabErrors_1718_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1701_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1719_ = crate::leanh::lean_ctor_get(v___y_1701_, 13);
    v_ref_1720_ = l_Lean_replaceRef(v_ref_1697_, v_ref_1709_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1719_);
    crate::leanh::lean_inc(v_cancelTk_x3f_1717_);
    crate::leanh::lean_inc(v_currMacroScope_1715_);
    crate::leanh::lean_inc(v_quotContext_1714_);
    crate::leanh::lean_inc(v_maxHeartbeats_1713_);
    crate::leanh::lean_inc(v_initHeartbeats_1712_);
    crate::leanh::lean_inc(v_openDecls_1711_);
    crate::leanh::lean_inc(v_currNamespace_1710_);
    crate::leanh::lean_inc(v_maxRecDepth_1708_);
    crate::leanh::lean_inc(v_currRecDepth_1707_);
    crate::leanh::lean_inc_ref(v_options_1706_);
    crate::leanh::lean_inc_ref(v_fileMap_1705_);
    crate::leanh::lean_inc_ref(v_fileName_1704_);
    v___x_1721_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1721_, 0, v_fileName_1704_);
    crate::leanh::lean_ctor_set(v___x_1721_, 1, v_fileMap_1705_);
    crate::leanh::lean_ctor_set(v___x_1721_, 2, v_options_1706_);
    crate::leanh::lean_ctor_set(v___x_1721_, 3, v_currRecDepth_1707_);
    crate::leanh::lean_ctor_set(v___x_1721_, 4, v_maxRecDepth_1708_);
    crate::leanh::lean_ctor_set(v___x_1721_, 5, v_ref_1720_);
    crate::leanh::lean_ctor_set(v___x_1721_, 6, v_currNamespace_1710_);
    crate::leanh::lean_ctor_set(v___x_1721_, 7, v_openDecls_1711_);
    crate::leanh::lean_ctor_set(v___x_1721_, 8, v_initHeartbeats_1712_);
    crate::leanh::lean_ctor_set(v___x_1721_, 9, v_maxHeartbeats_1713_);
    crate::leanh::lean_ctor_set(v___x_1721_, 10, v_quotContext_1714_);
    crate::leanh::lean_ctor_set(v___x_1721_, 11, v_currMacroScope_1715_);
    crate::leanh::lean_ctor_set(v___x_1721_, 12, v_cancelTk_x3f_1717_);
    crate::leanh::lean_ctor_set(v___x_1721_, 13, v_inheritedTraceOptions_1719_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1721_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_1716_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1721_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1718_,
    );
    v___x_1722_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_1698_, v___y_1699_, v___y_1700_, v___x_1721_, v___y_1702_);
    crate::leanh::lean_dec_ref_known(v___x_1721_, 14);
    return v___x_1722_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg___boxed(
    mut v_ref_1723_: *mut crate::leanh::LeanObject,
    mut v_msg_1724_: *mut crate::leanh::LeanObject,
    mut v___y_1725_: *mut crate::leanh::LeanObject,
    mut v___y_1726_: *mut crate::leanh::LeanObject,
    mut v___y_1727_: *mut crate::leanh::LeanObject,
    mut v___y_1728_: *mut crate::leanh::LeanObject,
    mut v___y_1729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1730_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(
        v_ref_1723_,
        v_msg_1724_,
        v___y_1725_,
        v___y_1726_,
        v___y_1727_,
        v___y_1728_,
    );
    crate::leanh::lean_dec(v___y_1728_);
    crate::leanh::lean_dec_ref(v___y_1727_);
    crate::leanh::lean_dec(v___y_1726_);
    crate::leanh::lean_dec_ref(v___y_1725_);
    crate::leanh::lean_dec(v_ref_1723_);
    return v_res_1730_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationBy_checkVars___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1732_ = l_Lean_Elab_TerminationBy_checkVars___closed__0;
    v___x_1733_ = l_Lean_stringToMessageData(v___x_1732_);
    return v___x_1733_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationBy_checkVars___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1735_ = l_Lean_Elab_TerminationBy_checkVars___closed__2;
    v___x_1736_ = l_Lean_stringToMessageData(v___x_1735_);
    return v___x_1736_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationBy_checkVars___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1738_ = l_Lean_Elab_TerminationBy_checkVars___closed__4;
    v___x_1739_ = l_Lean_stringToMessageData(v___x_1738_);
    return v___x_1739_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationBy_checkVars___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1744_ = l_Lean_Elab_TerminationBy_checkVars___closed__8;
    v___x_1745_ = l_Lean_stringToMessageData(v___x_1744_);
    return v___x_1745_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationBy_checkVars___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1749_ = l_Lean_Elab_TerminationBy_checkVars___closed__11;
    v___x_1750_ = l_Lean_MessageData_ofFormat(v___x_1749_);
    return v___x_1750_;
}
pub unsafe fn l_Lean_Elab_TerminationBy_checkVars(
    mut v_funName_1751_: *mut crate::leanh::LeanObject,
    mut v_extraParams_1752_: *mut crate::leanh::LeanObject,
    mut v_tb_1753_: *mut crate::leanh::LeanObject,
    mut v_a_1754_: *mut crate::leanh::LeanObject,
    mut v_a_1755_: *mut crate::leanh::LeanObject,
    mut v_a_1756_: *mut crate::leanh::LeanObject,
    mut v_a_1757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_synthetic_1759_: u8 = 0;
    v_synthetic_1759_ = crate::leanh::lean_ctor_get_uint8(
        v_tb_1753_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
    );
    if v_synthetic_1759_ == 0 {
        let mut v_ref_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_vars_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1763_: u8 = 0;
        v_ref_1760_ = crate::leanh::lean_ctor_get(v_tb_1753_, 0);
        v_vars_1761_ = crate::leanh::lean_ctor_get(v_tb_1753_, 1);
        v___x_1762_ = lean_array_get_size(v_vars_1761_);
        v___x_1763_ = lean_nat_dec_lt(v_extraParams_1752_, v___x_1762_);
        if v___x_1763_ == 0 {
            let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_extraParams_1752_);
            crate::leanh::lean_dec(v_funName_1751_);
            v___x_1764_ = crate::leanh::lean_box(0);
            v___x_1765_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1765_, 0, v___x_1764_);
            return v___x_1765_;
        } else {
            let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_msg_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_ident_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1780_: u8 = 0;
            v___x_1766_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(v___x_1762_);
            v___x_1767_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Elab_TerminationBy_checkVars___closed__1),
                core::ptr::addr_of_mut!(l_Lean_Elab_TerminationBy_checkVars___closed__1_once),
                _init_l_Lean_Elab_TerminationBy_checkVars___closed__1,
            );
            v___x_1768_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1768_, 0, v___x_1766_);
            crate::leanh::lean_ctor_set(v___x_1768_, 1, v___x_1767_);
            crate::leanh::lean_inc(v_funName_1751_);
            v___x_1769_ = l_Lean_MessageData_ofName(v_funName_1751_);
            v___x_1770_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Elab_TerminationBy_checkVars___closed__3),
                core::ptr::addr_of_mut!(l_Lean_Elab_TerminationBy_checkVars___closed__3_once),
                _init_l_Lean_Elab_TerminationBy_checkVars___closed__3,
            );
            v___x_1771_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1771_, 0, v___x_1769_);
            crate::leanh::lean_ctor_set(v___x_1771_, 1, v___x_1770_);
            v___x_1772_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(v_extraParams_1752_);
            v___x_1773_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1773_, 0, v___x_1771_);
            crate::leanh::lean_ctor_set(v___x_1773_, 1, v___x_1772_);
            v___x_1774_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Elab_TerminationBy_checkVars___closed__5),
                core::ptr::addr_of_mut!(l_Lean_Elab_TerminationBy_checkVars___closed__5_once),
                _init_l_Lean_Elab_TerminationBy_checkVars___closed__5,
            );
            v___x_1775_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1775_, 0, v___x_1773_);
            crate::leanh::lean_ctor_set(v___x_1775_, 1, v___x_1774_);
            v_msg_1776_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v_msg_1776_, 0, v___x_1768_);
            crate::leanh::lean_ctor_set(v_msg_1776_, 1, v___x_1775_);
            v___x_1777_ = crate::leanh::lean_unsigned_to_nat(0);
            v_ident_1778_ = lean_array_fget_borrowed(v_vars_1761_, v___x_1777_);
            v___x_1779_ = l_Lean_Elab_TerminationBy_checkVars___closed__7;
            crate::leanh::lean_inc(v_ident_1778_);
            v___x_1780_ = l_Lean_Syntax_isOfKind(v_ident_1778_, v___x_1779_);
            if v___x_1780_ == 0 {
                let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_funName_1751_);
                v___x_1781_ =
                    l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(
                        v_ref_1760_,
                        v_msg_1776_,
                        v_a_1754_,
                        v_a_1755_,
                        v_a_1756_,
                        v_a_1757_,
                    );
                return v___x_1781_;
            } else {
                let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1783_: u8 = 0;
                v___x_1782_ = l_Lean_TSyntax_getId(v_ident_1778_);
                v___x_1783_ = l_Lean_Name_isSuffixOf(v___x_1782_, v_funName_1751_);
                crate::leanh::lean_dec(v_funName_1751_);
                crate::leanh::lean_dec(v___x_1782_);
                if v___x_1783_ == 0 {
                    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_1784_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_1760_, v_msg_1776_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_);
                    return v___x_1784_;
                } else {
                    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_msg_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_1785_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_TerminationBy_checkVars___closed__9),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_TerminationBy_checkVars___closed__9_once
                        ),
                        _init_l_Lean_Elab_TerminationBy_checkVars___closed__9,
                    );
                    v___x_1786_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1786_, 0, v_msg_1776_);
                    crate::leanh::lean_ctor_set(v___x_1786_, 1, v___x_1785_);
                    v___x_1787_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_TerminationBy_checkVars___closed__12),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_TerminationBy_checkVars___closed__12_once
                        ),
                        _init_l_Lean_Elab_TerminationBy_checkVars___closed__12,
                    );
                    v_msg_1788_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_msg_1788_, 0, v___x_1786_);
                    crate::leanh::lean_ctor_set(v_msg_1788_, 1, v___x_1787_);
                    v___x_1789_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_1760_, v_msg_1788_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_);
                    return v___x_1789_;
                }
            }
        }
    } else {
        let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_extraParams_1752_);
        crate::leanh::lean_dec(v_funName_1751_);
        v___x_1790_ = crate::leanh::lean_box(0);
        v___x_1791_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1791_, 0, v___x_1790_);
        return v___x_1791_;
    }
}
pub unsafe fn l_Lean_Elab_TerminationBy_checkVars___boxed(
    mut v_funName_1792_: *mut crate::leanh::LeanObject,
    mut v_extraParams_1793_: *mut crate::leanh::LeanObject,
    mut v_tb_1794_: *mut crate::leanh::LeanObject,
    mut v_a_1795_: *mut crate::leanh::LeanObject,
    mut v_a_1796_: *mut crate::leanh::LeanObject,
    mut v_a_1797_: *mut crate::leanh::LeanObject,
    mut v_a_1798_: *mut crate::leanh::LeanObject,
    mut v_a_1799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1800_ = l_Lean_Elab_TerminationBy_checkVars(
        v_funName_1792_,
        v_extraParams_1793_,
        v_tb_1794_,
        v_a_1795_,
        v_a_1796_,
        v_a_1797_,
        v_a_1798_,
    );
    crate::leanh::lean_dec(v_a_1798_);
    crate::leanh::lean_dec_ref(v_a_1797_);
    crate::leanh::lean_dec(v_a_1796_);
    crate::leanh::lean_dec_ref(v_a_1795_);
    crate::leanh::lean_dec_ref(v_tb_1794_);
    return v_res_1800_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(
    mut v_00_u03b1_1801_: *mut crate::leanh::LeanObject,
    mut v_ref_1802_: *mut crate::leanh::LeanObject,
    mut v_msg_1803_: *mut crate::leanh::LeanObject,
    mut v___y_1804_: *mut crate::leanh::LeanObject,
    mut v___y_1805_: *mut crate::leanh::LeanObject,
    mut v___y_1806_: *mut crate::leanh::LeanObject,
    mut v___y_1807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1809_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(
        v_ref_1802_,
        v_msg_1803_,
        v___y_1804_,
        v___y_1805_,
        v___y_1806_,
        v___y_1807_,
    );
    return v___x_1809_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___boxed(
    mut v_00_u03b1_1810_: *mut crate::leanh::LeanObject,
    mut v_ref_1811_: *mut crate::leanh::LeanObject,
    mut v_msg_1812_: *mut crate::leanh::LeanObject,
    mut v___y_1813_: *mut crate::leanh::LeanObject,
    mut v___y_1814_: *mut crate::leanh::LeanObject,
    mut v___y_1815_: *mut crate::leanh::LeanObject,
    mut v___y_1816_: *mut crate::leanh::LeanObject,
    mut v___y_1817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1818_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(
        v_00_u03b1_1810_,
        v_ref_1811_,
        v_msg_1812_,
        v___y_1813_,
        v___y_1814_,
        v___y_1815_,
        v___y_1816_,
    );
    crate::leanh::lean_dec(v___y_1816_);
    crate::leanh::lean_dec_ref(v___y_1815_);
    crate::leanh::lean_dec(v___y_1814_);
    crate::leanh::lean_dec_ref(v___y_1813_);
    crate::leanh::lean_dec(v_ref_1811_);
    return v_res_1818_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(
    mut v_00_u03b1_1819_: *mut crate::leanh::LeanObject,
    mut v_msg_1820_: *mut crate::leanh::LeanObject,
    mut v___y_1821_: *mut crate::leanh::LeanObject,
    mut v___y_1822_: *mut crate::leanh::LeanObject,
    mut v___y_1823_: *mut crate::leanh::LeanObject,
    mut v___y_1824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1826_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
    return v___x_1826_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___boxed(
    mut v_00_u03b1_1827_: *mut crate::leanh::LeanObject,
    mut v_msg_1828_: *mut crate::leanh::LeanObject,
    mut v___y_1829_: *mut crate::leanh::LeanObject,
    mut v___y_1830_: *mut crate::leanh::LeanObject,
    mut v___y_1831_: *mut crate::leanh::LeanObject,
    mut v___y_1832_: *mut crate::leanh::LeanObject,
    mut v___y_1833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1834_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(v_00_u03b1_1827_, v_msg_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
    crate::leanh::lean_dec(v___y_1832_);
    crate::leanh::lean_dec_ref(v___y_1831_);
    crate::leanh::lean_dec(v___y_1830_);
    crate::leanh::lean_dec_ref(v___y_1829_);
    return v_res_1834_;
}
pub unsafe fn l_Lean_Elab_elabTerminationHints___redArg___lam__0(
    mut v_val_1835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1836_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1836_, 0, v_val_1835_);
    return v___x_1836_;
}
pub unsafe fn l_Lean_Elab_elabTerminationHints___redArg___lam__1(
    mut v_stx_1837_: *mut crate::leanh::LeanObject,
    mut v_terminationBy_x3f_x3f_1838_: *mut crate::leanh::LeanObject,
    mut v_terminationBy_x3f_1839_: *mut crate::leanh::LeanObject,
    mut v_partialFixpoint_x3f_1840_: *mut crate::leanh::LeanObject,
    mut v___x_1841_: *mut crate::leanh::LeanObject,
    mut v_toPure_1842_: *mut crate::leanh::LeanObject,
    mut v_decreasingBy_x3f_1843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1844_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1844_, 0, v_stx_1837_);
    crate::leanh::lean_ctor_set(v___x_1844_, 1, v_terminationBy_x3f_x3f_1838_);
    crate::leanh::lean_ctor_set(v___x_1844_, 2, v_terminationBy_x3f_1839_);
    crate::leanh::lean_ctor_set(v___x_1844_, 3, v_partialFixpoint_x3f_1840_);
    crate::leanh::lean_ctor_set(v___x_1844_, 4, v_decreasingBy_x3f_1843_);
    crate::leanh::lean_ctor_set(v___x_1844_, 5, v___x_1841_);
    v___x_1845_ =
        crate::leanh::lean_apply_2(v_toPure_1842_, crate::leanh::lean_box(0), v___x_1844_);
    return v___x_1845_;
}
pub unsafe fn _init_l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1848_ = l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__1;
    v___x_1849_ = l_Lean_stringToMessageData(v___x_1848_);
    return v___x_1849_;
}
pub unsafe fn l_Lean_Elab_elabTerminationHints___redArg___lam__2(
    mut v_stx_1850_: *mut crate::leanh::LeanObject,
    mut v_terminationBy_x3f_x3f_1851_: *mut crate::leanh::LeanObject,
    mut v_terminationBy_x3f_1852_: *mut crate::leanh::LeanObject,
    mut v___x_1853_: *mut crate::leanh::LeanObject,
    mut v_toPure_1854_: *mut crate::leanh::LeanObject,
    mut v_d_x3f_1855_: *mut crate::leanh::LeanObject,
    mut v_toBind_1856_: *mut crate::leanh::LeanObject,
    mut v_toFunctor_1857_: *mut crate::leanh::LeanObject,
    mut v___f_1858_: *mut crate::leanh::LeanObject,
    mut v___x_1859_: *mut crate::leanh::LeanObject,
    mut v___x_1860_: *mut crate::leanh::LeanObject,
    mut v___x_1861_: *mut crate::leanh::LeanObject,
    mut v_inst_1862_: *mut crate::leanh::LeanObject,
    mut v_inst_1863_: *mut crate::leanh::LeanObject,
    mut v___x_1864_: *mut crate::leanh::LeanObject,
    mut v_partialFixpoint_x3f_1865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1874_: u8 = 0;
    let mut v___y_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: u8 = 0;
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tactic_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1889_: u8 = 0;
    let mut v_unused_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_toPure_1854_);
                v___f_1866_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_elabTerminationHints___redArg___lam__1 as *mut core::ffi::c_void,
                    7,
                    6,
                );
                crate::leanh::lean_closure_set(v___f_1866_, 0, v_stx_1850_);
                crate::leanh::lean_closure_set(v___f_1866_, 1, v_terminationBy_x3f_x3f_1851_);
                crate::leanh::lean_closure_set(v___f_1866_, 2, v_terminationBy_x3f_1852_);
                crate::leanh::lean_closure_set(v___f_1866_, 3, v_partialFixpoint_x3f_1865_);
                crate::leanh::lean_closure_set(v___f_1866_, 4, v___x_1853_);
                crate::leanh::lean_closure_set(v___f_1866_, 5, v_toPure_1854_);
                if crate::leanh::lean_obj_tag(v_d_x3f_1855_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_1863_);
                    crate::leanh::lean_dec_ref(v_inst_1862_);
                    crate::leanh::lean_dec_ref(v___x_1861_);
                    crate::leanh::lean_dec_ref(v___x_1860_);
                    crate::leanh::lean_dec_ref(v___x_1859_);
                    crate::leanh::lean_dec_ref(v___f_1858_);
                    crate::leanh::lean_dec_ref(v_toFunctor_1857_);
                    v___x_1867_ = crate::leanh::lean_box(0);
                    v___x_1868_ = crate::leanh::lean_apply_2(
                        v_toPure_1854_,
                        crate::leanh::lean_box(0),
                        v___x_1867_,
                    );
                    v___x_1869_ = crate::leanh::lean_apply_4(
                        v_toBind_1856_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_1868_,
                        v___f_1866_,
                    );
                    return v___x_1869_;
                } else {
                    v_val_1870_ = crate::leanh::lean_ctor_get(v_d_x3f_1855_, 0);
                    crate::leanh::lean_inc(v_val_1870_);
                    crate::leanh::lean_dec_ref_known(v_d_x3f_1855_, 1);
                    v_map_1871_ = crate::leanh::lean_ctor_get(v_toFunctor_1857_, 0);
                    v_isSharedCheck_1889_ =
                        (!crate::leanh::lean_is_exclusive(v_toFunctor_1857_)) as u8;
                    if v_isSharedCheck_1889_ == 0 {
                        v_unused_1890_ = crate::leanh::lean_ctor_get(v_toFunctor_1857_, 1);
                        crate::leanh::lean_dec(v_unused_1890_);
                        v___x_1873_ = v_toFunctor_1857_;
                        v_isShared_1874_ = v_isSharedCheck_1889_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_map_1871_);
                        crate::leanh::lean_dec(v_toFunctor_1857_);
                        v___x_1873_ = crate::leanh::lean_box(0);
                        v_isShared_1874_ = v_isSharedCheck_1889_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1879_ = l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0;
                v___x_1880_ =
                    l_Lean_Name_mkStr4(v___x_1859_, v___x_1860_, v___x_1861_, v___x_1879_);
                crate::leanh::lean_inc(v_val_1870_);
                v___x_1881_ = l_Lean_Syntax_isOfKind(v_val_1870_, v___x_1880_);
                crate::leanh::lean_dec(v___x_1880_);
                if v___x_1881_ == 0 {
                    crate::leanh::lean_del_object(v___x_1873_);
                    crate::leanh::lean_dec(v_toPure_1854_);
                    v___x_1882_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2_once
                        ),
                        _init_l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2,
                    );
                    v___x_1883_ = l_Lean_throwErrorAt___redArg(
                        v_inst_1862_,
                        v_inst_1863_,
                        v_val_1870_,
                        v___x_1882_,
                    );
                    v___y_1876_ = v___x_1883_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_inst_1863_);
                    crate::leanh::lean_dec_ref(v_inst_1862_);
                    v_tactic_1884_ = l_Lean_Syntax_getArg(v_val_1870_, v___x_1864_);
                    if v_isShared_1874_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1873_, 1, v_tactic_1884_);
                        crate::leanh::lean_ctor_set(v___x_1873_, 0, v_val_1870_);
                        v___x_1886_ = v___x_1873_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1888_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_val_1870_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_tactic_1884_);
                        v___x_1886_ = v_reuseFailAlloc_1888_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1877_ = crate::leanh::lean_apply_4(
                    v_map_1871_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_1858_,
                    v___y_1876_,
                );
                v___x_1878_ = crate::leanh::lean_apply_4(
                    v_toBind_1856_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1877_,
                    v___f_1866_,
                );
                return v___x_1878_;
            }
            3 => {
                v___x_1887_ = crate::leanh::lean_apply_2(
                    v_toPure_1854_,
                    crate::leanh::lean_box(0),
                    v___x_1886_,
                );
                v___y_1876_ = v___x_1887_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed(
    mut v_stx_1891_: *mut crate::leanh::LeanObject,
    mut v_terminationBy_x3f_x3f_1892_: *mut crate::leanh::LeanObject,
    mut v_terminationBy_x3f_1893_: *mut crate::leanh::LeanObject,
    mut v___x_1894_: *mut crate::leanh::LeanObject,
    mut v_toPure_1895_: *mut crate::leanh::LeanObject,
    mut v_d_x3f_1896_: *mut crate::leanh::LeanObject,
    mut v_toBind_1897_: *mut crate::leanh::LeanObject,
    mut v_toFunctor_1898_: *mut crate::leanh::LeanObject,
    mut v___f_1899_: *mut crate::leanh::LeanObject,
    mut v___x_1900_: *mut crate::leanh::LeanObject,
    mut v___x_1901_: *mut crate::leanh::LeanObject,
    mut v___x_1902_: *mut crate::leanh::LeanObject,
    mut v_inst_1903_: *mut crate::leanh::LeanObject,
    mut v_inst_1904_: *mut crate::leanh::LeanObject,
    mut v___x_1905_: *mut crate::leanh::LeanObject,
    mut v_partialFixpoint_x3f_1906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1907_ = l_Lean_Elab_elabTerminationHints___redArg___lam__2(
        v_stx_1891_,
        v_terminationBy_x3f_x3f_1892_,
        v_terminationBy_x3f_1893_,
        v___x_1894_,
        v_toPure_1895_,
        v_d_x3f_1896_,
        v_toBind_1897_,
        v_toFunctor_1898_,
        v___f_1899_,
        v___x_1900_,
        v___x_1901_,
        v___x_1902_,
        v_inst_1903_,
        v_inst_1904_,
        v___x_1905_,
        v_partialFixpoint_x3f_1906_,
    );
    crate::leanh::lean_dec(v___x_1905_);
    return v_res_1907_;
}
pub unsafe fn l_Lean_Elab_elabTerminationHints___redArg___lam__3(
    mut v___f_1908_: *mut crate::leanh::LeanObject,
    mut v_partialFixpoint_x3f_1909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1910_ = crate::leanh::lean_apply_1(v___f_1908_, v_partialFixpoint_x3f_1909_);
    return v___x_1910_;
}
pub unsafe fn l_Lean_Elab_elabTerminationHints___redArg___lam__11(
    mut v_stx_1914_: *mut crate::leanh::LeanObject,
    mut v_terminationBy_x3f_x3f_1915_: *mut crate::leanh::LeanObject,
    mut v___x_1916_: *mut crate::leanh::LeanObject,
    mut v_toPure_1917_: *mut crate::leanh::LeanObject,
    mut v_d_x3f_1918_: *mut crate::leanh::LeanObject,
    mut v_toBind_1919_: *mut crate::leanh::LeanObject,
    mut v_toFunctor_1920_: *mut crate::leanh::LeanObject,
    mut v___f_1921_: *mut crate::leanh::LeanObject,
    mut v___x_1922_: *mut crate::leanh::LeanObject,
    mut v___x_1923_: *mut crate::leanh::LeanObject,
    mut v___x_1924_: *mut crate::leanh::LeanObject,
    mut v_inst_1925_: *mut crate::leanh::LeanObject,
    mut v_inst_1926_: *mut crate::leanh::LeanObject,
    mut v___x_1927_: *mut crate::leanh::LeanObject,
    mut v_t_x3f_1928_: *mut crate::leanh::LeanObject,
    mut v_terminationBy_x3f_1929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1934_: u8 = 0;
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: u8 = 0;
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: u8 = 0;
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: u8 = 0;
    let mut v___f_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_x3f_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: u8 = 0;
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: u8 = 0;
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: u8 = 0;
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_x3f_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_x3f_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: u8 = 0;
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: u8 = 0;
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: u8 = 0;
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_x3f_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_x3f_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: u8 = 0;
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: u8 = 0;
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: u8 = 0;
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_x3f_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2008_: u8 = 0;
    let mut v___f_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___x_1927_);
                crate::leanh::lean_inc_ref(v___x_1924_);
                crate::leanh::lean_inc_ref(v___x_1923_);
                crate::leanh::lean_inc_ref(v___x_1922_);
                crate::leanh::lean_inc(v_toBind_1919_);
                crate::leanh::lean_inc(v_toPure_1917_);
                v___f_1930_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed
                        as *mut core::ffi::c_void,
                    16,
                    15,
                );
                crate::leanh::lean_closure_set(v___f_1930_, 0, v_stx_1914_);
                crate::leanh::lean_closure_set(v___f_1930_, 1, v_terminationBy_x3f_x3f_1915_);
                crate::leanh::lean_closure_set(v___f_1930_, 2, v_terminationBy_x3f_1929_);
                crate::leanh::lean_closure_set(v___f_1930_, 3, v___x_1916_);
                crate::leanh::lean_closure_set(v___f_1930_, 4, v_toPure_1917_);
                crate::leanh::lean_closure_set(v___f_1930_, 5, v_d_x3f_1918_);
                crate::leanh::lean_closure_set(v___f_1930_, 6, v_toBind_1919_);
                crate::leanh::lean_closure_set(v___f_1930_, 7, v_toFunctor_1920_);
                crate::leanh::lean_closure_set(v___f_1930_, 8, v___f_1921_);
                crate::leanh::lean_closure_set(v___f_1930_, 9, v___x_1922_);
                crate::leanh::lean_closure_set(v___f_1930_, 10, v___x_1923_);
                crate::leanh::lean_closure_set(v___f_1930_, 11, v___x_1924_);
                crate::leanh::lean_closure_set(v___f_1930_, 12, v_inst_1925_);
                crate::leanh::lean_closure_set(v___f_1930_, 13, v_inst_1926_);
                crate::leanh::lean_closure_set(v___f_1930_, 14, v___x_1927_);
                if crate::leanh::lean_obj_tag(v_t_x3f_1928_) == 1 {
                    v_val_1931_ = crate::leanh::lean_ctor_get(v_t_x3f_1928_, 0);
                    v_isSharedCheck_2008_ = (!crate::leanh::lean_is_exclusive(v_t_x3f_1928_)) as u8;
                    if v_isSharedCheck_2008_ == 0 {
                        v___x_1933_ = v_t_x3f_1928_;
                        v_isShared_1934_ = v_isSharedCheck_2008_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1931_);
                        crate::leanh::lean_dec(v_t_x3f_1928_);
                        v___x_1933_ = crate::leanh::lean_box(0);
                        v_isShared_1934_ = v_isSharedCheck_2008_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_t_x3f_1928_);
                    crate::leanh::lean_dec(v___x_1927_);
                    crate::leanh::lean_dec_ref(v___x_1924_);
                    crate::leanh::lean_dec_ref(v___x_1923_);
                    crate::leanh::lean_dec_ref(v___x_1922_);
                    v___f_2009_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_elabTerminationHints___redArg___lam__3
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_2009_, 0, v___f_1930_);
                    v___x_2010_ = crate::leanh::lean_box(0);
                    v___x_2011_ = crate::leanh::lean_apply_2(
                        v_toPure_1917_,
                        crate::leanh::lean_box(0),
                        v___x_2010_,
                    );
                    v___x_2012_ = crate::leanh::lean_apply_4(
                        v_toBind_1919_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_2011_,
                        v___f_2009_,
                    );
                    return v___x_2012_;
                }
            }
            1 => {
                v___x_1935_ = l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0;
                crate::leanh::lean_inc_ref(v___x_1924_);
                crate::leanh::lean_inc_ref(v___x_1923_);
                crate::leanh::lean_inc_ref(v___x_1922_);
                v___x_1936_ =
                    l_Lean_Name_mkStr4(v___x_1922_, v___x_1923_, v___x_1924_, v___x_1935_);
                crate::leanh::lean_inc(v_val_1931_);
                v___x_1937_ = l_Lean_Syntax_isOfKind(v_val_1931_, v___x_1936_);
                crate::leanh::lean_dec(v___x_1936_);
                if v___x_1937_ == 0 {
                    v___x_1938_ = l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1;
                    crate::leanh::lean_inc_ref(v___x_1924_);
                    crate::leanh::lean_inc_ref(v___x_1923_);
                    crate::leanh::lean_inc_ref(v___x_1922_);
                    v___x_1939_ =
                        l_Lean_Name_mkStr4(v___x_1922_, v___x_1923_, v___x_1924_, v___x_1938_);
                    crate::leanh::lean_inc(v_val_1931_);
                    v___x_1940_ = l_Lean_Syntax_isOfKind(v_val_1931_, v___x_1939_);
                    crate::leanh::lean_dec(v___x_1939_);
                    if v___x_1940_ == 0 {
                        v___x_1941_ =
                            l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2;
                        v___x_1942_ =
                            l_Lean_Name_mkStr4(v___x_1922_, v___x_1923_, v___x_1924_, v___x_1941_);
                        crate::leanh::lean_inc(v_val_1931_);
                        v___x_1943_ = l_Lean_Syntax_isOfKind(v_val_1931_, v___x_1942_);
                        crate::leanh::lean_dec(v___x_1942_);
                        if v___x_1943_ == 0 {
                            crate::leanh::lean_del_object(v___x_1933_);
                            crate::leanh::lean_dec(v_val_1931_);
                            crate::leanh::lean_dec(v___x_1927_);
                            v___f_1944_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Elab_elabTerminationHints___redArg___lam__3
                                    as *mut core::ffi::c_void,
                                2,
                                1,
                            );
                            crate::leanh::lean_closure_set(v___f_1944_, 0, v___f_1930_);
                            v___x_1945_ = crate::leanh::lean_box(0);
                            v___x_1946_ = crate::leanh::lean_apply_2(
                                v_toPure_1917_,
                                crate::leanh::lean_box(0),
                                v___x_1945_,
                            );
                            v___x_1947_ = crate::leanh::lean_apply_4(
                                v_toBind_1919_,
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_1946_,
                                v___f_1944_,
                            );
                            return v___x_1947_;
                        } else {
                            v___f_1948_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Elab_elabTerminationHints___redArg___lam__3
                                    as *mut core::ffi::c_void,
                                2,
                                1,
                            );
                            crate::leanh::lean_closure_set(v___f_1948_, 0, v___f_1930_);
                            v___x_1958_ = l_Lean_Syntax_getArg(v_val_1931_, v___x_1927_);
                            v___x_1959_ = l_Lean_Syntax_isNone(v___x_1958_);
                            if v___x_1959_ == 0 {
                                v___x_1960_ = crate::leanh::lean_unsigned_to_nat(2);
                                crate::leanh::lean_inc(v___x_1958_);
                                v___x_1961_ = l_Lean_Syntax_matchesNull(v___x_1958_, v___x_1960_);
                                if v___x_1961_ == 0 {
                                    crate::leanh::lean_dec(v___x_1958_);
                                    crate::leanh::lean_del_object(v___x_1933_);
                                    crate::leanh::lean_dec(v_val_1931_);
                                    crate::leanh::lean_dec(v___x_1927_);
                                    v___x_1962_ = crate::leanh::lean_box(0);
                                    v___x_1963_ = crate::leanh::lean_apply_2(
                                        v_toPure_1917_,
                                        crate::leanh::lean_box(0),
                                        v___x_1962_,
                                    );
                                    v___x_1964_ = crate::leanh::lean_apply_4(
                                        v_toBind_1919_,
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        v___x_1963_,
                                        v___f_1948_,
                                    );
                                    return v___x_1964_;
                                } else {
                                    v_term_x3f_1965_ =
                                        l_Lean_Syntax_getArg(v___x_1958_, v___x_1927_);
                                    crate::leanh::lean_dec(v___x_1927_);
                                    crate::leanh::lean_dec(v___x_1958_);
                                    v___x_1966_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1966_, 0, v_term_x3f_1965_);
                                    v_term_x3f_1950_ = v___x_1966_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_1958_);
                                crate::leanh::lean_dec(v___x_1927_);
                                v___x_1967_ = crate::leanh::lean_box(0);
                                v_term_x3f_1950_ = v___x_1967_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1924_);
                        crate::leanh::lean_dec_ref(v___x_1923_);
                        crate::leanh::lean_dec_ref(v___x_1922_);
                        v___f_1968_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Elab_elabTerminationHints___redArg___lam__3
                                as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___f_1968_, 0, v___f_1930_);
                        v___x_1978_ = l_Lean_Syntax_getArg(v_val_1931_, v___x_1927_);
                        v___x_1979_ = l_Lean_Syntax_isNone(v___x_1978_);
                        if v___x_1979_ == 0 {
                            v___x_1980_ = crate::leanh::lean_unsigned_to_nat(2);
                            crate::leanh::lean_inc(v___x_1978_);
                            v___x_1981_ = l_Lean_Syntax_matchesNull(v___x_1978_, v___x_1980_);
                            if v___x_1981_ == 0 {
                                crate::leanh::lean_dec(v___x_1978_);
                                crate::leanh::lean_del_object(v___x_1933_);
                                crate::leanh::lean_dec(v_val_1931_);
                                crate::leanh::lean_dec(v___x_1927_);
                                v___x_1982_ = crate::leanh::lean_box(0);
                                v___x_1983_ = crate::leanh::lean_apply_2(
                                    v_toPure_1917_,
                                    crate::leanh::lean_box(0),
                                    v___x_1982_,
                                );
                                v___x_1984_ = crate::leanh::lean_apply_4(
                                    v_toBind_1919_,
                                    crate::leanh::lean_box(0),
                                    crate::leanh::lean_box(0),
                                    v___x_1983_,
                                    v___f_1968_,
                                );
                                return v___x_1984_;
                            } else {
                                v_term_x3f_1985_ = l_Lean_Syntax_getArg(v___x_1978_, v___x_1927_);
                                crate::leanh::lean_dec(v___x_1927_);
                                crate::leanh::lean_dec(v___x_1978_);
                                v___x_1986_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1986_, 0, v_term_x3f_1985_);
                                v_term_x3f_1970_ = v___x_1986_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_1978_);
                            crate::leanh::lean_dec(v___x_1927_);
                            v___x_1987_ = crate::leanh::lean_box(0);
                            v_term_x3f_1970_ = v___x_1987_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1924_);
                    crate::leanh::lean_dec_ref(v___x_1923_);
                    crate::leanh::lean_dec_ref(v___x_1922_);
                    v___f_1988_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_elabTerminationHints___redArg___lam__3
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_1988_, 0, v___f_1930_);
                    v___x_1998_ = l_Lean_Syntax_getArg(v_val_1931_, v___x_1927_);
                    v___x_1999_ = l_Lean_Syntax_isNone(v___x_1998_);
                    if v___x_1999_ == 0 {
                        v___x_2000_ = crate::leanh::lean_unsigned_to_nat(2);
                        crate::leanh::lean_inc(v___x_1998_);
                        v___x_2001_ = l_Lean_Syntax_matchesNull(v___x_1998_, v___x_2000_);
                        if v___x_2001_ == 0 {
                            crate::leanh::lean_dec(v___x_1998_);
                            crate::leanh::lean_del_object(v___x_1933_);
                            crate::leanh::lean_dec(v_val_1931_);
                            crate::leanh::lean_dec(v___x_1927_);
                            v___x_2002_ = crate::leanh::lean_box(0);
                            v___x_2003_ = crate::leanh::lean_apply_2(
                                v_toPure_1917_,
                                crate::leanh::lean_box(0),
                                v___x_2002_,
                            );
                            v___x_2004_ = crate::leanh::lean_apply_4(
                                v_toBind_1919_,
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_2003_,
                                v___f_1988_,
                            );
                            return v___x_2004_;
                        } else {
                            v_term_x3f_2005_ = l_Lean_Syntax_getArg(v___x_1998_, v___x_1927_);
                            crate::leanh::lean_dec(v___x_1927_);
                            crate::leanh::lean_dec(v___x_1998_);
                            v___x_2006_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2006_, 0, v_term_x3f_2005_);
                            v_term_x3f_1990_ = v___x_2006_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1998_);
                        crate::leanh::lean_dec(v___x_1927_);
                        v___x_2007_ = crate::leanh::lean_box(0);
                        v_term_x3f_1990_ = v___x_2007_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1951_ = 2;
                v___x_1952_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1952_, 0, v_val_1931_);
                crate::leanh::lean_ctor_set(v___x_1952_, 1, v_term_x3f_1950_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1952_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_1951_,
                );
                if v_isShared_1934_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1933_, 0, v___x_1952_);
                    v___x_1954_ = v___x_1933_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1957_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1952_);
                    v___x_1954_ = v_reuseFailAlloc_1957_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1955_ = crate::leanh::lean_apply_2(
                    v_toPure_1917_,
                    crate::leanh::lean_box(0),
                    v___x_1954_,
                );
                v___x_1956_ = crate::leanh::lean_apply_4(
                    v_toBind_1919_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1955_,
                    v___f_1948_,
                );
                return v___x_1956_;
            }
            4 => {
                v___x_1971_ = 1;
                v___x_1972_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1972_, 0, v_val_1931_);
                crate::leanh::lean_ctor_set(v___x_1972_, 1, v_term_x3f_1970_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1972_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_1971_,
                );
                if v_isShared_1934_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1933_, 0, v___x_1972_);
                    v___x_1974_ = v___x_1933_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1977_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1972_);
                    v___x_1974_ = v_reuseFailAlloc_1977_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1975_ = crate::leanh::lean_apply_2(
                    v_toPure_1917_,
                    crate::leanh::lean_box(0),
                    v___x_1974_,
                );
                v___x_1976_ = crate::leanh::lean_apply_4(
                    v_toBind_1919_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1975_,
                    v___f_1968_,
                );
                return v___x_1976_;
            }
            6 => {
                v___x_1991_ = 0;
                v___x_1992_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1992_, 0, v_val_1931_);
                crate::leanh::lean_ctor_set(v___x_1992_, 1, v_term_x3f_1990_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1992_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_1991_,
                );
                if v_isShared_1934_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1933_, 0, v___x_1992_);
                    v___x_1994_ = v___x_1933_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1997_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1992_);
                    v___x_1994_ = v_reuseFailAlloc_1997_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1995_ = crate::leanh::lean_apply_2(
                    v_toPure_1917_,
                    crate::leanh::lean_box(0),
                    v___x_1994_,
                );
                v___x_1996_ = crate::leanh::lean_apply_4(
                    v_toBind_1919_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1995_,
                    v___f_1988_,
                );
                return v___x_1996_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_elabTerminationHints___redArg___lam__4(
    mut v___f_2013_: *mut crate::leanh::LeanObject,
    mut v_terminationBy_x3f_2014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2015_ = crate::leanh::lean_apply_1(v___f_2013_, v_terminationBy_x3f_2014_);
    return v___x_2015_;
}
pub unsafe fn _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2019_ = l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__2;
    v___x_2020_ = l_Lean_stringToMessageData(v___x_2019_);
    return v___x_2020_;
}
pub unsafe fn _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2022_ = l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__4;
    v___x_2023_ = l_Lean_stringToMessageData(v___x_2022_);
    return v___x_2023_;
}
pub unsafe fn l_Lean_Elab_elabTerminationHints___redArg___lam__19(
    mut v_stx_2024_: *mut crate::leanh::LeanObject,
    mut v___x_2025_: *mut crate::leanh::LeanObject,
    mut v_toPure_2026_: *mut crate::leanh::LeanObject,
    mut v_d_x3f_2027_: *mut crate::leanh::LeanObject,
    mut v_toBind_2028_: *mut crate::leanh::LeanObject,
    mut v_toFunctor_2029_: *mut crate::leanh::LeanObject,
    mut v___f_2030_: *mut crate::leanh::LeanObject,
    mut v___x_2031_: *mut crate::leanh::LeanObject,
    mut v___x_2032_: *mut crate::leanh::LeanObject,
    mut v___x_2033_: *mut crate::leanh::LeanObject,
    mut v_inst_2034_: *mut crate::leanh::LeanObject,
    mut v_inst_2035_: *mut crate::leanh::LeanObject,
    mut v___x_2036_: *mut crate::leanh::LeanObject,
    mut v_t_x3f_2037_: *mut crate::leanh::LeanObject,
    mut v_terminationBy_x3f_x3f_2038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2043_: u8 = 0;
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: u8 = 0;
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: u8 = 0;
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: u8 = 0;
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: u8 = 0;
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: u8 = 0;
    let mut v___f_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: u8 = 0;
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: u8 = 0;
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: u8 = 0;
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: u8 = 0;
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: u8 = 0;
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: u8 = 0;
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2107_: u8 = 0;
    let mut v___y_2108_: u8 = 0;
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2117_: u8 = 0;
    let mut v___y_2118_: u8 = 0;
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: u8 = 0;
    let mut v___x_2129_: u8 = 0;
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: u8 = 0;
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: u8 = 0;
    let mut v___x_2145_: u8 = 0;
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2152_: u8 = 0;
    let mut v___f_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_t_x3f_2037_);
                crate::leanh::lean_inc(v___x_2036_);
                crate::leanh::lean_inc_ref(v_inst_2035_);
                crate::leanh::lean_inc_ref(v_inst_2034_);
                crate::leanh::lean_inc_ref(v___x_2033_);
                crate::leanh::lean_inc_ref(v___x_2032_);
                crate::leanh::lean_inc_ref(v___x_2031_);
                crate::leanh::lean_inc(v_toBind_2028_);
                crate::leanh::lean_inc(v_toPure_2026_);
                crate::leanh::lean_inc(v___x_2025_);
                v___f_2039_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_elabTerminationHints___redArg___lam__11 as *mut core::ffi::c_void,
                    16,
                    15,
                );
                crate::leanh::lean_closure_set(v___f_2039_, 0, v_stx_2024_);
                crate::leanh::lean_closure_set(v___f_2039_, 1, v_terminationBy_x3f_x3f_2038_);
                crate::leanh::lean_closure_set(v___f_2039_, 2, v___x_2025_);
                crate::leanh::lean_closure_set(v___f_2039_, 3, v_toPure_2026_);
                crate::leanh::lean_closure_set(v___f_2039_, 4, v_d_x3f_2027_);
                crate::leanh::lean_closure_set(v___f_2039_, 5, v_toBind_2028_);
                crate::leanh::lean_closure_set(v___f_2039_, 6, v_toFunctor_2029_);
                crate::leanh::lean_closure_set(v___f_2039_, 7, v___f_2030_);
                crate::leanh::lean_closure_set(v___f_2039_, 8, v___x_2031_);
                crate::leanh::lean_closure_set(v___f_2039_, 9, v___x_2032_);
                crate::leanh::lean_closure_set(v___f_2039_, 10, v___x_2033_);
                crate::leanh::lean_closure_set(v___f_2039_, 11, v_inst_2034_);
                crate::leanh::lean_closure_set(v___f_2039_, 12, v_inst_2035_);
                crate::leanh::lean_closure_set(v___f_2039_, 13, v___x_2036_);
                crate::leanh::lean_closure_set(v___f_2039_, 14, v_t_x3f_2037_);
                if crate::leanh::lean_obj_tag(v_t_x3f_2037_) == 1 {
                    v_val_2040_ = crate::leanh::lean_ctor_get(v_t_x3f_2037_, 0);
                    v_isSharedCheck_2152_ = (!crate::leanh::lean_is_exclusive(v_t_x3f_2037_)) as u8;
                    if v_isSharedCheck_2152_ == 0 {
                        v___x_2042_ = v_t_x3f_2037_;
                        v_isShared_2043_ = v_isSharedCheck_2152_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2040_);
                        crate::leanh::lean_dec(v_t_x3f_2037_);
                        v___x_2042_ = crate::leanh::lean_box(0);
                        v_isShared_2043_ = v_isSharedCheck_2152_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_t_x3f_2037_);
                    crate::leanh::lean_dec(v___x_2036_);
                    crate::leanh::lean_dec_ref(v_inst_2035_);
                    crate::leanh::lean_dec_ref(v_inst_2034_);
                    crate::leanh::lean_dec_ref(v___x_2033_);
                    crate::leanh::lean_dec_ref(v___x_2032_);
                    crate::leanh::lean_dec_ref(v___x_2031_);
                    crate::leanh::lean_dec(v___x_2025_);
                    v___f_2153_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_elabTerminationHints___redArg___lam__4
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_2153_, 0, v___f_2039_);
                    v___x_2154_ = crate::leanh::lean_box(0);
                    v___x_2155_ = crate::leanh::lean_apply_2(
                        v_toPure_2026_,
                        crate::leanh::lean_box(0),
                        v___x_2154_,
                    );
                    v___x_2156_ = crate::leanh::lean_apply_4(
                        v_toBind_2028_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_2155_,
                        v___f_2153_,
                    );
                    return v___x_2156_;
                }
            }
            1 => {
                v___x_2044_ = l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__0;
                crate::leanh::lean_inc_ref(v___x_2033_);
                crate::leanh::lean_inc_ref(v___x_2032_);
                crate::leanh::lean_inc_ref(v___x_2031_);
                v___x_2045_ =
                    l_Lean_Name_mkStr4(v___x_2031_, v___x_2032_, v___x_2033_, v___x_2044_);
                crate::leanh::lean_inc(v_val_2040_);
                v___x_2046_ = l_Lean_Syntax_isOfKind(v_val_2040_, v___x_2045_);
                crate::leanh::lean_dec(v___x_2045_);
                if v___x_2046_ == 0 {
                    crate::leanh::lean_del_object(v___x_2042_);
                    crate::leanh::lean_dec(v___x_2025_);
                    v___x_2047_ = l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__1;
                    crate::leanh::lean_inc_ref(v___x_2033_);
                    crate::leanh::lean_inc_ref(v___x_2032_);
                    crate::leanh::lean_inc_ref(v___x_2031_);
                    v___x_2048_ =
                        l_Lean_Name_mkStr4(v___x_2031_, v___x_2032_, v___x_2033_, v___x_2047_);
                    crate::leanh::lean_inc(v_val_2040_);
                    v___x_2049_ = l_Lean_Syntax_isOfKind(v_val_2040_, v___x_2048_);
                    crate::leanh::lean_dec(v___x_2048_);
                    if v___x_2049_ == 0 {
                        v___x_2050_ =
                            l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0;
                        crate::leanh::lean_inc_ref(v___x_2033_);
                        crate::leanh::lean_inc_ref(v___x_2032_);
                        crate::leanh::lean_inc_ref(v___x_2031_);
                        v___x_2051_ =
                            l_Lean_Name_mkStr4(v___x_2031_, v___x_2032_, v___x_2033_, v___x_2050_);
                        crate::leanh::lean_inc(v_val_2040_);
                        v___x_2052_ = l_Lean_Syntax_isOfKind(v_val_2040_, v___x_2051_);
                        crate::leanh::lean_dec(v___x_2051_);
                        if v___x_2052_ == 0 {
                            v___x_2053_ =
                                l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1;
                            crate::leanh::lean_inc_ref(v___x_2033_);
                            crate::leanh::lean_inc_ref(v___x_2032_);
                            crate::leanh::lean_inc_ref(v___x_2031_);
                            v___x_2054_ = l_Lean_Name_mkStr4(
                                v___x_2031_,
                                v___x_2032_,
                                v___x_2033_,
                                v___x_2053_,
                            );
                            crate::leanh::lean_inc(v_val_2040_);
                            v___x_2055_ = l_Lean_Syntax_isOfKind(v_val_2040_, v___x_2054_);
                            crate::leanh::lean_dec(v___x_2054_);
                            if v___x_2055_ == 0 {
                                v___x_2056_ =
                                    l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2;
                                v___x_2057_ = l_Lean_Name_mkStr4(
                                    v___x_2031_,
                                    v___x_2032_,
                                    v___x_2033_,
                                    v___x_2056_,
                                );
                                crate::leanh::lean_inc(v_val_2040_);
                                v___x_2058_ = l_Lean_Syntax_isOfKind(v_val_2040_, v___x_2057_);
                                crate::leanh::lean_dec(v___x_2057_);
                                if v___x_2058_ == 0 {
                                    crate::leanh::lean_dec(v___x_2036_);
                                    crate::leanh::lean_dec(v_toPure_2026_);
                                    v___f_2059_ = crate::leanh::lean_alloc_closure(
                                        l_Lean_Elab_elabTerminationHints___redArg___lam__4
                                            as *mut core::ffi::c_void,
                                        2,
                                        1,
                                    );
                                    crate::leanh::lean_closure_set(v___f_2059_, 0, v___f_2039_);
                                    v___x_2060_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once), _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
                                    v___x_2061_ = l_Lean_throwErrorAt___redArg(
                                        v_inst_2034_,
                                        v_inst_2035_,
                                        v_val_2040_,
                                        v___x_2060_,
                                    );
                                    v___x_2062_ = crate::leanh::lean_apply_4(
                                        v_toBind_2028_,
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        v___x_2061_,
                                        v___f_2059_,
                                    );
                                    return v___x_2062_;
                                } else {
                                    v___f_2063_ = crate::leanh::lean_alloc_closure(
                                        l_Lean_Elab_elabTerminationHints___redArg___lam__4
                                            as *mut core::ffi::c_void,
                                        2,
                                        1,
                                    );
                                    crate::leanh::lean_closure_set(v___f_2063_, 0, v___f_2039_);
                                    v___x_2068_ = l_Lean_Syntax_getArg(v_val_2040_, v___x_2036_);
                                    crate::leanh::lean_dec(v___x_2036_);
                                    v___x_2069_ = l_Lean_Syntax_isNone(v___x_2068_);
                                    if v___x_2069_ == 0 {
                                        v___x_2070_ = crate::leanh::lean_unsigned_to_nat(2);
                                        v___x_2071_ =
                                            l_Lean_Syntax_matchesNull(v___x_2068_, v___x_2070_);
                                        if v___x_2071_ == 0 {
                                            crate::leanh::lean_dec(v_toPure_2026_);
                                            v___x_2072_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once), _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
                                            v___x_2073_ = l_Lean_throwErrorAt___redArg(
                                                v_inst_2034_,
                                                v_inst_2035_,
                                                v_val_2040_,
                                                v___x_2072_,
                                            );
                                            v___x_2074_ = crate::leanh::lean_apply_4(
                                                v_toBind_2028_,
                                                crate::leanh::lean_box(0),
                                                crate::leanh::lean_box(0),
                                                v___x_2073_,
                                                v___f_2063_,
                                            );
                                            return v___x_2074_;
                                        } else {
                                            crate::leanh::lean_dec(v_val_2040_);
                                            crate::leanh::lean_dec_ref(v_inst_2035_);
                                            crate::leanh::lean_dec_ref(v_inst_2034_);
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v___x_2068_);
                                        crate::leanh::lean_dec(v_val_2040_);
                                        crate::leanh::lean_dec_ref(v_inst_2035_);
                                        crate::leanh::lean_dec_ref(v_inst_2034_);
                                        state = 2;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_2033_);
                                crate::leanh::lean_dec_ref(v___x_2032_);
                                crate::leanh::lean_dec_ref(v___x_2031_);
                                v___f_2075_ = crate::leanh::lean_alloc_closure(
                                    l_Lean_Elab_elabTerminationHints___redArg___lam__4
                                        as *mut core::ffi::c_void,
                                    2,
                                    1,
                                );
                                crate::leanh::lean_closure_set(v___f_2075_, 0, v___f_2039_);
                                v___x_2080_ = l_Lean_Syntax_getArg(v_val_2040_, v___x_2036_);
                                crate::leanh::lean_dec(v___x_2036_);
                                v___x_2081_ = l_Lean_Syntax_isNone(v___x_2080_);
                                if v___x_2081_ == 0 {
                                    v___x_2082_ = crate::leanh::lean_unsigned_to_nat(2);
                                    v___x_2083_ =
                                        l_Lean_Syntax_matchesNull(v___x_2080_, v___x_2082_);
                                    if v___x_2083_ == 0 {
                                        crate::leanh::lean_dec(v_toPure_2026_);
                                        v___x_2084_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once), _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
                                        v___x_2085_ = l_Lean_throwErrorAt___redArg(
                                            v_inst_2034_,
                                            v_inst_2035_,
                                            v_val_2040_,
                                            v___x_2084_,
                                        );
                                        v___x_2086_ = crate::leanh::lean_apply_4(
                                            v_toBind_2028_,
                                            crate::leanh::lean_box(0),
                                            crate::leanh::lean_box(0),
                                            v___x_2085_,
                                            v___f_2075_,
                                        );
                                        return v___x_2086_;
                                    } else {
                                        crate::leanh::lean_dec(v_val_2040_);
                                        crate::leanh::lean_dec_ref(v_inst_2035_);
                                        crate::leanh::lean_dec_ref(v_inst_2034_);
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___x_2080_);
                                    crate::leanh::lean_dec(v_val_2040_);
                                    crate::leanh::lean_dec_ref(v_inst_2035_);
                                    crate::leanh::lean_dec_ref(v_inst_2034_);
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2033_);
                            crate::leanh::lean_dec_ref(v___x_2032_);
                            crate::leanh::lean_dec_ref(v___x_2031_);
                            v___f_2087_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Elab_elabTerminationHints___redArg___lam__4
                                    as *mut core::ffi::c_void,
                                2,
                                1,
                            );
                            crate::leanh::lean_closure_set(v___f_2087_, 0, v___f_2039_);
                            v___x_2092_ = l_Lean_Syntax_getArg(v_val_2040_, v___x_2036_);
                            crate::leanh::lean_dec(v___x_2036_);
                            v___x_2093_ = l_Lean_Syntax_isNone(v___x_2092_);
                            if v___x_2093_ == 0 {
                                v___x_2094_ = crate::leanh::lean_unsigned_to_nat(2);
                                v___x_2095_ = l_Lean_Syntax_matchesNull(v___x_2092_, v___x_2094_);
                                if v___x_2095_ == 0 {
                                    crate::leanh::lean_dec(v_toPure_2026_);
                                    v___x_2096_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once), _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
                                    v___x_2097_ = l_Lean_throwErrorAt___redArg(
                                        v_inst_2034_,
                                        v_inst_2035_,
                                        v_val_2040_,
                                        v___x_2096_,
                                    );
                                    v___x_2098_ = crate::leanh::lean_apply_4(
                                        v_toBind_2028_,
                                        crate::leanh::lean_box(0),
                                        crate::leanh::lean_box(0),
                                        v___x_2097_,
                                        v___f_2087_,
                                    );
                                    return v___x_2098_;
                                } else {
                                    crate::leanh::lean_dec(v_val_2040_);
                                    crate::leanh::lean_dec_ref(v_inst_2035_);
                                    crate::leanh::lean_dec_ref(v_inst_2034_);
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_2092_);
                                crate::leanh::lean_dec(v_val_2040_);
                                crate::leanh::lean_dec_ref(v_inst_2035_);
                                crate::leanh::lean_dec_ref(v_inst_2034_);
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_2040_);
                        crate::leanh::lean_dec(v___x_2036_);
                        crate::leanh::lean_dec_ref(v_inst_2035_);
                        crate::leanh::lean_dec_ref(v_inst_2034_);
                        crate::leanh::lean_dec_ref(v___x_2033_);
                        crate::leanh::lean_dec_ref(v___x_2032_);
                        crate::leanh::lean_dec_ref(v___x_2031_);
                        v___f_2099_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Elab_elabTerminationHints___redArg___lam__4
                                as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___f_2099_, 0, v___f_2039_);
                        v___x_2100_ = crate::leanh::lean_box(0);
                        v___x_2101_ = crate::leanh::lean_apply_2(
                            v_toPure_2026_,
                            crate::leanh::lean_box(0),
                            v___x_2100_,
                        );
                        v___x_2102_ = crate::leanh::lean_apply_4(
                            v_toBind_2028_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_2101_,
                            v___f_2099_,
                        );
                        return v___x_2102_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2033_);
                    crate::leanh::lean_dec_ref(v___x_2032_);
                    crate::leanh::lean_dec_ref(v___x_2031_);
                    v___f_2103_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_elabTerminationHints___redArg___lam__4
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_2103_, 0, v___f_2039_);
                    v___x_2143_ = l_Lean_Syntax_getArg(v_val_2040_, v___x_2036_);
                    v___x_2144_ = l_Lean_Syntax_isNone(v___x_2143_);
                    if v___x_2144_ == 0 {
                        crate::leanh::lean_inc(v___x_2143_);
                        v___x_2145_ = l_Lean_Syntax_matchesNull(v___x_2143_, v___x_2036_);
                        crate::leanh::lean_dec(v___x_2036_);
                        if v___x_2145_ == 0 {
                            crate::leanh::lean_dec(v___x_2143_);
                            crate::leanh::lean_del_object(v___x_2042_);
                            crate::leanh::lean_dec(v_toPure_2026_);
                            crate::leanh::lean_dec(v___x_2025_);
                            v___x_2146_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once), _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
                            v___x_2147_ = l_Lean_throwErrorAt___redArg(
                                v_inst_2034_,
                                v_inst_2035_,
                                v_val_2040_,
                                v___x_2146_,
                            );
                            v___x_2148_ = crate::leanh::lean_apply_4(
                                v_toBind_2028_,
                                crate::leanh::lean_box(0),
                                crate::leanh::lean_box(0),
                                v___x_2147_,
                                v___f_2103_,
                            );
                            return v___x_2148_;
                        } else {
                            v_s_2149_ = l_Lean_Syntax_getArg(v___x_2143_, v___x_2025_);
                            crate::leanh::lean_dec(v___x_2143_);
                            v___x_2150_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2150_, 0, v_s_2149_);
                            v_s_2125_ = v___x_2150_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2143_);
                        crate::leanh::lean_dec(v___x_2036_);
                        v___x_2151_ = crate::leanh::lean_box(0);
                        v_s_2125_ = v___x_2151_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2065_ = crate::leanh::lean_box(0);
                v___x_2066_ = crate::leanh::lean_apply_2(
                    v_toPure_2026_,
                    crate::leanh::lean_box(0),
                    v___x_2065_,
                );
                v___x_2067_ = crate::leanh::lean_apply_4(
                    v_toBind_2028_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2066_,
                    v___f_2063_,
                );
                return v___x_2067_;
            }
            3 => {
                v___x_2077_ = crate::leanh::lean_box(0);
                v___x_2078_ = crate::leanh::lean_apply_2(
                    v_toPure_2026_,
                    crate::leanh::lean_box(0),
                    v___x_2077_,
                );
                v___x_2079_ = crate::leanh::lean_apply_4(
                    v_toBind_2028_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2078_,
                    v___f_2075_,
                );
                return v___x_2079_;
            }
            4 => {
                v___x_2089_ = crate::leanh::lean_box(0);
                v___x_2090_ = crate::leanh::lean_apply_2(
                    v_toPure_2026_,
                    crate::leanh::lean_box(0),
                    v___x_2089_,
                );
                v___x_2091_ = crate::leanh::lean_apply_4(
                    v_toBind_2028_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2090_,
                    v___f_2087_,
                );
                return v___x_2091_;
            }
            5 => {
                v___x_2109_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_2109_, 0, v_val_2040_);
                crate::leanh::lean_ctor_set(v___x_2109_, 1, v___y_2105_);
                crate::leanh::lean_ctor_set(v___x_2109_, 2, v___y_2106_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2109_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___y_2108_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2109_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    v___y_2107_,
                );
                if v_isShared_2043_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2042_, 0, v___x_2109_);
                    v___x_2111_ = v___x_2042_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2114_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2109_);
                    v___x_2111_ = v_reuseFailAlloc_2114_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2112_ = crate::leanh::lean_apply_2(
                    v_toPure_2026_,
                    crate::leanh::lean_box(0),
                    v___x_2111_,
                );
                v___x_2113_ = crate::leanh::lean_apply_4(
                    v_toBind_2028_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2112_,
                    v___f_2103_,
                );
                return v___x_2113_;
            }
            7 => {
                v___x_2119_ = lean_mk_empty_array_with_capacity(v___x_2025_);
                crate::leanh::lean_dec(v___x_2025_);
                v___x_2120_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_2120_, 0, v_val_2040_);
                crate::leanh::lean_ctor_set(v___x_2120_, 1, v___x_2119_);
                crate::leanh::lean_ctor_set(v___x_2120_, 2, v___y_2116_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2120_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___y_2118_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2120_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                    v___y_2117_,
                );
                v___x_2121_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2121_, 0, v___x_2120_);
                v___x_2122_ = crate::leanh::lean_apply_2(
                    v_toPure_2026_,
                    crate::leanh::lean_box(0),
                    v___x_2121_,
                );
                v___x_2123_ = crate::leanh::lean_apply_4(
                    v_toBind_2028_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2122_,
                    v___f_2103_,
                );
                return v___x_2123_;
            }
            8 => {
                v___x_2126_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2127_ = l_Lean_Syntax_getArg(v_val_2040_, v___x_2126_);
                crate::leanh::lean_inc(v___x_2127_);
                v___x_2128_ = l_Lean_Syntax_matchesNull(v___x_2127_, v___x_2126_);
                if v___x_2128_ == 0 {
                    crate::leanh::lean_del_object(v___x_2042_);
                    v___x_2129_ = l_Lean_Syntax_matchesNull(v___x_2127_, v___x_2025_);
                    if v___x_2129_ == 0 {
                        crate::leanh::lean_dec(v_s_2125_);
                        crate::leanh::lean_dec(v_toPure_2026_);
                        crate::leanh::lean_dec(v___x_2025_);
                        v___x_2130_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once), _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
                        v___x_2131_ = l_Lean_throwErrorAt___redArg(
                            v_inst_2034_,
                            v_inst_2035_,
                            v_val_2040_,
                            v___x_2130_,
                        );
                        v___x_2132_ = crate::leanh::lean_apply_4(
                            v_toBind_2028_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_2131_,
                            v___f_2103_,
                        );
                        return v___x_2132_;
                    } else {
                        crate::leanh::lean_dec_ref(v_inst_2035_);
                        crate::leanh::lean_dec_ref(v_inst_2034_);
                        v___x_2133_ = crate::leanh::lean_unsigned_to_nat(3);
                        v_body_2134_ = l_Lean_Syntax_getArg(v_val_2040_, v___x_2133_);
                        if crate::leanh::lean_obj_tag(v_s_2125_) == 0 {
                            v___y_2116_ = v_body_2134_;
                            v___y_2117_ = v___x_2128_;
                            v___y_2118_ = v___x_2128_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_s_2125_, 1);
                            v___y_2116_ = v_body_2134_;
                            v___y_2117_ = v___x_2128_;
                            v___y_2118_ = v___x_2129_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v___x_2135_ = l_Lean_Syntax_getArg(v___x_2127_, v___x_2025_);
                    crate::leanh::lean_dec(v___x_2127_);
                    crate::leanh::lean_inc(v___x_2135_);
                    v___x_2136_ = l_Lean_Syntax_matchesNull(v___x_2135_, v___x_2025_);
                    crate::leanh::lean_dec(v___x_2025_);
                    if v___x_2136_ == 0 {
                        crate::leanh::lean_dec_ref(v_inst_2035_);
                        crate::leanh::lean_dec_ref(v_inst_2034_);
                        v___x_2137_ = crate::leanh::lean_unsigned_to_nat(3);
                        v_body_2138_ = l_Lean_Syntax_getArg(v_val_2040_, v___x_2137_);
                        v_vars_2139_ = l_Lean_Syntax_getArgs(v___x_2135_);
                        crate::leanh::lean_dec(v___x_2135_);
                        if crate::leanh::lean_obj_tag(v_s_2125_) == 0 {
                            v___y_2105_ = v_vars_2139_;
                            v___y_2106_ = v_body_2138_;
                            v___y_2107_ = v___x_2136_;
                            v___y_2108_ = v___x_2136_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_s_2125_, 1);
                            v___y_2105_ = v_vars_2139_;
                            v___y_2106_ = v_body_2138_;
                            v___y_2107_ = v___x_2136_;
                            v___y_2108_ = v___x_2128_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2135_);
                        crate::leanh::lean_dec(v_s_2125_);
                        crate::leanh::lean_del_object(v___x_2042_);
                        crate::leanh::lean_dec(v_toPure_2026_);
                        v___x_2140_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5_once), _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5);
                        v___x_2141_ = l_Lean_throwErrorAt___redArg(
                            v_inst_2034_,
                            v_inst_2035_,
                            v_val_2040_,
                            v___x_2140_,
                        );
                        v___x_2142_ = crate::leanh::lean_apply_4(
                            v_toBind_2028_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_2141_,
                            v___f_2103_,
                        );
                        return v___x_2142_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_elabTerminationHints___redArg___lam__5(
    mut v___f_2157_: *mut crate::leanh::LeanObject,
    mut v_terminationBy_x3f_x3f_2158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2159_ = crate::leanh::lean_apply_1(v___f_2157_, v_terminationBy_x3f_x3f_2158_);
    return v___x_2159_;
}
pub unsafe fn l_Lean_Elab_elabTerminationHints___redArg(
    mut v_inst_2182_: *mut crate::leanh::LeanObject,
    mut v_inst_2183_: *mut crate::leanh::LeanObject,
    mut v_stx_2184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: u8 = 0;
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: u8 = 0;
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_x3f_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2226_: u8 = 0;
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: u8 = 0;
    let mut v___f_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2239_: u8 = 0;
    let mut v___f_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_x3f_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: u8 = 0;
    let mut v___x_2249_: u8 = 0;
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_x3f_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: u8 = 0;
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: u8 = 0;
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: u8 = 0;
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_x3f_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_stx_2184_) == 0 {
                    v_toApplicative_2185_ = crate::leanh::lean_ctor_get(v_inst_2182_, 0);
                    crate::leanh::lean_inc_ref(v_toApplicative_2185_);
                    crate::leanh::lean_dec_ref(v_inst_2183_);
                    crate::leanh::lean_dec_ref(v_inst_2182_);
                    v_toPure_2186_ = crate::leanh::lean_ctor_get(v_toApplicative_2185_, 1);
                    crate::leanh::lean_inc(v_toPure_2186_);
                    crate::leanh::lean_dec_ref(v_toApplicative_2185_);
                    v___x_2187_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2188_ = crate::leanh::lean_box(0);
                    v___x_2189_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2189_, 0, v_stx_2184_);
                    crate::leanh::lean_ctor_set(v___x_2189_, 1, v___x_2188_);
                    crate::leanh::lean_ctor_set(v___x_2189_, 2, v___x_2188_);
                    crate::leanh::lean_ctor_set(v___x_2189_, 3, v___x_2188_);
                    crate::leanh::lean_ctor_set(v___x_2189_, 4, v___x_2188_);
                    crate::leanh::lean_ctor_set(v___x_2189_, 5, v___x_2187_);
                    v___x_2190_ = crate::leanh::lean_apply_2(
                        v_toPure_2186_,
                        crate::leanh::lean_box(0),
                        v___x_2189_,
                    );
                    return v___x_2190_;
                } else {
                    v_toApplicative_2191_ = crate::leanh::lean_ctor_get(v_inst_2182_, 0);
                    v_toBind_2192_ = crate::leanh::lean_ctor_get(v_inst_2182_, 1);
                    v_toFunctor_2193_ = crate::leanh::lean_ctor_get(v_toApplicative_2191_, 0);
                    v_toPure_2194_ = crate::leanh::lean_ctor_get(v_toApplicative_2191_, 1);
                    v___x_2195_ = l_Lean_Elab_elabTerminationHints___redArg___closed__0;
                    v___x_2196_ = l_Lean_Elab_elabTerminationHints___redArg___closed__1;
                    v___x_2197_ = l_Lean_Elab_elabTerminationHints___redArg___closed__2;
                    v___x_2198_ = l_Lean_Elab_elabTerminationHints___redArg___closed__4;
                    crate::leanh::lean_inc(v_stx_2184_);
                    v___x_2199_ = l_Lean_Syntax_isOfKind(v_stx_2184_, v___x_2198_);
                    if v___x_2199_ == 0 {
                        v___x_2200_ = l_Lean_Elab_elabTerminationHints___redArg___closed__5;
                        v___x_2201_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc_n(v_stx_2184_, 2);
                        v___x_2202_ =
                            l_Lean_Syntax_formatStx(v_stx_2184_, v___x_2201_, v___x_2199_);
                        v___x_2203_ = l_Std_Format_defWidth;
                        v___x_2204_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2205_ =
                            l_Std_Format_pretty(v___x_2202_, v___x_2203_, v___x_2204_, v___x_2204_);
                        v___x_2206_ = lean_string_append(v___x_2200_, v___x_2205_);
                        crate::leanh::lean_dec_ref(v___x_2205_);
                        v___x_2207_ = l_Lean_Elab_elabTerminationHints___redArg___closed__6;
                        v___x_2208_ = lean_string_append(v___x_2206_, v___x_2207_);
                        v___x_2209_ = l_Lean_Syntax_getKind(v_stx_2184_);
                        v___x_2210_ = 1;
                        v___x_2211_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v___x_2209_,
                                v___x_2210_,
                            );
                        v___x_2212_ = lean_string_append(v___x_2208_, v___x_2211_);
                        crate::leanh::lean_dec_ref(v___x_2211_);
                        v___x_2213_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2213_, 0, v___x_2212_);
                        v___x_2214_ = l_Lean_MessageData_ofFormat(v___x_2213_);
                        v___x_2215_ = l_Lean_throwErrorAt___redArg(
                            v_inst_2182_,
                            v_inst_2183_,
                            v_stx_2184_,
                            v___x_2214_,
                        );
                        return v___x_2215_;
                    } else {
                        v___f_2216_ = l_Lean_Elab_elabTerminationHints___redArg___closed__7;
                        v___x_2217_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2283_ = l_Lean_Syntax_getArg(v_stx_2184_, v___x_2217_);
                        v___x_2284_ = l_Lean_Syntax_isNone(v___x_2283_);
                        if v___x_2284_ == 0 {
                            v___x_2285_ = crate::leanh::lean_unsigned_to_nat(1);
                            crate::leanh::lean_inc(v___x_2283_);
                            v___x_2286_ = l_Lean_Syntax_matchesNull(v___x_2283_, v___x_2285_);
                            if v___x_2286_ == 0 {
                                crate::leanh::lean_dec(v___x_2283_);
                                v___x_2287_ = l_Lean_Elab_elabTerminationHints___redArg___closed__5;
                                v___x_2288_ = crate::leanh::lean_box(0);
                                crate::leanh::lean_inc_n(v_stx_2184_, 2);
                                v___x_2289_ =
                                    l_Lean_Syntax_formatStx(v_stx_2184_, v___x_2288_, v___x_2286_);
                                v___x_2290_ = l_Std_Format_defWidth;
                                v___x_2291_ = l_Std_Format_pretty(
                                    v___x_2289_,
                                    v___x_2290_,
                                    v___x_2217_,
                                    v___x_2217_,
                                );
                                v___x_2292_ = lean_string_append(v___x_2287_, v___x_2291_);
                                crate::leanh::lean_dec_ref(v___x_2291_);
                                v___x_2293_ = l_Lean_Elab_elabTerminationHints___redArg___closed__6;
                                v___x_2294_ = lean_string_append(v___x_2292_, v___x_2293_);
                                v___x_2295_ = l_Lean_Syntax_getKind(v_stx_2184_);
                                v___x_2296_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2295_, v___x_2199_);
                                v___x_2297_ = lean_string_append(v___x_2294_, v___x_2296_);
                                crate::leanh::lean_dec_ref(v___x_2296_);
                                v___x_2298_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2298_, 0, v___x_2297_);
                                v___x_2299_ = l_Lean_MessageData_ofFormat(v___x_2298_);
                                v___x_2300_ = l_Lean_throwErrorAt___redArg(
                                    v_inst_2182_,
                                    v_inst_2183_,
                                    v_stx_2184_,
                                    v___x_2299_,
                                );
                                return v___x_2300_;
                            } else {
                                v_t_x3f_2301_ = l_Lean_Syntax_getArg(v___x_2283_, v___x_2217_);
                                crate::leanh::lean_dec(v___x_2283_);
                                v___x_2302_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2302_, 0, v_t_x3f_2301_);
                                v_t_x3f_2245_ = v___x_2302_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_2283_);
                            v___x_2303_ = crate::leanh::lean_box(0);
                            v_t_x3f_2245_ = v___x_2303_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_2219_);
                crate::leanh::lean_inc(v_toBind_2192_);
                crate::leanh::lean_inc(v_toPure_2194_);
                v___f_2222_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_elabTerminationHints___redArg___lam__19 as *mut core::ffi::c_void,
                    15,
                    14,
                );
                crate::leanh::lean_closure_set(v___f_2222_, 0, v_stx_2184_);
                crate::leanh::lean_closure_set(v___f_2222_, 1, v___x_2217_);
                crate::leanh::lean_closure_set(v___f_2222_, 2, v_toPure_2194_);
                crate::leanh::lean_closure_set(v___f_2222_, 3, v_d_x3f_2221_);
                crate::leanh::lean_closure_set(v___f_2222_, 4, v_toBind_2192_);
                crate::leanh::lean_closure_set(v___f_2222_, 5, v_toFunctor_2193_);
                crate::leanh::lean_closure_set(v___f_2222_, 6, v___f_2216_);
                crate::leanh::lean_closure_set(v___f_2222_, 7, v___x_2195_);
                crate::leanh::lean_closure_set(v___f_2222_, 8, v___x_2196_);
                crate::leanh::lean_closure_set(v___f_2222_, 9, v___x_2197_);
                crate::leanh::lean_closure_set(v___f_2222_, 10, v_inst_2182_);
                crate::leanh::lean_closure_set(v___f_2222_, 11, v_inst_2183_);
                crate::leanh::lean_closure_set(v___f_2222_, 12, v___y_2220_);
                crate::leanh::lean_closure_set(v___f_2222_, 13, v___y_2219_);
                if crate::leanh::lean_obj_tag(v___y_2219_) == 1 {
                    v_val_2223_ = crate::leanh::lean_ctor_get(v___y_2219_, 0);
                    v_isSharedCheck_2239_ = (!crate::leanh::lean_is_exclusive(v___y_2219_)) as u8;
                    if v_isSharedCheck_2239_ == 0 {
                        v___x_2225_ = v___y_2219_;
                        v_isShared_2226_ = v_isSharedCheck_2239_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2223_);
                        crate::leanh::lean_dec(v___y_2219_);
                        v___x_2225_ = crate::leanh::lean_box(0);
                        v_isShared_2226_ = v_isSharedCheck_2239_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2219_);
                    v___f_2240_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_elabTerminationHints___redArg___lam__5
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_2240_, 0, v___f_2222_);
                    v___x_2241_ = crate::leanh::lean_box(0);
                    v___x_2242_ = crate::leanh::lean_apply_2(
                        v_toPure_2194_,
                        crate::leanh::lean_box(0),
                        v___x_2241_,
                    );
                    v___x_2243_ = crate::leanh::lean_apply_4(
                        v_toBind_2192_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_2242_,
                        v___f_2240_,
                    );
                    return v___x_2243_;
                }
            }
            2 => {
                v___x_2227_ = l_Lean_Elab_elabTerminationHints___redArg___closed__8;
                crate::leanh::lean_inc(v_val_2223_);
                v___x_2228_ = l_Lean_Syntax_isOfKind(v_val_2223_, v___x_2227_);
                if v___x_2228_ == 0 {
                    crate::leanh::lean_del_object(v___x_2225_);
                    crate::leanh::lean_dec(v_val_2223_);
                    v___f_2229_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_elabTerminationHints___redArg___lam__5
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_2229_, 0, v___f_2222_);
                    v___x_2230_ = crate::leanh::lean_box(0);
                    v___x_2231_ = crate::leanh::lean_apply_2(
                        v_toPure_2194_,
                        crate::leanh::lean_box(0),
                        v___x_2230_,
                    );
                    v___x_2232_ = crate::leanh::lean_apply_4(
                        v_toBind_2192_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_2231_,
                        v___f_2229_,
                    );
                    return v___x_2232_;
                } else {
                    v___f_2233_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_elabTerminationHints___redArg___lam__5
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_2233_, 0, v___f_2222_);
                    if v_isShared_2226_ == 0 {
                        v___x_2235_ = v___x_2225_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2238_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_val_2223_);
                        v___x_2235_ = v_reuseFailAlloc_2238_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2236_ = crate::leanh::lean_apply_2(
                    v_toPure_2194_,
                    crate::leanh::lean_box(0),
                    v___x_2235_,
                );
                v___x_2237_ = crate::leanh::lean_apply_4(
                    v_toBind_2192_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2236_,
                    v___f_2233_,
                );
                return v___x_2237_;
            }
            4 => {
                v___x_2246_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2247_ = l_Lean_Syntax_getArg(v_stx_2184_, v___x_2246_);
                v___x_2248_ = l_Lean_Syntax_isNone(v___x_2247_);
                if v___x_2248_ == 0 {
                    crate::leanh::lean_inc(v___x_2247_);
                    v___x_2249_ = l_Lean_Syntax_matchesNull(v___x_2247_, v___x_2246_);
                    if v___x_2249_ == 0 {
                        crate::leanh::lean_dec(v___x_2247_);
                        crate::leanh::lean_dec(v_t_x3f_2245_);
                        v___x_2250_ = l_Lean_Elab_elabTerminationHints___redArg___closed__5;
                        v___x_2251_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc_n(v_stx_2184_, 2);
                        v___x_2252_ =
                            l_Lean_Syntax_formatStx(v_stx_2184_, v___x_2251_, v___x_2249_);
                        v___x_2253_ = l_Std_Format_defWidth;
                        v___x_2254_ =
                            l_Std_Format_pretty(v___x_2252_, v___x_2253_, v___x_2217_, v___x_2217_);
                        v___x_2255_ = lean_string_append(v___x_2250_, v___x_2254_);
                        crate::leanh::lean_dec_ref(v___x_2254_);
                        v___x_2256_ = l_Lean_Elab_elabTerminationHints___redArg___closed__6;
                        v___x_2257_ = lean_string_append(v___x_2255_, v___x_2256_);
                        v___x_2258_ = l_Lean_Syntax_getKind(v_stx_2184_);
                        v___x_2259_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v___x_2258_,
                                v___x_2199_,
                            );
                        v___x_2260_ = lean_string_append(v___x_2257_, v___x_2259_);
                        crate::leanh::lean_dec_ref(v___x_2259_);
                        v___x_2261_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2261_, 0, v___x_2260_);
                        v___x_2262_ = l_Lean_MessageData_ofFormat(v___x_2261_);
                        v___x_2263_ = l_Lean_throwErrorAt___redArg(
                            v_inst_2182_,
                            v_inst_2183_,
                            v_stx_2184_,
                            v___x_2262_,
                        );
                        return v___x_2263_;
                    } else {
                        v_d_x3f_2264_ = l_Lean_Syntax_getArg(v___x_2247_, v___x_2217_);
                        crate::leanh::lean_dec(v___x_2247_);
                        v___x_2265_ = l_Lean_Elab_elabTerminationHints___redArg___closed__9;
                        crate::leanh::lean_inc(v_d_x3f_2264_);
                        v___x_2266_ = l_Lean_Syntax_isOfKind(v_d_x3f_2264_, v___x_2265_);
                        if v___x_2266_ == 0 {
                            crate::leanh::lean_dec(v_d_x3f_2264_);
                            crate::leanh::lean_dec(v_t_x3f_2245_);
                            v___x_2267_ = l_Lean_Elab_elabTerminationHints___redArg___closed__5;
                            v___x_2268_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc_n(v_stx_2184_, 2);
                            v___x_2269_ =
                                l_Lean_Syntax_formatStx(v_stx_2184_, v___x_2268_, v___x_2266_);
                            v___x_2270_ = l_Std_Format_defWidth;
                            v___x_2271_ = l_Std_Format_pretty(
                                v___x_2269_,
                                v___x_2270_,
                                v___x_2217_,
                                v___x_2217_,
                            );
                            v___x_2272_ = lean_string_append(v___x_2267_, v___x_2271_);
                            crate::leanh::lean_dec_ref(v___x_2271_);
                            v___x_2273_ = l_Lean_Elab_elabTerminationHints___redArg___closed__6;
                            v___x_2274_ = lean_string_append(v___x_2272_, v___x_2273_);
                            v___x_2275_ = l_Lean_Syntax_getKind(v_stx_2184_);
                            v___x_2276_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v___x_2275_,
                                    v___x_2249_,
                                );
                            v___x_2277_ = lean_string_append(v___x_2274_, v___x_2276_);
                            crate::leanh::lean_dec_ref(v___x_2276_);
                            v___x_2278_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2278_, 0, v___x_2277_);
                            v___x_2279_ = l_Lean_MessageData_ofFormat(v___x_2278_);
                            v___x_2280_ = l_Lean_throwErrorAt___redArg(
                                v_inst_2182_,
                                v_inst_2183_,
                                v_stx_2184_,
                                v___x_2279_,
                            );
                            return v___x_2280_;
                        } else {
                            crate::leanh::lean_inc(v_toPure_2194_);
                            crate::leanh::lean_inc_ref(v_toFunctor_2193_);
                            crate::leanh::lean_inc(v_toBind_2192_);
                            v___x_2281_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2281_, 0, v_d_x3f_2264_);
                            v___y_2219_ = v_t_x3f_2245_;
                            v___y_2220_ = v___x_2246_;
                            v_d_x3f_2221_ = v___x_2281_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_toPure_2194_);
                    crate::leanh::lean_inc_ref(v_toFunctor_2193_);
                    crate::leanh::lean_inc(v_toBind_2192_);
                    crate::leanh::lean_dec(v___x_2247_);
                    v___x_2282_ = crate::leanh::lean_box(0);
                    v___y_2219_ = v_t_x3f_2245_;
                    v___y_2220_ = v___x_2246_;
                    v_d_x3f_2221_ = v___x_2282_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_elabTerminationHints(
    mut v_m_2304_: *mut crate::leanh::LeanObject,
    mut v_inst_2305_: *mut crate::leanh::LeanObject,
    mut v_inst_2306_: *mut crate::leanh::LeanObject,
    mut v_stx_2307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2308_ =
        l_Lean_Elab_elabTerminationHints___redArg(v_inst_2305_, v_inst_2306_, v_stx_2307_);
    return v___x_2308_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_TerminationHint(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Term(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Elab_instInhabitedPartialFixpointType_default =
        _init_l_Lean_Elab_instInhabitedPartialFixpointType_default();
    l_Lean_Elab_instInhabitedPartialFixpointType =
        _init_l_Lean_Elab_instInhabitedPartialFixpointType();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_TerminationHint(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Parser_Term(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_PreDefinition_TerminationHint(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Term(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Term(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_TerminationHint(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_TerminationHint(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_TerminationHint(builtin);
}

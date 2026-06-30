// Lean compiler output
// Module: Lean.Elab.PreDefinition.TerminationHint
// Imports: Lean.Parser.Term Lean.Parser.Term Init.Omega
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_mk_empty_array_with_capacity,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_string_append, lean_string_dec_eq,
};
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
pub static l_Lean_Elab_instInhabitedTerminationBy_default___closed__0_value:
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
static mut l_Lean_Elab_instInhabitedTerminationBy_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedTerminationBy_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instInhabitedTerminationBy_default___closed__1_value:
    leanh::LeanCtorObject<4> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 8) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_instInhabitedTerminationBy_default___closed__0_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        0 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instInhabitedTerminationBy_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedTerminationBy_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedTerminationBy_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedTerminationBy_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedTerminationBy: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedTerminationBy_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instInhabitedDecreasingBy_default___closed__0_value:
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
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instInhabitedDecreasingBy_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedDecreasingBy_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedDecreasingBy_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedDecreasingBy_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedDecreasingBy: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedDecreasingBy_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedPartialFixpointType_default: u8 = 0;
pub static mut l_Lean_Elab_instInhabitedPartialFixpointType: u8 = 0;
pub static l_Lean_Elab_instInhabitedPartialFixpoint_default___closed__0_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        0 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instInhabitedPartialFixpoint_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedPartialFixpoint_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedPartialFixpoint_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedPartialFixpoint_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedPartialFixpoint: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedPartialFixpoint_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_instInhabitedTerminationHints_default___closed__0_value:
    leanh::LeanCtorObject<6> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 6
            + 0) as u16,
        other: 6,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_instInhabitedTerminationHints_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedTerminationHints_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedTerminationHints_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedTerminationHints_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_instInhabitedTerminationHints: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedTerminationHints_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_TerminationHints_none: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_instInhabitedTerminationHints_default___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__3_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__5_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__6_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__7_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___closed__0_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_TerminationHints_ensureNone___closed__0_value:
    leanh::LeanStringObject<39> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationHints_ensureNone___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationHints_ensureNone___closed__2_value:
    leanh::LeanStringObject<40> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationHints_ensureNone___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationHints_ensureNone___closed__4_value:
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
        117, 110, 117, 115, 101, 100, 32, 96, 99, 111, 105, 110, 100, 117, 99, 116, 105, 118, 101,
        95, 102, 105, 120, 112, 111, 105, 110, 116, 96, 44, 32, 102, 117, 110, 99, 116, 105, 111,
        110, 32, 105, 115, 32, 0,
    ],
};
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationHints_ensureNone___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationHints_ensureNone___closed__6_value:
    leanh::LeanStringObject<42> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationHints_ensureNone___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationHints_ensureNone___closed__8_value:
    leanh::LeanStringObject<37> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationHints_ensureNone___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationHints_ensureNone___closed__10_value:
    leanh::LeanStringObject<38> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationHints_ensureNone___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationHints_ensureNone___closed__12_value:
    leanh::LeanStringObject<39> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationHints_ensureNone___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_TerminationHints_ensureNone___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__0_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 0]};
static mut l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [111, 110, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 0]};
static mut l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__2_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_TerminationBy_checkVars___closed__0_value: leanh::LeanStringObject<
    45,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_TerminationBy_checkVars___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationBy_checkVars___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationBy_checkVars___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_TerminationBy_checkVars___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationBy_checkVars___closed__2_value: leanh::LeanStringObject<
    13,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_TerminationBy_checkVars___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationBy_checkVars___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationBy_checkVars___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_TerminationBy_checkVars___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationBy_checkVars___closed__4_value: leanh::LeanStringObject<
    2,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_TerminationBy_checkVars___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationBy_checkVars___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationBy_checkVars___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_TerminationBy_checkVars___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationBy_checkVars___closed__6_value: leanh::LeanStringObject<
    6,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_TerminationBy_checkVars___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationBy_checkVars___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_TerminationBy_checkVars___closed__7_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_TerminationBy_checkVars___closed__6_value)
                as *mut leanh::LeanObject,
            5117844058249666356 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_TerminationBy_checkVars___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationBy_checkVars___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_TerminationBy_checkVars___closed__8_value: leanh::LeanStringObject<
    60,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_TerminationBy_checkVars___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationBy_checkVars___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationBy_checkVars___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_TerminationBy_checkVars___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_TerminationBy_checkVars___closed__10_value: leanh::LeanStringObject<
    33,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_TerminationBy_checkVars___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationBy_checkVars___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_TerminationBy_checkVars___closed__11_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_TerminationBy_checkVars___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_TerminationBy_checkVars___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_TerminationBy_checkVars___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_TerminationBy_checkVars___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_TerminationBy_checkVars___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__1_value:
    leanh::LeanStringObject<34> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0_value:
    leanh::LeanStringObject<16> = leanh::LeanStringObject {
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
        112, 97, 114, 116, 105, 97, 108, 70, 105, 120, 112, 111, 105, 110, 116, 0,
    ],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1_value:
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
        99, 111, 105, 110, 100, 117, 99, 116, 105, 118, 101, 70, 105, 120, 112, 111, 105, 110, 116,
        0,
    ],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2_value:
    leanh::LeanStringObject<18> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__0_value:
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
        116, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 66, 121, 0,
    ],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__1_value:
    leanh::LeanStringObject<15> = leanh::LeanStringObject {
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
        116, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 66, 121, 63, 0,
    ],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__2_value:
    leanh::LeanStringObject<35> = leanh::LeanStringObject {
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
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 96, 116, 101, 114, 109, 105, 110, 97,
        116, 105, 111, 110, 95, 98, 121, 96, 32, 115, 121, 110, 116, 97, 120, 0,
    ],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__4_value:
    leanh::LeanStringObject<49> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_elabTerminationHints___redArg___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_elabTerminationHints___redArg___closed__1_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_elabTerminationHints___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_elabTerminationHints___redArg___closed__2_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_elabTerminationHints___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_elabTerminationHints___redArg___closed__3_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_elabTerminationHints___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_elabTerminationHints___redArg___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_elabTerminationHints___redArg___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_elabTerminationHints___redArg___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__4_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        7625897890118033792 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_elabTerminationHints___redArg___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__4_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        8715860392475343861 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_elabTerminationHints___redArg___closed__5_value:
    leanh::LeanStringObject<39> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_elabTerminationHints___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_elabTerminationHints___redArg___closed__6_value:
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
    m_data: [32, 111, 102, 32, 107, 105, 110, 100, 32, 0],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_elabTerminationHints___redArg___closed__7_value:
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
    m_fun: l_Lean_Elab_elabTerminationHints___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__7_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_elabTerminationHints___redArg___closed__8_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_elabTerminationHints___redArg___closed__8_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__8_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_elabTerminationHints___redArg___closed__8_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__8_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        7625897890118033792 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_elabTerminationHints___redArg___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__8_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__1_value)
            as *mut leanh::LeanObject,
        12996790131644993504 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__8_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_elabTerminationHints___redArg___closed__9_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_elabTerminationHints___redArg___closed__9_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__9_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_elabTerminationHints___redArg___closed__9_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__9_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        7625897890118033792 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_elabTerminationHints___redArg___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__9_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__0_value)
            as *mut leanh::LeanObject,
        3331099446614607828 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_elabTerminationHints___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabTerminationHints___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Elab_PartialFixpointType_ctorIdx(
    mut v_x_1167_: u8,
) -> *mut leanh::LeanObject {
    match v_x_1167_ {
        0 => {
            let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1168_ = leanh::lean_unsigned_to_nat(0);
            return v___x_1168_;
        }
        1 => {
            let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1169_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1169_;
        }
        _ => {
            let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1170_ = leanh::lean_unsigned_to_nat(2);
            return v___x_1170_;
        }
    }
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_ctorIdx___boxed(
    mut v_x_1171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_1172_: u8 = 0;
    let mut v_res_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1172_ = (leanh::lean_unbox(v_x_1171_) as u8);
    v_res_1173_ = l_Lean_Elab_PartialFixpointType_ctorIdx(v_x_boxed_1172_);
    return v_res_1173_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_toCtorIdx(
    mut v_x_1174_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1175_ = l_Lean_Elab_PartialFixpointType_ctorIdx(v_x_1174_);
    return v___x_1175_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_toCtorIdx___boxed(
    mut v_x_1176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_1177_: u8 = 0;
    let mut v_res_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1177_ = (leanh::lean_unbox(v_x_1176_) as u8);
    v_res_1178_ = l_Lean_Elab_PartialFixpointType_toCtorIdx(v_x_4__boxed_1177_);
    return v_res_1178_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_ctorElim___redArg(
    mut v_k_1179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_1179_);
    return v_k_1179_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_ctorElim___redArg___boxed(
    mut v_k_1180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1181_ = l_Lean_Elab_PartialFixpointType_ctorElim___redArg(v_k_1180_);
    leanh::lean_dec(v_k_1180_);
    return v_res_1181_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_ctorElim(
    mut v_motive_1182_: *mut leanh::LeanObject,
    mut v_ctorIdx_1183_: *mut leanh::LeanObject,
    mut v_t_1184_: u8,
    mut v_h_1185_: *mut leanh::LeanObject,
    mut v_k_1186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_1186_);
    return v_k_1186_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_ctorElim___boxed(
    mut v_motive_1187_: *mut leanh::LeanObject,
    mut v_ctorIdx_1188_: *mut leanh::LeanObject,
    mut v_t_1189_: *mut leanh::LeanObject,
    mut v_h_1190_: *mut leanh::LeanObject,
    mut v_k_1191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1192_: u8 = 0;
    let mut v_res_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1192_ = (leanh::lean_unbox(v_t_1189_) as u8);
    v_res_1193_ = l_Lean_Elab_PartialFixpointType_ctorElim(
        v_motive_1187_,
        v_ctorIdx_1188_,
        v_t_boxed_1192_,
        v_h_1190_,
        v_k_1191_,
    );
    leanh::lean_dec(v_k_1191_);
    leanh::lean_dec(v_ctorIdx_1188_);
    return v_res_1193_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___redArg(
    mut v_partialFixpoint_1194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_partialFixpoint_1194_);
    return v_partialFixpoint_1194_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___redArg___boxed(
    mut v_partialFixpoint_1195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1196_ =
        l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___redArg(v_partialFixpoint_1195_);
    leanh::lean_dec(v_partialFixpoint_1195_);
    return v_res_1196_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_partialFixpoint_elim(
    mut v_motive_1197_: *mut leanh::LeanObject,
    mut v_t_1198_: u8,
    mut v_h_1199_: *mut leanh::LeanObject,
    mut v_partialFixpoint_1200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_partialFixpoint_1200_);
    return v_partialFixpoint_1200_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_partialFixpoint_elim___boxed(
    mut v_motive_1201_: *mut leanh::LeanObject,
    mut v_t_1202_: *mut leanh::LeanObject,
    mut v_h_1203_: *mut leanh::LeanObject,
    mut v_partialFixpoint_1204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1205_: u8 = 0;
    let mut v_res_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1205_ = (leanh::lean_unbox(v_t_1202_) as u8);
    v_res_1206_ = l_Lean_Elab_PartialFixpointType_partialFixpoint_elim(
        v_motive_1201_,
        v_t_boxed_1205_,
        v_h_1203_,
        v_partialFixpoint_1204_,
    );
    leanh::lean_dec(v_partialFixpoint_1204_);
    return v_res_1206_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___redArg(
    mut v_coinductiveFixpoint_1207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_coinductiveFixpoint_1207_);
    return v_coinductiveFixpoint_1207_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___redArg___boxed(
    mut v_coinductiveFixpoint_1208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1209_ = l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___redArg(
        v_coinductiveFixpoint_1208_,
    );
    leanh::lean_dec(v_coinductiveFixpoint_1208_);
    return v_res_1209_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim(
    mut v_motive_1210_: *mut leanh::LeanObject,
    mut v_t_1211_: u8,
    mut v_h_1212_: *mut leanh::LeanObject,
    mut v_coinductiveFixpoint_1213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_coinductiveFixpoint_1213_);
    return v_coinductiveFixpoint_1213_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim___boxed(
    mut v_motive_1214_: *mut leanh::LeanObject,
    mut v_t_1215_: *mut leanh::LeanObject,
    mut v_h_1216_: *mut leanh::LeanObject,
    mut v_coinductiveFixpoint_1217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1218_: u8 = 0;
    let mut v_res_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1218_ = (leanh::lean_unbox(v_t_1215_) as u8);
    v_res_1219_ = l_Lean_Elab_PartialFixpointType_coinductiveFixpoint_elim(
        v_motive_1214_,
        v_t_boxed_1218_,
        v_h_1216_,
        v_coinductiveFixpoint_1217_,
    );
    leanh::lean_dec(v_coinductiveFixpoint_1217_);
    return v_res_1219_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___redArg(
    mut v_inductiveFixpoint_1220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inductiveFixpoint_1220_);
    return v_inductiveFixpoint_1220_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___redArg___boxed(
    mut v_inductiveFixpoint_1221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1222_ =
        l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___redArg(v_inductiveFixpoint_1221_);
    leanh::lean_dec(v_inductiveFixpoint_1221_);
    return v_res_1222_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim(
    mut v_motive_1223_: *mut leanh::LeanObject,
    mut v_t_1224_: u8,
    mut v_h_1225_: *mut leanh::LeanObject,
    mut v_inductiveFixpoint_1226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inductiveFixpoint_1226_);
    return v_inductiveFixpoint_1226_;
}
pub unsafe fn l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim___boxed(
    mut v_motive_1227_: *mut leanh::LeanObject,
    mut v_t_1228_: *mut leanh::LeanObject,
    mut v_h_1229_: *mut leanh::LeanObject,
    mut v_inductiveFixpoint_1230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1231_: u8 = 0;
    let mut v_res_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1231_ = (leanh::lean_unbox(v_t_1228_) as u8);
    v_res_1232_ = l_Lean_Elab_PartialFixpointType_inductiveFixpoint_elim(
        v_motive_1227_,
        v_t_boxed_1231_,
        v_h_1229_,
        v_inductiveFixpoint_1230_,
    );
    leanh::lean_dec(v_inductiveFixpoint_1230_);
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
    mut v_x_1250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_21__boxed_1251_: u8 = 0;
    let mut v_res_1252_: u8 = 0;
    let mut v_r_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_21__boxed_1251_ = (leanh::lean_unbox(v_x_1250_) as u8);
    v_res_1252_ = l_Lean_Elab_isInductiveFixpoint(v_x_21__boxed_1251_);
    v_r_1253_ = leanh::lean_box((v_res_1252_) as usize);
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
    mut v_x_1257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_21__boxed_1258_: u8 = 0;
    let mut v_res_1259_: u8 = 0;
    let mut v_r_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_21__boxed_1258_ = (leanh::lean_unbox(v_x_1257_) as u8);
    v_res_1259_ = l_Lean_Elab_isCoinductiveFixpoint(v_x_21__boxed_1258_);
    v_r_1260_ = leanh::lean_box((v_res_1259_) as usize);
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
    mut v_x_1264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_21__boxed_1265_: u8 = 0;
    let mut v_res_1266_: u8 = 0;
    let mut v_r_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_21__boxed_1265_ = (leanh::lean_unbox(v_x_1264_) as u8);
    v_res_1266_ = l_Lean_Elab_isPartialFixpoint(v_x_21__boxed_1265_);
    v_r_1267_ = leanh::lean_box((v_res_1266_) as usize);
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
    mut v_p_1271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p_boxed_1272_: u8 = 0;
    let mut v_res_1273_: u8 = 0;
    let mut v_r_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_p_boxed_1272_ = (leanh::lean_unbox(v_p_1271_) as u8);
    v_res_1273_ = l_Lean_Elab_isLatticeTheoretic(v_p_boxed_1272_);
    v_r_1274_ = leanh::lean_box((v_res_1273_) as usize);
    return v_r_1274_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1276_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1276_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1277_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__0);
    v___x_1278_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1278_, 0, v___x_1277_);
    return v___x_1278_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1279_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1);
    v___x_1280_ = leanh::lean_unsigned_to_nat(0);
    v___x_1281_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_1281_, 0, v___x_1280_);
    leanh::lean_ctor_set(v___x_1281_, 1, v___x_1280_);
    leanh::lean_ctor_set(v___x_1281_, 2, v___x_1280_);
    leanh::lean_ctor_set(v___x_1281_, 3, v___x_1280_);
    leanh::lean_ctor_set(v___x_1281_, 4, v___x_1279_);
    leanh::lean_ctor_set(v___x_1281_, 5, v___x_1279_);
    leanh::lean_ctor_set(v___x_1281_, 6, v___x_1279_);
    leanh::lean_ctor_set(v___x_1281_, 7, v___x_1279_);
    leanh::lean_ctor_set(v___x_1281_, 8, v___x_1279_);
    leanh::lean_ctor_set(v___x_1281_, 9, v___x_1279_);
    return v___x_1281_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1282_ = leanh::lean_unsigned_to_nat(32);
    v___x_1283_ = lean_mk_empty_array_with_capacity(v___x_1282_);
    v___x_1284_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1284_, 0, v___x_1283_);
    return v___x_1284_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1285_: usize = 0;
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1285_ = 5usize;
    v___x_1286_ = leanh::lean_unsigned_to_nat(0);
    v___x_1287_ = leanh::lean_unsigned_to_nat(32);
    v___x_1288_ = lean_mk_empty_array_with_capacity(v___x_1287_);
    v___x_1289_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__3);
    v___x_1290_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1290_, 0, v___x_1289_);
    leanh::lean_ctor_set(v___x_1290_, 1, v___x_1288_);
    leanh::lean_ctor_set(v___x_1290_, 2, v___x_1286_);
    leanh::lean_ctor_set(v___x_1290_, 3, v___x_1286_);
    leanh::lean_ctor_set_usize(v___x_1290_, 4, v___x_1285_);
    return v___x_1290_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1291_ = leanh::lean_box(1);
    v___x_1292_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__4);
    v___x_1293_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__1);
    v___x_1294_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1294_, 0, v___x_1293_);
    leanh::lean_ctor_set(v___x_1294_, 1, v___x_1292_);
    leanh::lean_ctor_set(v___x_1294_, 2, v___x_1291_);
    return v___x_1294_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(
    mut v_msgData_1295_: *mut leanh::LeanObject,
    mut v___y_1296_: *mut leanh::LeanObject,
    mut v___y_1297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1299_ = lean_st_ref_get(v___y_1297_);
    v_env_1300_ = leanh::lean_ctor_get(v___x_1299_, 0);
    leanh::lean_inc_ref(v_env_1300_);
    leanh::lean_dec(v___x_1299_);
    v_options_1301_ = leanh::lean_ctor_get(v___y_1296_, 2);
    v___x_1302_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__2);
    v___x_1303_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___closed__5);
    leanh::lean_inc_ref(v_options_1301_);
    v___x_1304_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1304_, 0, v_env_1300_);
    leanh::lean_ctor_set(v___x_1304_, 1, v___x_1302_);
    leanh::lean_ctor_set(v___x_1304_, 2, v___x_1303_);
    leanh::lean_ctor_set(v___x_1304_, 3, v_options_1301_);
    v___x_1305_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1305_, 0, v___x_1304_);
    leanh::lean_ctor_set(v___x_1305_, 1, v_msgData_1295_);
    v___x_1306_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1306_, 0, v___x_1305_);
    return v___x_1306_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_1307_: *mut leanh::LeanObject,
    mut v___y_1308_: *mut leanh::LeanObject,
    mut v___y_1309_: *mut leanh::LeanObject,
    mut v___y_1310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1311_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(v_msgData_1307_, v___y_1308_, v___y_1309_);
    leanh::lean_dec(v___y_1309_);
    leanh::lean_dec_ref(v___y_1308_);
    return v_res_1311_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0(
    mut v___y_1320_: u8,
    mut v_suppressElabErrors_1321_: u8,
    mut v_x_1322_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_1322_) == 1 {
        let mut v_pre_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_1323_ = leanh::lean_ctor_get(v_x_1322_, 0);
        match leanh::lean_obj_tag(v_pre_1323_) {
            1 => {
                let mut v_pre_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_pre_1324_ = leanh::lean_ctor_get(v_pre_1323_, 0);
                match leanh::lean_obj_tag(v_pre_1324_) {
                    0 => {
                        let mut v_str_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1328_: u8 = 0;
                        v_str_1325_ = leanh::lean_ctor_get(v_x_1322_, 1);
                        v_str_1326_ = leanh::lean_ctor_get(v_pre_1323_, 1);
                        v___x_1327_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__0;
                        v___x_1328_ = lean_string_dec_eq(v_str_1326_, v___x_1327_);
                        if v___x_1328_ == 0 {
                            let mut v___x_1329_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1330_: u8 = 0;
                            v___x_1329_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__1;
                            v___x_1330_ = lean_string_dec_eq(v_str_1326_, v___x_1329_);
                            if v___x_1330_ == 0 {
                                return v___y_1320_;
                            } else {
                                let mut v___x_1331_: *mut leanh::LeanObject =
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
                            let mut v___x_1333_: *mut leanh::LeanObject =
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
                        let mut v_pre_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v_pre_1335_ = leanh::lean_ctor_get(v_pre_1324_, 0);
                        if leanh::lean_obj_tag(v_pre_1335_) == 0 {
                            let mut v_str_1336_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_1337_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_1338_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1339_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1340_: u8 = 0;
                            v_str_1336_ = leanh::lean_ctor_get(v_x_1322_, 1);
                            v_str_1337_ = leanh::lean_ctor_get(v_pre_1323_, 1);
                            v_str_1338_ = leanh::lean_ctor_get(v_pre_1324_, 1);
                            v___x_1339_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__4;
                            v___x_1340_ = lean_string_dec_eq(v_str_1338_, v___x_1339_);
                            if v___x_1340_ == 0 {
                                return v___y_1320_;
                            } else {
                                let mut v___x_1341_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1342_: u8 = 0;
                                v___x_1341_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___closed__5;
                                v___x_1342_ = lean_string_dec_eq(v_str_1337_, v___x_1341_);
                                if v___x_1342_ == 0 {
                                    return v___y_1320_;
                                } else {
                                    let mut v___x_1343_: *mut leanh::LeanObject =
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
                let mut v_str_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1347_: u8 = 0;
                v_str_1345_ = leanh::lean_ctor_get(v_x_1322_, 1);
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
    mut v___y_1348_: *mut leanh::LeanObject,
    mut v_suppressElabErrors_1349_: *mut leanh::LeanObject,
    mut v_x_1350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3124__boxed_1351_: u8 = 0;
    let mut v_suppressElabErrors_boxed_1352_: u8 = 0;
    let mut v_res_1353_: u8 = 0;
    let mut v_r_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_3124__boxed_1351_ = (leanh::lean_unbox(v___y_1348_) as u8);
    v_suppressElabErrors_boxed_1352_ = (leanh::lean_unbox(v_suppressElabErrors_1349_) as u8);
    v_res_1353_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0(v___y_3124__boxed_1351_, v_suppressElabErrors_boxed_1352_, v_x_1350_);
    leanh::lean_dec(v_x_1350_);
    v_r_1354_ = leanh::lean_box((v_res_1353_) as usize);
    return v_r_1354_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(
    mut v_opts_1355_: *mut leanh::LeanObject,
    mut v_opt_1356_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1357_ = leanh::lean_ctor_get(v_opt_1356_, 0);
    v_defValue_1358_ = leanh::lean_ctor_get(v_opt_1356_, 1);
    v_map_1359_ = leanh::lean_ctor_get(v_opts_1355_, 0);
    v___x_1360_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1359_,
            v_name_1357_,
        );
    if leanh::lean_obj_tag(v___x_1360_) == 0 {
        let mut v___x_1361_: u8 = 0;
        v___x_1361_ = (leanh::lean_unbox(v_defValue_1358_) as u8);
        return v___x_1361_;
    } else {
        let mut v_val_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1362_ = leanh::lean_ctor_get(v___x_1360_, 0);
        leanh::lean_inc(v_val_1362_);
        leanh::lean_dec_ref_known(v___x_1360_, 1);
        if leanh::lean_obj_tag(v_val_1362_) == 1 {
            let mut v_v_1363_: u8 = 0;
            v_v_1363_ = leanh::lean_ctor_get_uint8(v_val_1362_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_1362_, 0);
            return v_v_1363_;
        } else {
            let mut v___x_1364_: u8 = 0;
            leanh::lean_dec(v_val_1362_);
            v___x_1364_ = (leanh::lean_unbox(v_defValue_1358_) as u8);
            return v___x_1364_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2___boxed(
    mut v_opts_1365_: *mut leanh::LeanObject,
    mut v_opt_1366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1367_: u8 = 0;
    let mut v_r_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1367_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__2(v_opts_1365_, v_opt_1366_);
    leanh::lean_dec_ref(v_opt_1366_);
    leanh::lean_dec_ref(v_opts_1365_);
    v_r_1368_ = leanh::lean_box((v_res_1367_) as usize);
    return v_r_1368_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(
    mut v_ref_1370_: *mut leanh::LeanObject,
    mut v_msgData_1371_: *mut leanh::LeanObject,
    mut v_severity_1372_: u8,
    mut v_isSilent_1373_: u8,
    mut v___y_1374_: *mut leanh::LeanObject,
    mut v___y_1375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1378_: u8 = 0;
    let mut v___y_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1384_: u8 = 0;
    let mut v___y_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1401_: u8 = 0;
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1412_: u8 = 0;
    let mut v___y_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1415_: u8 = 0;
    let mut v___y_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1418_: u8 = 0;
    let mut v___y_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1420_: u8 = 0;
    let mut v___y_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1427_: u8 = 0;
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: u8 = 0;
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1437_: u8 = 0;
    let mut v___y_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1440_: u8 = 0;
    let mut v___y_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1444_: u8 = 0;
    let mut v___y_1445_: u8 = 0;
    let mut v___y_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1451_: u8 = 0;
    let mut v___y_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1455_: u8 = 0;
    let mut v___y_1456_: u8 = 0;
    let mut v_ref_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: u8 = 0;
    let mut v___y_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1467_: u8 = 0;
    let mut v___y_1468_: u8 = 0;
    let mut v___y_1469_: u8 = 0;
    let mut v___y_1471_: u8 = 0;
    let mut v_fileName_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1476_: u8 = 0;
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: u8 = 0;
    let mut v___x_1481_: u8 = 0;
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: u8 = 0;
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                    leanh::lean_inc_ref(v_msgData_1371_);
                    v___x_1487_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1371_);
                    v___y_1471_ = v___x_1487_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_1387_ = lean_st_ref_take(v___y_1386_);
                v_currNamespace_1388_ = leanh::lean_ctor_get(v___y_1385_, 6);
                v_openDecls_1389_ = leanh::lean_ctor_get(v___y_1385_, 7);
                v_env_1390_ = leanh::lean_ctor_get(v___x_1387_, 0);
                v_nextMacroScope_1391_ = leanh::lean_ctor_get(v___x_1387_, 1);
                v_ngen_1392_ = leanh::lean_ctor_get(v___x_1387_, 2);
                v_auxDeclNGen_1393_ = leanh::lean_ctor_get(v___x_1387_, 3);
                v_traceState_1394_ = leanh::lean_ctor_get(v___x_1387_, 4);
                v_cache_1395_ = leanh::lean_ctor_get(v___x_1387_, 5);
                v_messages_1396_ = leanh::lean_ctor_get(v___x_1387_, 6);
                v_infoState_1397_ = leanh::lean_ctor_get(v___x_1387_, 7);
                v_snapshotTasks_1398_ = leanh::lean_ctor_get(v___x_1387_, 8);
                v_isSharedCheck_1412_ = (!leanh::lean_is_exclusive(v___x_1387_)) as u8;
                if v_isSharedCheck_1412_ == 0 {
                    v___x_1400_ = v___x_1387_;
                    v_isShared_1401_ = v_isSharedCheck_1412_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1398_);
                    leanh::lean_inc(v_infoState_1397_);
                    leanh::lean_inc(v_messages_1396_);
                    leanh::lean_inc(v_cache_1395_);
                    leanh::lean_inc(v_traceState_1394_);
                    leanh::lean_inc(v_auxDeclNGen_1393_);
                    leanh::lean_inc(v_ngen_1392_);
                    leanh::lean_inc(v_nextMacroScope_1391_);
                    leanh::lean_inc(v_env_1390_);
                    leanh::lean_dec(v___x_1387_);
                    v___x_1400_ = leanh::lean_box(0);
                    v_isShared_1401_ = v_isSharedCheck_1412_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_openDecls_1389_);
                leanh::lean_inc(v_currNamespace_1388_);
                v___x_1402_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1402_, 0, v_currNamespace_1388_);
                leanh::lean_ctor_set(v___x_1402_, 1, v_openDecls_1389_);
                v___x_1403_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1403_, 0, v___x_1402_);
                leanh::lean_ctor_set(v___x_1403_, 1, v___y_1383_);
                leanh::lean_inc_ref(v___y_1382_);
                leanh::lean_inc_ref(v___y_1379_);
                v___x_1404_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_1404_, 0, v___y_1379_);
                leanh::lean_ctor_set(v___x_1404_, 1, v___y_1380_);
                leanh::lean_ctor_set(v___x_1404_, 2, v___y_1381_);
                leanh::lean_ctor_set(v___x_1404_, 3, v___y_1382_);
                leanh::lean_ctor_set(v___x_1404_, 4, v___x_1403_);
                leanh::lean_ctor_set_uint8(
                    v___x_1404_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___y_1378_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1404_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_1384_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1404_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_1373_,
                );
                v___x_1405_ = l_Lean_MessageLog_add(v___x_1404_, v_messages_1396_);
                if v_isShared_1401_ == 0 {
                    leanh::lean_ctor_set(v___x_1400_, 6, v___x_1405_);
                    v___x_1407_ = v___x_1400_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1411_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_env_1390_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_nextMacroScope_1391_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1411_, 2, v_ngen_1392_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1411_, 3, v_auxDeclNGen_1393_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1411_, 4, v_traceState_1394_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1411_, 5, v_cache_1395_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1411_, 6, v___x_1405_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1411_, 7, v_infoState_1397_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1411_, 8, v_snapshotTasks_1398_);
                    v___x_1407_ = v_reuseFailAlloc_1411_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1408_ = lean_st_ref_set(v___y_1386_, v___x_1407_);
                v___x_1409_ = leanh::lean_box(0);
                v___x_1410_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1410_, 0, v___x_1409_);
                return v___x_1410_;
            }
            4 => {
                v___x_1422_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_1371_,
                    );
                v___x_1423_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0_spec__1(v___x_1422_, v___y_1374_, v___y_1375_);
                v_a_1424_ = leanh::lean_ctor_get(v___x_1423_, 0);
                v_isSharedCheck_1437_ = (!leanh::lean_is_exclusive(v___x_1423_)) as u8;
                if v_isSharedCheck_1437_ == 0 {
                    v___x_1426_ = v___x_1423_;
                    v_isShared_1427_ = v_isSharedCheck_1437_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1424_);
                    leanh::lean_dec(v___x_1423_);
                    v___x_1426_ = leanh::lean_box(0);
                    v_isShared_1427_ = v_isSharedCheck_1437_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref_n(v___y_1416_, 2);
                v___x_1428_ = l_Lean_FileMap_toPosition(v___y_1416_, v___y_1419_);
                leanh::lean_dec(v___y_1419_);
                v___x_1429_ = l_Lean_FileMap_toPosition(v___y_1416_, v___y_1421_);
                leanh::lean_dec(v___y_1421_);
                v___x_1430_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1430_, 0, v___x_1429_);
                v___x_1431_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___closed__0;
                if v___y_1418_ == 0 {
                    leanh::lean_del_object(v___x_1426_);
                    leanh::lean_dec_ref(v___y_1414_);
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
                    leanh::lean_inc(v_a_1424_);
                    v___x_1432_ = l_Lean_MessageData_hasTag(v___y_1414_, v_a_1424_);
                    if v___x_1432_ == 0 {
                        leanh::lean_dec_ref_known(v___x_1430_, 1);
                        leanh::lean_dec_ref(v___x_1428_);
                        leanh::lean_dec(v_a_1424_);
                        v___x_1433_ = leanh::lean_box(0);
                        if v_isShared_1427_ == 0 {
                            leanh::lean_ctor_set(v___x_1426_, 0, v___x_1433_);
                            v___x_1435_ = v___x_1426_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_1436_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1433_);
                            v___x_1435_ = v_reuseFailAlloc_1436_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1426_);
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
                leanh::lean_dec(v___y_1443_);
                if leanh::lean_obj_tag(v___x_1447_) == 0 {
                    leanh::lean_inc(v___y_1446_);
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
                    v_val_1448_ = leanh::lean_ctor_get(v___x_1447_, 0);
                    leanh::lean_inc(v_val_1448_);
                    leanh::lean_dec_ref_known(v___x_1447_, 1);
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
                if leanh::lean_obj_tag(v___x_1458_) == 0 {
                    v___x_1459_ = leanh::lean_unsigned_to_nat(0);
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
                    v_val_1460_ = leanh::lean_ctor_get(v___x_1458_, 0);
                    leanh::lean_inc(v_val_1460_);
                    leanh::lean_dec_ref_known(v___x_1458_, 1);
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
                    v_fileName_1472_ = leanh::lean_ctor_get(v___y_1374_, 0);
                    v_fileMap_1473_ = leanh::lean_ctor_get(v___y_1374_, 1);
                    v_options_1474_ = leanh::lean_ctor_get(v___y_1374_, 2);
                    v_ref_1475_ = leanh::lean_ctor_get(v___y_1374_, 5);
                    v_suppressElabErrors_1476_ = leanh::lean_ctor_get_uint8(
                        v___y_1374_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_1477_ = leanh::lean_box((v___y_1471_) as usize);
                    v___x_1478_ = leanh::lean_box((v_suppressElabErrors_1476_) as usize);
                    v___f_1479_ = leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    leanh::lean_closure_set(v___f_1479_, 0, v___x_1477_);
                    leanh::lean_closure_set(v___f_1479_, 1, v___x_1478_);
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
                    leanh::lean_dec_ref(v_msgData_1371_);
                    v___x_1484_ = leanh::lean_box(0);
                    v___x_1485_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1485_, 0, v___x_1484_);
                    return v___x_1485_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0___boxed(
    mut v_ref_1488_: *mut leanh::LeanObject,
    mut v_msgData_1489_: *mut leanh::LeanObject,
    mut v_severity_1490_: *mut leanh::LeanObject,
    mut v_isSilent_1491_: *mut leanh::LeanObject,
    mut v___y_1492_: *mut leanh::LeanObject,
    mut v___y_1493_: *mut leanh::LeanObject,
    mut v___y_1494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_1495_: u8 = 0;
    let mut v_isSilent_boxed_1496_: u8 = 0;
    let mut v_res_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_1495_ = (leanh::lean_unbox(v_severity_1490_) as u8);
    v_isSilent_boxed_1496_ = (leanh::lean_unbox(v_isSilent_1491_) as u8);
    v_res_1497_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(v_ref_1488_, v_msgData_1489_, v_severity_boxed_1495_, v_isSilent_boxed_1496_, v___y_1492_, v___y_1493_);
    leanh::lean_dec(v___y_1493_);
    leanh::lean_dec_ref(v___y_1492_);
    leanh::lean_dec(v_ref_1488_);
    return v_res_1497_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(
    mut v_ref_1498_: *mut leanh::LeanObject,
    mut v_msgData_1499_: *mut leanh::LeanObject,
    mut v___y_1500_: *mut leanh::LeanObject,
    mut v___y_1501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1503_: u8 = 0;
    let mut v___x_1504_: u8 = 0;
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1503_ = 1;
    v___x_1504_ = 0;
    v___x_1505_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0_spec__0(v_ref_1498_, v_msgData_1499_, v___x_1503_, v___x_1504_, v___y_1500_, v___y_1501_);
    return v___x_1505_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0___boxed(
    mut v_ref_1506_: *mut leanh::LeanObject,
    mut v_msgData_1507_: *mut leanh::LeanObject,
    mut v___y_1508_: *mut leanh::LeanObject,
    mut v___y_1509_: *mut leanh::LeanObject,
    mut v___y_1510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1511_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(
        v_ref_1506_,
        v_msgData_1507_,
        v___y_1508_,
        v___y_1509_,
    );
    leanh::lean_dec(v___y_1509_);
    leanh::lean_dec_ref(v___y_1508_);
    leanh::lean_dec(v_ref_1506_);
    return v_res_1511_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationHints_ensureNone___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1513_ = l_Lean_Elab_TerminationHints_ensureNone___closed__0;
    v___x_1514_ = l_Lean_stringToMessageData(v___x_1513_);
    return v___x_1514_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationHints_ensureNone___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1516_ = l_Lean_Elab_TerminationHints_ensureNone___closed__2;
    v___x_1517_ = l_Lean_stringToMessageData(v___x_1516_);
    return v___x_1517_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationHints_ensureNone___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1519_ = l_Lean_Elab_TerminationHints_ensureNone___closed__4;
    v___x_1520_ = l_Lean_stringToMessageData(v___x_1519_);
    return v___x_1520_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationHints_ensureNone___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1522_ = l_Lean_Elab_TerminationHints_ensureNone___closed__6;
    v___x_1523_ = l_Lean_stringToMessageData(v___x_1522_);
    return v___x_1523_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationHints_ensureNone___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1525_ = l_Lean_Elab_TerminationHints_ensureNone___closed__8;
    v___x_1526_ = l_Lean_stringToMessageData(v___x_1525_);
    return v___x_1526_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationHints_ensureNone___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1528_ = l_Lean_Elab_TerminationHints_ensureNone___closed__10;
    v___x_1529_ = l_Lean_stringToMessageData(v___x_1528_);
    return v___x_1529_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationHints_ensureNone___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1531_ = l_Lean_Elab_TerminationHints_ensureNone___closed__12;
    v___x_1532_ = l_Lean_stringToMessageData(v___x_1531_);
    return v___x_1532_;
}
pub unsafe fn l_Lean_Elab_TerminationHints_ensureNone(
    mut v_hints_1533_: *mut leanh::LeanObject,
    mut v_reason_1534_: *mut leanh::LeanObject,
    mut v_a_1535_: *mut leanh::LeanObject,
    mut v_a_1536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_terminationBy_x3f_x3f_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_terminationBy_x3f_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_partialFixpoint_x3f_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decreasingBy_x3f_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fixpointType_1553_: u8 = 0;
    let mut v_ref_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1573_: u8 = 0;
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1580_: u8 = 0;
    let mut v_unused_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1538_ = leanh::lean_ctor_get(v_hints_1533_, 0);
                leanh::lean_inc(v_ref_1538_);
                v_terminationBy_x3f_x3f_1539_ = leanh::lean_ctor_get(v_hints_1533_, 1);
                leanh::lean_inc(v_terminationBy_x3f_x3f_1539_);
                v_terminationBy_x3f_1540_ = leanh::lean_ctor_get(v_hints_1533_, 2);
                leanh::lean_inc(v_terminationBy_x3f_1540_);
                v_partialFixpoint_x3f_1541_ = leanh::lean_ctor_get(v_hints_1533_, 3);
                leanh::lean_inc(v_partialFixpoint_x3f_1541_);
                v_decreasingBy_x3f_1542_ = leanh::lean_ctor_get(v_hints_1533_, 4);
                leanh::lean_inc(v_decreasingBy_x3f_1542_);
                leanh::lean_dec_ref(v_hints_1533_);
                if leanh::lean_obj_tag(v_terminationBy_x3f_x3f_1539_) == 0 {
                    if leanh::lean_obj_tag(v_terminationBy_x3f_1540_) == 0 {
                        if leanh::lean_obj_tag(v_decreasingBy_x3f_1542_) == 0 {
                            leanh::lean_dec(v_ref_1538_);
                            if leanh::lean_obj_tag(v_partialFixpoint_x3f_1541_) == 0 {
                                leanh::lean_dec_ref(v_reason_1534_);
                                v___x_1550_ = leanh::lean_box(0);
                                v___x_1551_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1551_, 0, v___x_1550_);
                                return v___x_1551_;
                            } else {
                                v_val_1552_ =
                                    leanh::lean_ctor_get(v_partialFixpoint_x3f_1541_, 0);
                                leanh::lean_inc(v_val_1552_);
                                leanh::lean_dec_ref_known(v_partialFixpoint_x3f_1541_, 1);
                                v_fixpointType_1553_ = leanh::lean_ctor_get_uint8(
                                    v_val_1552_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                                        as u32,
                                );
                                match v_fixpointType_1553_ {
                                    0 => {
                                        v_ref_1554_ = leanh::lean_ctor_get(v_val_1552_, 0);
                                        leanh::lean_inc(v_ref_1554_);
                                        leanh::lean_dec(v_val_1552_);
                                        v___x_1555_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_TerminationHints_ensureNone___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_TerminationHints_ensureNone___closed__3_once), _init_l_Lean_Elab_TerminationHints_ensureNone___closed__3);
                                        v___x_1556_ = l_Lean_stringToMessageData(v_reason_1534_);
                                        v___x_1557_ =
                                            leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_1557_, 0, v___x_1555_);
                                        leanh::lean_ctor_set(v___x_1557_, 1, v___x_1556_);
                                        v___x_1558_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_1554_, v___x_1557_, v_a_1535_, v_a_1536_);
                                        leanh::lean_dec(v_ref_1554_);
                                        return v___x_1558_;
                                    }
                                    1 => {
                                        v_ref_1559_ = leanh::lean_ctor_get(v_val_1552_, 0);
                                        leanh::lean_inc(v_ref_1559_);
                                        leanh::lean_dec(v_val_1552_);
                                        v___x_1560_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_TerminationHints_ensureNone___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_TerminationHints_ensureNone___closed__5_once), _init_l_Lean_Elab_TerminationHints_ensureNone___closed__5);
                                        v___x_1561_ = l_Lean_stringToMessageData(v_reason_1534_);
                                        v___x_1562_ =
                                            leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_1562_, 0, v___x_1560_);
                                        leanh::lean_ctor_set(v___x_1562_, 1, v___x_1561_);
                                        v___x_1563_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_1559_, v___x_1562_, v_a_1535_, v_a_1536_);
                                        leanh::lean_dec(v_ref_1559_);
                                        return v___x_1563_;
                                    }
                                    _ => {
                                        v_ref_1564_ = leanh::lean_ctor_get(v_val_1552_, 0);
                                        leanh::lean_inc(v_ref_1564_);
                                        leanh::lean_dec(v_val_1552_);
                                        v___x_1565_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_TerminationHints_ensureNone___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_TerminationHints_ensureNone___closed__7_once), _init_l_Lean_Elab_TerminationHints_ensureNone___closed__7);
                                        v___x_1566_ = l_Lean_stringToMessageData(v_reason_1534_);
                                        v___x_1567_ =
                                            leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_1567_, 0, v___x_1565_);
                                        leanh::lean_ctor_set(v___x_1567_, 1, v___x_1566_);
                                        v___x_1568_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_1564_, v___x_1567_, v_a_1535_, v_a_1536_);
                                        leanh::lean_dec(v_ref_1564_);
                                        return v___x_1568_;
                                    }
                                }
                            }
                        } else {
                            if leanh::lean_obj_tag(v_partialFixpoint_x3f_1541_) == 0 {
                                leanh::lean_dec(v_ref_1538_);
                                v_val_1569_ =
                                    leanh::lean_ctor_get(v_decreasingBy_x3f_1542_, 0);
                                leanh::lean_inc(v_val_1569_);
                                leanh::lean_dec_ref_known(v_decreasingBy_x3f_1542_, 1);
                                v_ref_1570_ = leanh::lean_ctor_get(v_val_1569_, 0);
                                v_isSharedCheck_1580_ =
                                    (!leanh::lean_is_exclusive(v_val_1569_)) as u8;
                                if v_isSharedCheck_1580_ == 0 {
                                    v_unused_1581_ = leanh::lean_ctor_get(v_val_1569_, 1);
                                    leanh::lean_dec(v_unused_1581_);
                                    v___x_1572_ = v_val_1569_;
                                    v_isShared_1573_ = v_isSharedCheck_1580_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_ref_1570_);
                                    leanh::lean_dec(v_val_1569_);
                                    v___x_1572_ = leanh::lean_box(0);
                                    v_isShared_1573_ = v_isSharedCheck_1580_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref_known(v_decreasingBy_x3f_1542_, 1);
                                leanh::lean_dec(v_partialFixpoint_x3f_1541_);
                                v___y_1544_ = v_a_1535_;
                                v___y_1545_ = v_a_1536_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        if leanh::lean_obj_tag(v_decreasingBy_x3f_1542_) == 0 {
                            if leanh::lean_obj_tag(v_partialFixpoint_x3f_1541_) == 0 {
                                leanh::lean_dec(v_ref_1538_);
                                v_val_1582_ =
                                    leanh::lean_ctor_get(v_terminationBy_x3f_1540_, 0);
                                leanh::lean_inc(v_val_1582_);
                                leanh::lean_dec_ref_known(v_terminationBy_x3f_1540_, 1);
                                v_ref_1583_ = leanh::lean_ctor_get(v_val_1582_, 0);
                                leanh::lean_inc(v_ref_1583_);
                                leanh::lean_dec(v_val_1582_);
                                v___x_1584_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_TerminationHints_ensureNone___closed__11
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_TerminationHints_ensureNone___closed__11_once
                                    ),
                                    _init_l_Lean_Elab_TerminationHints_ensureNone___closed__11,
                                );
                                v___x_1585_ = l_Lean_stringToMessageData(v_reason_1534_);
                                v___x_1586_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1586_, 0, v___x_1584_);
                                leanh::lean_ctor_set(v___x_1586_, 1, v___x_1585_);
                                v___x_1587_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_ref_1583_, v___x_1586_, v_a_1535_, v_a_1536_);
                                leanh::lean_dec(v_ref_1583_);
                                return v___x_1587_;
                            } else {
                                leanh::lean_dec_ref_known(v_terminationBy_x3f_1540_, 1);
                                leanh::lean_dec(v_partialFixpoint_x3f_1541_);
                                v___y_1544_ = v_a_1535_;
                                v___y_1545_ = v_a_1536_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_terminationBy_x3f_1540_, 1);
                            leanh::lean_dec(v_decreasingBy_x3f_1542_);
                            leanh::lean_dec(v_partialFixpoint_x3f_1541_);
                            v___y_1544_ = v_a_1535_;
                            v___y_1545_ = v_a_1536_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    if leanh::lean_obj_tag(v_terminationBy_x3f_1540_) == 0 {
                        if leanh::lean_obj_tag(v_decreasingBy_x3f_1542_) == 0 {
                            if leanh::lean_obj_tag(v_partialFixpoint_x3f_1541_) == 0 {
                                leanh::lean_dec(v_ref_1538_);
                                v_val_1588_ =
                                    leanh::lean_ctor_get(v_terminationBy_x3f_x3f_1539_, 0);
                                leanh::lean_inc(v_val_1588_);
                                leanh::lean_dec_ref_known(v_terminationBy_x3f_x3f_1539_, 1);
                                v___x_1589_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_TerminationHints_ensureNone___closed__13
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_TerminationHints_ensureNone___closed__13_once
                                    ),
                                    _init_l_Lean_Elab_TerminationHints_ensureNone___closed__13,
                                );
                                v___x_1590_ = l_Lean_stringToMessageData(v_reason_1534_);
                                v___x_1591_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1591_, 0, v___x_1589_);
                                leanh::lean_ctor_set(v___x_1591_, 1, v___x_1590_);
                                v___x_1592_ = l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(v_val_1588_, v___x_1591_, v_a_1535_, v_a_1536_);
                                leanh::lean_dec(v_val_1588_);
                                return v___x_1592_;
                            } else {
                                leanh::lean_dec_ref_known(v_terminationBy_x3f_x3f_1539_, 1);
                                leanh::lean_dec(v_partialFixpoint_x3f_1541_);
                                v___y_1544_ = v_a_1535_;
                                v___y_1545_ = v_a_1536_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_terminationBy_x3f_x3f_1539_, 1);
                            leanh::lean_dec(v_decreasingBy_x3f_1542_);
                            leanh::lean_dec(v_partialFixpoint_x3f_1541_);
                            v___y_1544_ = v_a_1535_;
                            v___y_1545_ = v_a_1536_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_terminationBy_x3f_x3f_1539_, 1);
                        leanh::lean_dec(v_decreasingBy_x3f_1542_);
                        leanh::lean_dec(v_partialFixpoint_x3f_1541_);
                        leanh::lean_dec(v_terminationBy_x3f_1540_);
                        v___y_1544_ = v_a_1535_;
                        v___y_1545_ = v_a_1536_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1546_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_TerminationHints_ensureNone___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_TerminationHints_ensureNone___closed__1_once
                    ),
                    _init_l_Lean_Elab_TerminationHints_ensureNone___closed__1,
                );
                v___x_1547_ = l_Lean_stringToMessageData(v_reason_1534_);
                v___x_1548_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1548_, 0, v___x_1546_);
                leanh::lean_ctor_set(v___x_1548_, 1, v___x_1547_);
                v___x_1549_ =
                    l_Lean_logWarningAt___at___00Lean_Elab_TerminationHints_ensureNone_spec__0(
                        v_ref_1538_,
                        v___x_1548_,
                        v___y_1544_,
                        v___y_1545_,
                    );
                leanh::lean_dec(v_ref_1538_);
                return v___x_1549_;
            }
            2 => {
                v___x_1574_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_TerminationHints_ensureNone___closed__9),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_TerminationHints_ensureNone___closed__9_once
                    ),
                    _init_l_Lean_Elab_TerminationHints_ensureNone___closed__9,
                );
                v___x_1575_ = l_Lean_stringToMessageData(v_reason_1534_);
                if v_isShared_1573_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1572_, 7);
                    leanh::lean_ctor_set(v___x_1572_, 1, v___x_1575_);
                    leanh::lean_ctor_set(v___x_1572_, 0, v___x_1574_);
                    v___x_1577_ = v___x_1572_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1579_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1574_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1579_, 1, v___x_1575_);
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
                leanh::lean_dec(v_ref_1570_);
                return v___x_1578_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_TerminationHints_ensureNone___boxed(
    mut v_hints_1593_: *mut leanh::LeanObject,
    mut v_reason_1594_: *mut leanh::LeanObject,
    mut v_a_1595_: *mut leanh::LeanObject,
    mut v_a_1596_: *mut leanh::LeanObject,
    mut v_a_1597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1598_ = l_Lean_Elab_TerminationHints_ensureNone(
        v_hints_1593_,
        v_reason_1594_,
        v_a_1595_,
        v_a_1596_,
    );
    leanh::lean_dec(v_a_1596_);
    leanh::lean_dec_ref(v_a_1595_);
    return v_res_1598_;
}
pub unsafe fn l_Lean_Elab_TerminationHints_isNotNone(
    mut v_hints_1599_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_terminationBy_x3f_x3f_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_terminationBy_x3f_x3f_1600_ = leanh::lean_ctor_get(v_hints_1599_, 1);
    if leanh::lean_obj_tag(v_terminationBy_x3f_x3f_1600_) == 0 {
        let mut v_terminationBy_x3f_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_terminationBy_x3f_1601_ = leanh::lean_ctor_get(v_hints_1599_, 2);
        if leanh::lean_obj_tag(v_terminationBy_x3f_1601_) == 0 {
            let mut v_decreasingBy_x3f_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_decreasingBy_x3f_1602_ = leanh::lean_ctor_get(v_hints_1599_, 4);
            if leanh::lean_obj_tag(v_decreasingBy_x3f_1602_) == 0 {
                let mut v_partialFixpoint_x3f_1603_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                v_partialFixpoint_x3f_1603_ = leanh::lean_ctor_get(v_hints_1599_, 3);
                if leanh::lean_obj_tag(v_partialFixpoint_x3f_1603_) == 0 {
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
    mut v_hints_1609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1610_: u8 = 0;
    let mut v_r_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1610_ = l_Lean_Elab_TerminationHints_isNotNone(v_hints_1609_);
    leanh::lean_dec_ref(v_hints_1609_);
    v_r_1611_ = leanh::lean_box((v_res_1610_) as usize);
    return v_r_1611_;
}
pub unsafe fn l_Lean_Elab_TerminationHints_rememberExtraParams(
    mut v_headerParams_1612_: *mut leanh::LeanObject,
    mut v_hints_1613_: *mut leanh::LeanObject,
    mut v_value_1614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_terminationBy_x3f_x3f_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_terminationBy_x3f_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_partialFixpoint_x3f_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decreasingBy_x3f_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1622_: u8 = 0;
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1628_: u8 = 0;
    let mut v_unused_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1615_ = leanh::lean_ctor_get(v_hints_1613_, 0);
                v_terminationBy_x3f_x3f_1616_ = leanh::lean_ctor_get(v_hints_1613_, 1);
                v_terminationBy_x3f_1617_ = leanh::lean_ctor_get(v_hints_1613_, 2);
                v_partialFixpoint_x3f_1618_ = leanh::lean_ctor_get(v_hints_1613_, 3);
                v_decreasingBy_x3f_1619_ = leanh::lean_ctor_get(v_hints_1613_, 4);
                v_isSharedCheck_1628_ = (!leanh::lean_is_exclusive(v_hints_1613_)) as u8;
                if v_isSharedCheck_1628_ == 0 {
                    v_unused_1629_ = leanh::lean_ctor_get(v_hints_1613_, 5);
                    leanh::lean_dec(v_unused_1629_);
                    v___x_1621_ = v_hints_1613_;
                    v_isShared_1622_ = v_isSharedCheck_1628_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_decreasingBy_x3f_1619_);
                    leanh::lean_inc(v_partialFixpoint_x3f_1618_);
                    leanh::lean_inc(v_terminationBy_x3f_1617_);
                    leanh::lean_inc(v_terminationBy_x3f_x3f_1616_);
                    leanh::lean_inc(v_ref_1615_);
                    leanh::lean_dec(v_hints_1613_);
                    v___x_1621_ = leanh::lean_box(0);
                    v_isShared_1622_ = v_isSharedCheck_1628_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1623_ = l_Lean_Expr_getNumHeadLambdas(v_value_1614_);
                v___x_1624_ = lean_nat_sub(v___x_1623_, v_headerParams_1612_);
                leanh::lean_dec(v___x_1623_);
                if v_isShared_1622_ == 0 {
                    leanh::lean_ctor_set(v___x_1621_, 5, v___x_1624_);
                    v___x_1626_ = v___x_1621_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1627_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_ref_1615_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1627_,
                        1,
                        v_terminationBy_x3f_x3f_1616_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1627_,
                        2,
                        v_terminationBy_x3f_1617_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1627_,
                        3,
                        v_partialFixpoint_x3f_1618_,
                    );
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1627_,
                        4,
                        v_decreasingBy_x3f_1619_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1627_, 5, v___x_1624_);
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
    mut v_headerParams_1630_: *mut leanh::LeanObject,
    mut v_hints_1631_: *mut leanh::LeanObject,
    mut v_value_1632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1633_ = l_Lean_Elab_TerminationHints_rememberExtraParams(
        v_headerParams_1630_,
        v_hints_1631_,
        v_value_1632_,
    );
    leanh::lean_dec_ref(v_value_1632_);
    leanh::lean_dec(v_headerParams_1630_);
    return v_res_1633_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1635_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__0;
    v___x_1636_ = l_Lean_stringToMessageData(v___x_1635_);
    return v___x_1636_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1640_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__3;
    v___x_1641_ = l_Lean_MessageData_ofFormat(v___x_1640_);
    return v___x_1641_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(
    mut v_a_1642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: u8 = 0;
    v___x_1643_ = leanh::lean_unsigned_to_nat(1);
    v___x_1644_ = lean_nat_dec_eq(v_a_1642_, v___x_1643_);
    if v___x_1644_ == 0 {
        let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1645_ = l_Nat_reprFast(v_a_1642_);
        v___x_1646_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1646_, 0, v___x_1645_);
        v___x_1647_ = l_Lean_MessageData_ofFormat(v___x_1646_);
        v___x_1648_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1_once), _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__1);
        v___x_1649_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1649_, 0, v___x_1647_);
        leanh::lean_ctor_set(v___x_1649_, 1, v___x_1648_);
        return v___x_1649_;
    } else {
        let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_1642_);
        v___x_1650_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4_once), _init_l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters___closed__4);
        return v___x_1650_;
    }
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(
    mut v_msgData_1651_: *mut leanh::LeanObject,
    mut v___y_1652_: *mut leanh::LeanObject,
    mut v___y_1653_: *mut leanh::LeanObject,
    mut v___y_1654_: *mut leanh::LeanObject,
    mut v___y_1655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1657_ = lean_st_ref_get(v___y_1655_);
    v_env_1658_ = leanh::lean_ctor_get(v___x_1657_, 0);
    leanh::lean_inc_ref(v_env_1658_);
    leanh::lean_dec(v___x_1657_);
    v___x_1659_ = lean_st_ref_get(v___y_1653_);
    v_mctx_1660_ = leanh::lean_ctor_get(v___x_1659_, 0);
    leanh::lean_inc_ref(v_mctx_1660_);
    leanh::lean_dec(v___x_1659_);
    v_lctx_1661_ = leanh::lean_ctor_get(v___y_1652_, 2);
    v_options_1662_ = leanh::lean_ctor_get(v___y_1654_, 2);
    leanh::lean_inc_ref(v_options_1662_);
    leanh::lean_inc_ref(v_lctx_1661_);
    v___x_1663_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1663_, 0, v_env_1658_);
    leanh::lean_ctor_set(v___x_1663_, 1, v_mctx_1660_);
    leanh::lean_ctor_set(v___x_1663_, 2, v_lctx_1661_);
    leanh::lean_ctor_set(v___x_1663_, 3, v_options_1662_);
    v___x_1664_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1664_, 0, v___x_1663_);
    leanh::lean_ctor_set(v___x_1664_, 1, v_msgData_1651_);
    v___x_1665_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1665_, 0, v___x_1664_);
    return v___x_1665_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_1666_: *mut leanh::LeanObject,
    mut v___y_1667_: *mut leanh::LeanObject,
    mut v___y_1668_: *mut leanh::LeanObject,
    mut v___y_1669_: *mut leanh::LeanObject,
    mut v___y_1670_: *mut leanh::LeanObject,
    mut v___y_1671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1672_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(v_msgData_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
    leanh::lean_dec(v___y_1670_);
    leanh::lean_dec_ref(v___y_1669_);
    leanh::lean_dec(v___y_1668_);
    leanh::lean_dec_ref(v___y_1667_);
    return v_res_1672_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(
    mut v_msg_1673_: *mut leanh::LeanObject,
    mut v___y_1674_: *mut leanh::LeanObject,
    mut v___y_1675_: *mut leanh::LeanObject,
    mut v___y_1676_: *mut leanh::LeanObject,
    mut v___y_1677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1684_: u8 = 0;
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1689_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1679_ = leanh::lean_ctor_get(v___y_1676_, 5);
                v___x_1680_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0_spec__1(v_msg_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
                v_a_1681_ = leanh::lean_ctor_get(v___x_1680_, 0);
                v_isSharedCheck_1689_ = (!leanh::lean_is_exclusive(v___x_1680_)) as u8;
                if v_isSharedCheck_1689_ == 0 {
                    v___x_1683_ = v___x_1680_;
                    v_isShared_1684_ = v_isSharedCheck_1689_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1681_);
                    leanh::lean_dec(v___x_1680_);
                    v___x_1683_ = leanh::lean_box(0);
                    v_isShared_1684_ = v_isSharedCheck_1689_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1679_);
                v___x_1685_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1685_, 0, v_ref_1679_);
                leanh::lean_ctor_set(v___x_1685_, 1, v_a_1681_);
                if v_isShared_1684_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1683_, 1);
                    leanh::lean_ctor_set(v___x_1683_, 0, v___x_1685_);
                    v___x_1687_ = v___x_1683_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1688_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1685_);
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
    mut v_msg_1690_: *mut leanh::LeanObject,
    mut v___y_1691_: *mut leanh::LeanObject,
    mut v___y_1692_: *mut leanh::LeanObject,
    mut v___y_1693_: *mut leanh::LeanObject,
    mut v___y_1694_: *mut leanh::LeanObject,
    mut v___y_1695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1696_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
    leanh::lean_dec(v___y_1694_);
    leanh::lean_dec_ref(v___y_1693_);
    leanh::lean_dec(v___y_1692_);
    leanh::lean_dec_ref(v___y_1691_);
    return v_res_1696_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(
    mut v_ref_1697_: *mut leanh::LeanObject,
    mut v_msg_1698_: *mut leanh::LeanObject,
    mut v___y_1699_: *mut leanh::LeanObject,
    mut v___y_1700_: *mut leanh::LeanObject,
    mut v___y_1701_: *mut leanh::LeanObject,
    mut v___y_1702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1716_: u8 = 0;
    let mut v_cancelTk_x3f_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1718_: u8 = 0;
    let mut v_inheritedTraceOptions_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1704_ = leanh::lean_ctor_get(v___y_1701_, 0);
    v_fileMap_1705_ = leanh::lean_ctor_get(v___y_1701_, 1);
    v_options_1706_ = leanh::lean_ctor_get(v___y_1701_, 2);
    v_currRecDepth_1707_ = leanh::lean_ctor_get(v___y_1701_, 3);
    v_maxRecDepth_1708_ = leanh::lean_ctor_get(v___y_1701_, 4);
    v_ref_1709_ = leanh::lean_ctor_get(v___y_1701_, 5);
    v_currNamespace_1710_ = leanh::lean_ctor_get(v___y_1701_, 6);
    v_openDecls_1711_ = leanh::lean_ctor_get(v___y_1701_, 7);
    v_initHeartbeats_1712_ = leanh::lean_ctor_get(v___y_1701_, 8);
    v_maxHeartbeats_1713_ = leanh::lean_ctor_get(v___y_1701_, 9);
    v_quotContext_1714_ = leanh::lean_ctor_get(v___y_1701_, 10);
    v_currMacroScope_1715_ = leanh::lean_ctor_get(v___y_1701_, 11);
    v_diag_1716_ = leanh::lean_ctor_get_uint8(
        v___y_1701_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1717_ = leanh::lean_ctor_get(v___y_1701_, 12);
    v_suppressElabErrors_1718_ = leanh::lean_ctor_get_uint8(
        v___y_1701_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1719_ = leanh::lean_ctor_get(v___y_1701_, 13);
    v_ref_1720_ = l_Lean_replaceRef(v_ref_1697_, v_ref_1709_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_1719_);
    leanh::lean_inc(v_cancelTk_x3f_1717_);
    leanh::lean_inc(v_currMacroScope_1715_);
    leanh::lean_inc(v_quotContext_1714_);
    leanh::lean_inc(v_maxHeartbeats_1713_);
    leanh::lean_inc(v_initHeartbeats_1712_);
    leanh::lean_inc(v_openDecls_1711_);
    leanh::lean_inc(v_currNamespace_1710_);
    leanh::lean_inc(v_maxRecDepth_1708_);
    leanh::lean_inc(v_currRecDepth_1707_);
    leanh::lean_inc_ref(v_options_1706_);
    leanh::lean_inc_ref(v_fileMap_1705_);
    leanh::lean_inc_ref(v_fileName_1704_);
    v___x_1721_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_1721_, 0, v_fileName_1704_);
    leanh::lean_ctor_set(v___x_1721_, 1, v_fileMap_1705_);
    leanh::lean_ctor_set(v___x_1721_, 2, v_options_1706_);
    leanh::lean_ctor_set(v___x_1721_, 3, v_currRecDepth_1707_);
    leanh::lean_ctor_set(v___x_1721_, 4, v_maxRecDepth_1708_);
    leanh::lean_ctor_set(v___x_1721_, 5, v_ref_1720_);
    leanh::lean_ctor_set(v___x_1721_, 6, v_currNamespace_1710_);
    leanh::lean_ctor_set(v___x_1721_, 7, v_openDecls_1711_);
    leanh::lean_ctor_set(v___x_1721_, 8, v_initHeartbeats_1712_);
    leanh::lean_ctor_set(v___x_1721_, 9, v_maxHeartbeats_1713_);
    leanh::lean_ctor_set(v___x_1721_, 10, v_quotContext_1714_);
    leanh::lean_ctor_set(v___x_1721_, 11, v_currMacroScope_1715_);
    leanh::lean_ctor_set(v___x_1721_, 12, v_cancelTk_x3f_1717_);
    leanh::lean_ctor_set(v___x_1721_, 13, v_inheritedTraceOptions_1719_);
    leanh::lean_ctor_set_uint8(
        v___x_1721_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_1716_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1721_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1718_,
    );
    v___x_1722_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_1698_, v___y_1699_, v___y_1700_, v___x_1721_, v___y_1702_);
    leanh::lean_dec_ref_known(v___x_1721_, 14);
    return v___x_1722_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg___boxed(
    mut v_ref_1723_: *mut leanh::LeanObject,
    mut v_msg_1724_: *mut leanh::LeanObject,
    mut v___y_1725_: *mut leanh::LeanObject,
    mut v___y_1726_: *mut leanh::LeanObject,
    mut v___y_1727_: *mut leanh::LeanObject,
    mut v___y_1728_: *mut leanh::LeanObject,
    mut v___y_1729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1730_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(
        v_ref_1723_,
        v_msg_1724_,
        v___y_1725_,
        v___y_1726_,
        v___y_1727_,
        v___y_1728_,
    );
    leanh::lean_dec(v___y_1728_);
    leanh::lean_dec_ref(v___y_1727_);
    leanh::lean_dec(v___y_1726_);
    leanh::lean_dec_ref(v___y_1725_);
    leanh::lean_dec(v_ref_1723_);
    return v_res_1730_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationBy_checkVars___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1732_ = l_Lean_Elab_TerminationBy_checkVars___closed__0;
    v___x_1733_ = l_Lean_stringToMessageData(v___x_1732_);
    return v___x_1733_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationBy_checkVars___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1735_ = l_Lean_Elab_TerminationBy_checkVars___closed__2;
    v___x_1736_ = l_Lean_stringToMessageData(v___x_1735_);
    return v___x_1736_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationBy_checkVars___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1738_ = l_Lean_Elab_TerminationBy_checkVars___closed__4;
    v___x_1739_ = l_Lean_stringToMessageData(v___x_1738_);
    return v___x_1739_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationBy_checkVars___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1744_ = l_Lean_Elab_TerminationBy_checkVars___closed__8;
    v___x_1745_ = l_Lean_stringToMessageData(v___x_1744_);
    return v___x_1745_;
}
pub unsafe fn _init_l_Lean_Elab_TerminationBy_checkVars___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1749_ = l_Lean_Elab_TerminationBy_checkVars___closed__11;
    v___x_1750_ = l_Lean_MessageData_ofFormat(v___x_1749_);
    return v___x_1750_;
}
pub unsafe fn l_Lean_Elab_TerminationBy_checkVars(
    mut v_funName_1751_: *mut leanh::LeanObject,
    mut v_extraParams_1752_: *mut leanh::LeanObject,
    mut v_tb_1753_: *mut leanh::LeanObject,
    mut v_a_1754_: *mut leanh::LeanObject,
    mut v_a_1755_: *mut leanh::LeanObject,
    mut v_a_1756_: *mut leanh::LeanObject,
    mut v_a_1757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_synthetic_1759_: u8 = 0;
    v_synthetic_1759_ = leanh::lean_ctor_get_uint8(
        v_tb_1753_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
    );
    if v_synthetic_1759_ == 0 {
        let mut v_ref_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_vars_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1763_: u8 = 0;
        v_ref_1760_ = leanh::lean_ctor_get(v_tb_1753_, 0);
        v_vars_1761_ = leanh::lean_ctor_get(v_tb_1753_, 1);
        v___x_1762_ = lean_array_get_size(v_vars_1761_);
        v___x_1763_ = lean_nat_dec_lt(v_extraParams_1752_, v___x_1762_);
        if v___x_1763_ == 0 {
            let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_extraParams_1752_);
            leanh::lean_dec(v_funName_1751_);
            v___x_1764_ = leanh::lean_box(0);
            v___x_1765_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1765_, 0, v___x_1764_);
            return v___x_1765_;
        } else {
            let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_msg_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_ident_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1780_: u8 = 0;
            v___x_1766_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(v___x_1762_);
            v___x_1767_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Elab_TerminationBy_checkVars___closed__1),
                core::ptr::addr_of_mut!(l_Lean_Elab_TerminationBy_checkVars___closed__1_once),
                _init_l_Lean_Elab_TerminationBy_checkVars___closed__1,
            );
            v___x_1768_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1768_, 0, v___x_1766_);
            leanh::lean_ctor_set(v___x_1768_, 1, v___x_1767_);
            leanh::lean_inc(v_funName_1751_);
            v___x_1769_ = l_Lean_MessageData_ofName(v_funName_1751_);
            v___x_1770_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Elab_TerminationBy_checkVars___closed__3),
                core::ptr::addr_of_mut!(l_Lean_Elab_TerminationBy_checkVars___closed__3_once),
                _init_l_Lean_Elab_TerminationBy_checkVars___closed__3,
            );
            v___x_1771_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1771_, 0, v___x_1769_);
            leanh::lean_ctor_set(v___x_1771_, 1, v___x_1770_);
            v___x_1772_ = l___private_Lean_Elab_PreDefinition_TerminationHint_0__Lean_Elab_TerminationBy_checkVars_parameters(v_extraParams_1752_);
            v___x_1773_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1773_, 0, v___x_1771_);
            leanh::lean_ctor_set(v___x_1773_, 1, v___x_1772_);
            v___x_1774_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Elab_TerminationBy_checkVars___closed__5),
                core::ptr::addr_of_mut!(l_Lean_Elab_TerminationBy_checkVars___closed__5_once),
                _init_l_Lean_Elab_TerminationBy_checkVars___closed__5,
            );
            v___x_1775_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_1775_, 0, v___x_1773_);
            leanh::lean_ctor_set(v___x_1775_, 1, v___x_1774_);
            v_msg_1776_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
            leanh::lean_ctor_set(v_msg_1776_, 0, v___x_1768_);
            leanh::lean_ctor_set(v_msg_1776_, 1, v___x_1775_);
            v___x_1777_ = leanh::lean_unsigned_to_nat(0);
            v_ident_1778_ = lean_array_fget_borrowed(v_vars_1761_, v___x_1777_);
            v___x_1779_ = l_Lean_Elab_TerminationBy_checkVars___closed__7;
            leanh::lean_inc(v_ident_1778_);
            v___x_1780_ = l_Lean_Syntax_isOfKind(v_ident_1778_, v___x_1779_);
            if v___x_1780_ == 0 {
                let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_funName_1751_);
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
                let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1783_: u8 = 0;
                v___x_1782_ = l_Lean_TSyntax_getId(v_ident_1778_);
                v___x_1783_ = l_Lean_Name_isSuffixOf(v___x_1782_, v_funName_1751_);
                leanh::lean_dec(v_funName_1751_);
                leanh::lean_dec(v___x_1782_);
                if v___x_1783_ == 0 {
                    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1784_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_1760_, v_msg_1776_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_);
                    return v___x_1784_;
                } else {
                    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_msg_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1785_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_TerminationBy_checkVars___closed__9),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_TerminationBy_checkVars___closed__9_once
                        ),
                        _init_l_Lean_Elab_TerminationBy_checkVars___closed__9,
                    );
                    v___x_1786_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1786_, 0, v_msg_1776_);
                    leanh::lean_ctor_set(v___x_1786_, 1, v___x_1785_);
                    v___x_1787_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_TerminationBy_checkVars___closed__12),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_TerminationBy_checkVars___closed__12_once
                        ),
                        _init_l_Lean_Elab_TerminationBy_checkVars___closed__12,
                    );
                    v_msg_1788_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_msg_1788_, 0, v___x_1786_);
                    leanh::lean_ctor_set(v_msg_1788_, 1, v___x_1787_);
                    v___x_1789_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0___redArg(v_ref_1760_, v_msg_1788_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_);
                    return v___x_1789_;
                }
            }
        }
    } else {
        let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_extraParams_1752_);
        leanh::lean_dec(v_funName_1751_);
        v___x_1790_ = leanh::lean_box(0);
        v___x_1791_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1791_, 0, v___x_1790_);
        return v___x_1791_;
    }
}
pub unsafe fn l_Lean_Elab_TerminationBy_checkVars___boxed(
    mut v_funName_1792_: *mut leanh::LeanObject,
    mut v_extraParams_1793_: *mut leanh::LeanObject,
    mut v_tb_1794_: *mut leanh::LeanObject,
    mut v_a_1795_: *mut leanh::LeanObject,
    mut v_a_1796_: *mut leanh::LeanObject,
    mut v_a_1797_: *mut leanh::LeanObject,
    mut v_a_1798_: *mut leanh::LeanObject,
    mut v_a_1799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1800_ = l_Lean_Elab_TerminationBy_checkVars(
        v_funName_1792_,
        v_extraParams_1793_,
        v_tb_1794_,
        v_a_1795_,
        v_a_1796_,
        v_a_1797_,
        v_a_1798_,
    );
    leanh::lean_dec(v_a_1798_);
    leanh::lean_dec_ref(v_a_1797_);
    leanh::lean_dec(v_a_1796_);
    leanh::lean_dec_ref(v_a_1795_);
    leanh::lean_dec_ref(v_tb_1794_);
    return v_res_1800_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(
    mut v_00_u03b1_1801_: *mut leanh::LeanObject,
    mut v_ref_1802_: *mut leanh::LeanObject,
    mut v_msg_1803_: *mut leanh::LeanObject,
    mut v___y_1804_: *mut leanh::LeanObject,
    mut v___y_1805_: *mut leanh::LeanObject,
    mut v___y_1806_: *mut leanh::LeanObject,
    mut v___y_1807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1810_: *mut leanh::LeanObject,
    mut v_ref_1811_: *mut leanh::LeanObject,
    mut v_msg_1812_: *mut leanh::LeanObject,
    mut v___y_1813_: *mut leanh::LeanObject,
    mut v___y_1814_: *mut leanh::LeanObject,
    mut v___y_1815_: *mut leanh::LeanObject,
    mut v___y_1816_: *mut leanh::LeanObject,
    mut v___y_1817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1818_ = l_Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0(
        v_00_u03b1_1810_,
        v_ref_1811_,
        v_msg_1812_,
        v___y_1813_,
        v___y_1814_,
        v___y_1815_,
        v___y_1816_,
    );
    leanh::lean_dec(v___y_1816_);
    leanh::lean_dec_ref(v___y_1815_);
    leanh::lean_dec(v___y_1814_);
    leanh::lean_dec_ref(v___y_1813_);
    leanh::lean_dec(v_ref_1811_);
    return v_res_1818_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(
    mut v_00_u03b1_1819_: *mut leanh::LeanObject,
    mut v_msg_1820_: *mut leanh::LeanObject,
    mut v___y_1821_: *mut leanh::LeanObject,
    mut v___y_1822_: *mut leanh::LeanObject,
    mut v___y_1823_: *mut leanh::LeanObject,
    mut v___y_1824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1826_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___redArg(v_msg_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
    return v___x_1826_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0___boxed(
    mut v_00_u03b1_1827_: *mut leanh::LeanObject,
    mut v_msg_1828_: *mut leanh::LeanObject,
    mut v___y_1829_: *mut leanh::LeanObject,
    mut v___y_1830_: *mut leanh::LeanObject,
    mut v___y_1831_: *mut leanh::LeanObject,
    mut v___y_1832_: *mut leanh::LeanObject,
    mut v___y_1833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1834_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_TerminationBy_checkVars_spec__0_spec__0(v_00_u03b1_1827_, v_msg_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
    leanh::lean_dec(v___y_1832_);
    leanh::lean_dec_ref(v___y_1831_);
    leanh::lean_dec(v___y_1830_);
    leanh::lean_dec_ref(v___y_1829_);
    return v_res_1834_;
}
pub unsafe fn l_Lean_Elab_elabTerminationHints___redArg___lam__0(
    mut v_val_1835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1836_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1836_, 0, v_val_1835_);
    return v___x_1836_;
}
pub unsafe fn l_Lean_Elab_elabTerminationHints___redArg___lam__1(
    mut v_stx_1837_: *mut leanh::LeanObject,
    mut v_terminationBy_x3f_x3f_1838_: *mut leanh::LeanObject,
    mut v_terminationBy_x3f_1839_: *mut leanh::LeanObject,
    mut v_partialFixpoint_x3f_1840_: *mut leanh::LeanObject,
    mut v___x_1841_: *mut leanh::LeanObject,
    mut v_toPure_1842_: *mut leanh::LeanObject,
    mut v_decreasingBy_x3f_1843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1844_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_1844_, 0, v_stx_1837_);
    leanh::lean_ctor_set(v___x_1844_, 1, v_terminationBy_x3f_x3f_1838_);
    leanh::lean_ctor_set(v___x_1844_, 2, v_terminationBy_x3f_1839_);
    leanh::lean_ctor_set(v___x_1844_, 3, v_partialFixpoint_x3f_1840_);
    leanh::lean_ctor_set(v___x_1844_, 4, v_decreasingBy_x3f_1843_);
    leanh::lean_ctor_set(v___x_1844_, 5, v___x_1841_);
    v___x_1845_ =
        leanh::lean_apply_2(v_toPure_1842_, leanh::lean_box(0), v___x_1844_);
    return v___x_1845_;
}
pub unsafe fn _init_l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1848_ = l_Lean_Elab_elabTerminationHints___redArg___lam__2___closed__1;
    v___x_1849_ = l_Lean_stringToMessageData(v___x_1848_);
    return v___x_1849_;
}
pub unsafe fn l_Lean_Elab_elabTerminationHints___redArg___lam__2(
    mut v_stx_1850_: *mut leanh::LeanObject,
    mut v_terminationBy_x3f_x3f_1851_: *mut leanh::LeanObject,
    mut v_terminationBy_x3f_1852_: *mut leanh::LeanObject,
    mut v___x_1853_: *mut leanh::LeanObject,
    mut v_toPure_1854_: *mut leanh::LeanObject,
    mut v_d_x3f_1855_: *mut leanh::LeanObject,
    mut v_toBind_1856_: *mut leanh::LeanObject,
    mut v_toFunctor_1857_: *mut leanh::LeanObject,
    mut v___f_1858_: *mut leanh::LeanObject,
    mut v___x_1859_: *mut leanh::LeanObject,
    mut v___x_1860_: *mut leanh::LeanObject,
    mut v___x_1861_: *mut leanh::LeanObject,
    mut v_inst_1862_: *mut leanh::LeanObject,
    mut v_inst_1863_: *mut leanh::LeanObject,
    mut v___x_1864_: *mut leanh::LeanObject,
    mut v_partialFixpoint_x3f_1865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1874_: u8 = 0;
    let mut v___y_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: u8 = 0;
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tactic_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1889_: u8 = 0;
    let mut v_unused_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_toPure_1854_);
                v___f_1866_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_elabTerminationHints___redArg___lam__1 as *mut core::ffi::c_void,
                    7,
                    6,
                );
                leanh::lean_closure_set(v___f_1866_, 0, v_stx_1850_);
                leanh::lean_closure_set(v___f_1866_, 1, v_terminationBy_x3f_x3f_1851_);
                leanh::lean_closure_set(v___f_1866_, 2, v_terminationBy_x3f_1852_);
                leanh::lean_closure_set(v___f_1866_, 3, v_partialFixpoint_x3f_1865_);
                leanh::lean_closure_set(v___f_1866_, 4, v___x_1853_);
                leanh::lean_closure_set(v___f_1866_, 5, v_toPure_1854_);
                if leanh::lean_obj_tag(v_d_x3f_1855_) == 0 {
                    leanh::lean_dec_ref(v_inst_1863_);
                    leanh::lean_dec_ref(v_inst_1862_);
                    leanh::lean_dec_ref(v___x_1861_);
                    leanh::lean_dec_ref(v___x_1860_);
                    leanh::lean_dec_ref(v___x_1859_);
                    leanh::lean_dec_ref(v___f_1858_);
                    leanh::lean_dec_ref(v_toFunctor_1857_);
                    v___x_1867_ = leanh::lean_box(0);
                    v___x_1868_ = leanh::lean_apply_2(
                        v_toPure_1854_,
                        leanh::lean_box(0),
                        v___x_1867_,
                    );
                    v___x_1869_ = leanh::lean_apply_4(
                        v_toBind_1856_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1868_,
                        v___f_1866_,
                    );
                    return v___x_1869_;
                } else {
                    v_val_1870_ = leanh::lean_ctor_get(v_d_x3f_1855_, 0);
                    leanh::lean_inc(v_val_1870_);
                    leanh::lean_dec_ref_known(v_d_x3f_1855_, 1);
                    v_map_1871_ = leanh::lean_ctor_get(v_toFunctor_1857_, 0);
                    v_isSharedCheck_1889_ =
                        (!leanh::lean_is_exclusive(v_toFunctor_1857_)) as u8;
                    if v_isSharedCheck_1889_ == 0 {
                        v_unused_1890_ = leanh::lean_ctor_get(v_toFunctor_1857_, 1);
                        leanh::lean_dec(v_unused_1890_);
                        v___x_1873_ = v_toFunctor_1857_;
                        v_isShared_1874_ = v_isSharedCheck_1889_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_map_1871_);
                        leanh::lean_dec(v_toFunctor_1857_);
                        v___x_1873_ = leanh::lean_box(0);
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
                leanh::lean_inc(v_val_1870_);
                v___x_1881_ = l_Lean_Syntax_isOfKind(v_val_1870_, v___x_1880_);
                leanh::lean_dec(v___x_1880_);
                if v___x_1881_ == 0 {
                    leanh::lean_del_object(v___x_1873_);
                    leanh::lean_dec(v_toPure_1854_);
                    v___x_1882_ = leanh::lean_obj_once(
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
                    leanh::lean_dec_ref(v_inst_1863_);
                    leanh::lean_dec_ref(v_inst_1862_);
                    v_tactic_1884_ = l_Lean_Syntax_getArg(v_val_1870_, v___x_1864_);
                    if v_isShared_1874_ == 0 {
                        leanh::lean_ctor_set(v___x_1873_, 1, v_tactic_1884_);
                        leanh::lean_ctor_set(v___x_1873_, 0, v_val_1870_);
                        v___x_1886_ = v___x_1873_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1888_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_val_1870_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_tactic_1884_);
                        v___x_1886_ = v_reuseFailAlloc_1888_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1877_ = leanh::lean_apply_4(
                    v_map_1871_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___f_1858_,
                    v___y_1876_,
                );
                v___x_1878_ = leanh::lean_apply_4(
                    v_toBind_1856_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1877_,
                    v___f_1866_,
                );
                return v___x_1878_;
            }
            3 => {
                v___x_1887_ = leanh::lean_apply_2(
                    v_toPure_1854_,
                    leanh::lean_box(0),
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
    mut v_stx_1891_: *mut leanh::LeanObject,
    mut v_terminationBy_x3f_x3f_1892_: *mut leanh::LeanObject,
    mut v_terminationBy_x3f_1893_: *mut leanh::LeanObject,
    mut v___x_1894_: *mut leanh::LeanObject,
    mut v_toPure_1895_: *mut leanh::LeanObject,
    mut v_d_x3f_1896_: *mut leanh::LeanObject,
    mut v_toBind_1897_: *mut leanh::LeanObject,
    mut v_toFunctor_1898_: *mut leanh::LeanObject,
    mut v___f_1899_: *mut leanh::LeanObject,
    mut v___x_1900_: *mut leanh::LeanObject,
    mut v___x_1901_: *mut leanh::LeanObject,
    mut v___x_1902_: *mut leanh::LeanObject,
    mut v_inst_1903_: *mut leanh::LeanObject,
    mut v_inst_1904_: *mut leanh::LeanObject,
    mut v___x_1905_: *mut leanh::LeanObject,
    mut v_partialFixpoint_x3f_1906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___x_1905_);
    return v_res_1907_;
}
pub unsafe fn l_Lean_Elab_elabTerminationHints___redArg___lam__3(
    mut v___f_1908_: *mut leanh::LeanObject,
    mut v_partialFixpoint_x3f_1909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1910_ = leanh::lean_apply_1(v___f_1908_, v_partialFixpoint_x3f_1909_);
    return v___x_1910_;
}
pub unsafe fn l_Lean_Elab_elabTerminationHints___redArg___lam__11(
    mut v_stx_1914_: *mut leanh::LeanObject,
    mut v_terminationBy_x3f_x3f_1915_: *mut leanh::LeanObject,
    mut v___x_1916_: *mut leanh::LeanObject,
    mut v_toPure_1917_: *mut leanh::LeanObject,
    mut v_d_x3f_1918_: *mut leanh::LeanObject,
    mut v_toBind_1919_: *mut leanh::LeanObject,
    mut v_toFunctor_1920_: *mut leanh::LeanObject,
    mut v___f_1921_: *mut leanh::LeanObject,
    mut v___x_1922_: *mut leanh::LeanObject,
    mut v___x_1923_: *mut leanh::LeanObject,
    mut v___x_1924_: *mut leanh::LeanObject,
    mut v_inst_1925_: *mut leanh::LeanObject,
    mut v_inst_1926_: *mut leanh::LeanObject,
    mut v___x_1927_: *mut leanh::LeanObject,
    mut v_t_x3f_1928_: *mut leanh::LeanObject,
    mut v_terminationBy_x3f_1929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1934_: u8 = 0;
    let mut v___x_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: u8 = 0;
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: u8 = 0;
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: u8 = 0;
    let mut v___f_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_x3f_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: u8 = 0;
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: u8 = 0;
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: u8 = 0;
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_x3f_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_x3f_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: u8 = 0;
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: u8 = 0;
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: u8 = 0;
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_x3f_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_x3f_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: u8 = 0;
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: u8 = 0;
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: u8 = 0;
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_term_x3f_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2008_: u8 = 0;
    let mut v___f_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___x_1927_);
                leanh::lean_inc_ref(v___x_1924_);
                leanh::lean_inc_ref(v___x_1923_);
                leanh::lean_inc_ref(v___x_1922_);
                leanh::lean_inc(v_toBind_1919_);
                leanh::lean_inc(v_toPure_1917_);
                v___f_1930_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_elabTerminationHints___redArg___lam__2___boxed
                        as *mut core::ffi::c_void,
                    16,
                    15,
                );
                leanh::lean_closure_set(v___f_1930_, 0, v_stx_1914_);
                leanh::lean_closure_set(v___f_1930_, 1, v_terminationBy_x3f_x3f_1915_);
                leanh::lean_closure_set(v___f_1930_, 2, v_terminationBy_x3f_1929_);
                leanh::lean_closure_set(v___f_1930_, 3, v___x_1916_);
                leanh::lean_closure_set(v___f_1930_, 4, v_toPure_1917_);
                leanh::lean_closure_set(v___f_1930_, 5, v_d_x3f_1918_);
                leanh::lean_closure_set(v___f_1930_, 6, v_toBind_1919_);
                leanh::lean_closure_set(v___f_1930_, 7, v_toFunctor_1920_);
                leanh::lean_closure_set(v___f_1930_, 8, v___f_1921_);
                leanh::lean_closure_set(v___f_1930_, 9, v___x_1922_);
                leanh::lean_closure_set(v___f_1930_, 10, v___x_1923_);
                leanh::lean_closure_set(v___f_1930_, 11, v___x_1924_);
                leanh::lean_closure_set(v___f_1930_, 12, v_inst_1925_);
                leanh::lean_closure_set(v___f_1930_, 13, v_inst_1926_);
                leanh::lean_closure_set(v___f_1930_, 14, v___x_1927_);
                if leanh::lean_obj_tag(v_t_x3f_1928_) == 1 {
                    v_val_1931_ = leanh::lean_ctor_get(v_t_x3f_1928_, 0);
                    v_isSharedCheck_2008_ = (!leanh::lean_is_exclusive(v_t_x3f_1928_)) as u8;
                    if v_isSharedCheck_2008_ == 0 {
                        v___x_1933_ = v_t_x3f_1928_;
                        v_isShared_1934_ = v_isSharedCheck_2008_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1931_);
                        leanh::lean_dec(v_t_x3f_1928_);
                        v___x_1933_ = leanh::lean_box(0);
                        v_isShared_1934_ = v_isSharedCheck_2008_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_t_x3f_1928_);
                    leanh::lean_dec(v___x_1927_);
                    leanh::lean_dec_ref(v___x_1924_);
                    leanh::lean_dec_ref(v___x_1923_);
                    leanh::lean_dec_ref(v___x_1922_);
                    v___f_2009_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_elabTerminationHints___redArg___lam__3
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_2009_, 0, v___f_1930_);
                    v___x_2010_ = leanh::lean_box(0);
                    v___x_2011_ = leanh::lean_apply_2(
                        v_toPure_1917_,
                        leanh::lean_box(0),
                        v___x_2010_,
                    );
                    v___x_2012_ = leanh::lean_apply_4(
                        v_toBind_1919_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2011_,
                        v___f_2009_,
                    );
                    return v___x_2012_;
                }
            }
            1 => {
                v___x_1935_ = l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0;
                leanh::lean_inc_ref(v___x_1924_);
                leanh::lean_inc_ref(v___x_1923_);
                leanh::lean_inc_ref(v___x_1922_);
                v___x_1936_ =
                    l_Lean_Name_mkStr4(v___x_1922_, v___x_1923_, v___x_1924_, v___x_1935_);
                leanh::lean_inc(v_val_1931_);
                v___x_1937_ = l_Lean_Syntax_isOfKind(v_val_1931_, v___x_1936_);
                leanh::lean_dec(v___x_1936_);
                if v___x_1937_ == 0 {
                    v___x_1938_ = l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1;
                    leanh::lean_inc_ref(v___x_1924_);
                    leanh::lean_inc_ref(v___x_1923_);
                    leanh::lean_inc_ref(v___x_1922_);
                    v___x_1939_ =
                        l_Lean_Name_mkStr4(v___x_1922_, v___x_1923_, v___x_1924_, v___x_1938_);
                    leanh::lean_inc(v_val_1931_);
                    v___x_1940_ = l_Lean_Syntax_isOfKind(v_val_1931_, v___x_1939_);
                    leanh::lean_dec(v___x_1939_);
                    if v___x_1940_ == 0 {
                        v___x_1941_ =
                            l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2;
                        v___x_1942_ =
                            l_Lean_Name_mkStr4(v___x_1922_, v___x_1923_, v___x_1924_, v___x_1941_);
                        leanh::lean_inc(v_val_1931_);
                        v___x_1943_ = l_Lean_Syntax_isOfKind(v_val_1931_, v___x_1942_);
                        leanh::lean_dec(v___x_1942_);
                        if v___x_1943_ == 0 {
                            leanh::lean_del_object(v___x_1933_);
                            leanh::lean_dec(v_val_1931_);
                            leanh::lean_dec(v___x_1927_);
                            v___f_1944_ = leanh::lean_alloc_closure(
                                l_Lean_Elab_elabTerminationHints___redArg___lam__3
                                    as *mut core::ffi::c_void,
                                2,
                                1,
                            );
                            leanh::lean_closure_set(v___f_1944_, 0, v___f_1930_);
                            v___x_1945_ = leanh::lean_box(0);
                            v___x_1946_ = leanh::lean_apply_2(
                                v_toPure_1917_,
                                leanh::lean_box(0),
                                v___x_1945_,
                            );
                            v___x_1947_ = leanh::lean_apply_4(
                                v_toBind_1919_,
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v___x_1946_,
                                v___f_1944_,
                            );
                            return v___x_1947_;
                        } else {
                            v___f_1948_ = leanh::lean_alloc_closure(
                                l_Lean_Elab_elabTerminationHints___redArg___lam__3
                                    as *mut core::ffi::c_void,
                                2,
                                1,
                            );
                            leanh::lean_closure_set(v___f_1948_, 0, v___f_1930_);
                            v___x_1958_ = l_Lean_Syntax_getArg(v_val_1931_, v___x_1927_);
                            v___x_1959_ = l_Lean_Syntax_isNone(v___x_1958_);
                            if v___x_1959_ == 0 {
                                v___x_1960_ = leanh::lean_unsigned_to_nat(2);
                                leanh::lean_inc(v___x_1958_);
                                v___x_1961_ = l_Lean_Syntax_matchesNull(v___x_1958_, v___x_1960_);
                                if v___x_1961_ == 0 {
                                    leanh::lean_dec(v___x_1958_);
                                    leanh::lean_del_object(v___x_1933_);
                                    leanh::lean_dec(v_val_1931_);
                                    leanh::lean_dec(v___x_1927_);
                                    v___x_1962_ = leanh::lean_box(0);
                                    v___x_1963_ = leanh::lean_apply_2(
                                        v_toPure_1917_,
                                        leanh::lean_box(0),
                                        v___x_1962_,
                                    );
                                    v___x_1964_ = leanh::lean_apply_4(
                                        v_toBind_1919_,
                                        leanh::lean_box(0),
                                        leanh::lean_box(0),
                                        v___x_1963_,
                                        v___f_1948_,
                                    );
                                    return v___x_1964_;
                                } else {
                                    v_term_x3f_1965_ =
                                        l_Lean_Syntax_getArg(v___x_1958_, v___x_1927_);
                                    leanh::lean_dec(v___x_1927_);
                                    leanh::lean_dec(v___x_1958_);
                                    v___x_1966_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_1966_, 0, v_term_x3f_1965_);
                                    v_term_x3f_1950_ = v___x_1966_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v___x_1958_);
                                leanh::lean_dec(v___x_1927_);
                                v___x_1967_ = leanh::lean_box(0);
                                v_term_x3f_1950_ = v___x_1967_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_1924_);
                        leanh::lean_dec_ref(v___x_1923_);
                        leanh::lean_dec_ref(v___x_1922_);
                        v___f_1968_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_elabTerminationHints___redArg___lam__3
                                as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        leanh::lean_closure_set(v___f_1968_, 0, v___f_1930_);
                        v___x_1978_ = l_Lean_Syntax_getArg(v_val_1931_, v___x_1927_);
                        v___x_1979_ = l_Lean_Syntax_isNone(v___x_1978_);
                        if v___x_1979_ == 0 {
                            v___x_1980_ = leanh::lean_unsigned_to_nat(2);
                            leanh::lean_inc(v___x_1978_);
                            v___x_1981_ = l_Lean_Syntax_matchesNull(v___x_1978_, v___x_1980_);
                            if v___x_1981_ == 0 {
                                leanh::lean_dec(v___x_1978_);
                                leanh::lean_del_object(v___x_1933_);
                                leanh::lean_dec(v_val_1931_);
                                leanh::lean_dec(v___x_1927_);
                                v___x_1982_ = leanh::lean_box(0);
                                v___x_1983_ = leanh::lean_apply_2(
                                    v_toPure_1917_,
                                    leanh::lean_box(0),
                                    v___x_1982_,
                                );
                                v___x_1984_ = leanh::lean_apply_4(
                                    v_toBind_1919_,
                                    leanh::lean_box(0),
                                    leanh::lean_box(0),
                                    v___x_1983_,
                                    v___f_1968_,
                                );
                                return v___x_1984_;
                            } else {
                                v_term_x3f_1985_ = l_Lean_Syntax_getArg(v___x_1978_, v___x_1927_);
                                leanh::lean_dec(v___x_1927_);
                                leanh::lean_dec(v___x_1978_);
                                v___x_1986_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1986_, 0, v_term_x3f_1985_);
                                v_term_x3f_1970_ = v___x_1986_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_1978_);
                            leanh::lean_dec(v___x_1927_);
                            v___x_1987_ = leanh::lean_box(0);
                            v_term_x3f_1970_ = v___x_1987_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_1924_);
                    leanh::lean_dec_ref(v___x_1923_);
                    leanh::lean_dec_ref(v___x_1922_);
                    v___f_1988_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_elabTerminationHints___redArg___lam__3
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_1988_, 0, v___f_1930_);
                    v___x_1998_ = l_Lean_Syntax_getArg(v_val_1931_, v___x_1927_);
                    v___x_1999_ = l_Lean_Syntax_isNone(v___x_1998_);
                    if v___x_1999_ == 0 {
                        v___x_2000_ = leanh::lean_unsigned_to_nat(2);
                        leanh::lean_inc(v___x_1998_);
                        v___x_2001_ = l_Lean_Syntax_matchesNull(v___x_1998_, v___x_2000_);
                        if v___x_2001_ == 0 {
                            leanh::lean_dec(v___x_1998_);
                            leanh::lean_del_object(v___x_1933_);
                            leanh::lean_dec(v_val_1931_);
                            leanh::lean_dec(v___x_1927_);
                            v___x_2002_ = leanh::lean_box(0);
                            v___x_2003_ = leanh::lean_apply_2(
                                v_toPure_1917_,
                                leanh::lean_box(0),
                                v___x_2002_,
                            );
                            v___x_2004_ = leanh::lean_apply_4(
                                v_toBind_1919_,
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v___x_2003_,
                                v___f_1988_,
                            );
                            return v___x_2004_;
                        } else {
                            v_term_x3f_2005_ = l_Lean_Syntax_getArg(v___x_1998_, v___x_1927_);
                            leanh::lean_dec(v___x_1927_);
                            leanh::lean_dec(v___x_1998_);
                            v___x_2006_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2006_, 0, v_term_x3f_2005_);
                            v_term_x3f_1990_ = v___x_2006_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1998_);
                        leanh::lean_dec(v___x_1927_);
                        v___x_2007_ = leanh::lean_box(0);
                        v_term_x3f_1990_ = v___x_2007_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1951_ = 2;
                v___x_1952_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_1952_, 0, v_val_1931_);
                leanh::lean_ctor_set(v___x_1952_, 1, v_term_x3f_1950_);
                leanh::lean_ctor_set_uint8(
                    v___x_1952_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_1951_,
                );
                if v_isShared_1934_ == 0 {
                    leanh::lean_ctor_set(v___x_1933_, 0, v___x_1952_);
                    v___x_1954_ = v___x_1933_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1957_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1952_);
                    v___x_1954_ = v_reuseFailAlloc_1957_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1955_ = leanh::lean_apply_2(
                    v_toPure_1917_,
                    leanh::lean_box(0),
                    v___x_1954_,
                );
                v___x_1956_ = leanh::lean_apply_4(
                    v_toBind_1919_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1955_,
                    v___f_1948_,
                );
                return v___x_1956_;
            }
            4 => {
                v___x_1971_ = 1;
                v___x_1972_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_1972_, 0, v_val_1931_);
                leanh::lean_ctor_set(v___x_1972_, 1, v_term_x3f_1970_);
                leanh::lean_ctor_set_uint8(
                    v___x_1972_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_1971_,
                );
                if v_isShared_1934_ == 0 {
                    leanh::lean_ctor_set(v___x_1933_, 0, v___x_1972_);
                    v___x_1974_ = v___x_1933_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1977_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1972_);
                    v___x_1974_ = v_reuseFailAlloc_1977_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1975_ = leanh::lean_apply_2(
                    v_toPure_1917_,
                    leanh::lean_box(0),
                    v___x_1974_,
                );
                v___x_1976_ = leanh::lean_apply_4(
                    v_toBind_1919_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1975_,
                    v___f_1968_,
                );
                return v___x_1976_;
            }
            6 => {
                v___x_1991_ = 0;
                v___x_1992_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_1992_, 0, v_val_1931_);
                leanh::lean_ctor_set(v___x_1992_, 1, v_term_x3f_1990_);
                leanh::lean_ctor_set_uint8(
                    v___x_1992_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_1991_,
                );
                if v_isShared_1934_ == 0 {
                    leanh::lean_ctor_set(v___x_1933_, 0, v___x_1992_);
                    v___x_1994_ = v___x_1933_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1997_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1992_);
                    v___x_1994_ = v_reuseFailAlloc_1997_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1995_ = leanh::lean_apply_2(
                    v_toPure_1917_,
                    leanh::lean_box(0),
                    v___x_1994_,
                );
                v___x_1996_ = leanh::lean_apply_4(
                    v_toBind_1919_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
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
    mut v___f_2013_: *mut leanh::LeanObject,
    mut v_terminationBy_x3f_2014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2015_ = leanh::lean_apply_1(v___f_2013_, v_terminationBy_x3f_2014_);
    return v___x_2015_;
}
pub unsafe fn _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2019_ = l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__2;
    v___x_2020_ = l_Lean_stringToMessageData(v___x_2019_);
    return v___x_2020_;
}
pub unsafe fn _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2022_ = l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__4;
    v___x_2023_ = l_Lean_stringToMessageData(v___x_2022_);
    return v___x_2023_;
}
pub unsafe fn l_Lean_Elab_elabTerminationHints___redArg___lam__19(
    mut v_stx_2024_: *mut leanh::LeanObject,
    mut v___x_2025_: *mut leanh::LeanObject,
    mut v_toPure_2026_: *mut leanh::LeanObject,
    mut v_d_x3f_2027_: *mut leanh::LeanObject,
    mut v_toBind_2028_: *mut leanh::LeanObject,
    mut v_toFunctor_2029_: *mut leanh::LeanObject,
    mut v___f_2030_: *mut leanh::LeanObject,
    mut v___x_2031_: *mut leanh::LeanObject,
    mut v___x_2032_: *mut leanh::LeanObject,
    mut v___x_2033_: *mut leanh::LeanObject,
    mut v_inst_2034_: *mut leanh::LeanObject,
    mut v_inst_2035_: *mut leanh::LeanObject,
    mut v___x_2036_: *mut leanh::LeanObject,
    mut v_t_x3f_2037_: *mut leanh::LeanObject,
    mut v_terminationBy_x3f_x3f_2038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2043_: u8 = 0;
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: u8 = 0;
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: u8 = 0;
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: u8 = 0;
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: u8 = 0;
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: u8 = 0;
    let mut v___f_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: u8 = 0;
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: u8 = 0;
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: u8 = 0;
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: u8 = 0;
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: u8 = 0;
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: u8 = 0;
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2107_: u8 = 0;
    let mut v___y_2108_: u8 = 0;
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2117_: u8 = 0;
    let mut v___y_2118_: u8 = 0;
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: u8 = 0;
    let mut v___x_2129_: u8 = 0;
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: u8 = 0;
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: u8 = 0;
    let mut v___x_2145_: u8 = 0;
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2152_: u8 = 0;
    let mut v___f_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_t_x3f_2037_);
                leanh::lean_inc(v___x_2036_);
                leanh::lean_inc_ref(v_inst_2035_);
                leanh::lean_inc_ref(v_inst_2034_);
                leanh::lean_inc_ref(v___x_2033_);
                leanh::lean_inc_ref(v___x_2032_);
                leanh::lean_inc_ref(v___x_2031_);
                leanh::lean_inc(v_toBind_2028_);
                leanh::lean_inc(v_toPure_2026_);
                leanh::lean_inc(v___x_2025_);
                v___f_2039_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_elabTerminationHints___redArg___lam__11 as *mut core::ffi::c_void,
                    16,
                    15,
                );
                leanh::lean_closure_set(v___f_2039_, 0, v_stx_2024_);
                leanh::lean_closure_set(v___f_2039_, 1, v_terminationBy_x3f_x3f_2038_);
                leanh::lean_closure_set(v___f_2039_, 2, v___x_2025_);
                leanh::lean_closure_set(v___f_2039_, 3, v_toPure_2026_);
                leanh::lean_closure_set(v___f_2039_, 4, v_d_x3f_2027_);
                leanh::lean_closure_set(v___f_2039_, 5, v_toBind_2028_);
                leanh::lean_closure_set(v___f_2039_, 6, v_toFunctor_2029_);
                leanh::lean_closure_set(v___f_2039_, 7, v___f_2030_);
                leanh::lean_closure_set(v___f_2039_, 8, v___x_2031_);
                leanh::lean_closure_set(v___f_2039_, 9, v___x_2032_);
                leanh::lean_closure_set(v___f_2039_, 10, v___x_2033_);
                leanh::lean_closure_set(v___f_2039_, 11, v_inst_2034_);
                leanh::lean_closure_set(v___f_2039_, 12, v_inst_2035_);
                leanh::lean_closure_set(v___f_2039_, 13, v___x_2036_);
                leanh::lean_closure_set(v___f_2039_, 14, v_t_x3f_2037_);
                if leanh::lean_obj_tag(v_t_x3f_2037_) == 1 {
                    v_val_2040_ = leanh::lean_ctor_get(v_t_x3f_2037_, 0);
                    v_isSharedCheck_2152_ = (!leanh::lean_is_exclusive(v_t_x3f_2037_)) as u8;
                    if v_isSharedCheck_2152_ == 0 {
                        v___x_2042_ = v_t_x3f_2037_;
                        v_isShared_2043_ = v_isSharedCheck_2152_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2040_);
                        leanh::lean_dec(v_t_x3f_2037_);
                        v___x_2042_ = leanh::lean_box(0);
                        v_isShared_2043_ = v_isSharedCheck_2152_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_t_x3f_2037_);
                    leanh::lean_dec(v___x_2036_);
                    leanh::lean_dec_ref(v_inst_2035_);
                    leanh::lean_dec_ref(v_inst_2034_);
                    leanh::lean_dec_ref(v___x_2033_);
                    leanh::lean_dec_ref(v___x_2032_);
                    leanh::lean_dec_ref(v___x_2031_);
                    leanh::lean_dec(v___x_2025_);
                    v___f_2153_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_elabTerminationHints___redArg___lam__4
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_2153_, 0, v___f_2039_);
                    v___x_2154_ = leanh::lean_box(0);
                    v___x_2155_ = leanh::lean_apply_2(
                        v_toPure_2026_,
                        leanh::lean_box(0),
                        v___x_2154_,
                    );
                    v___x_2156_ = leanh::lean_apply_4(
                        v_toBind_2028_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2155_,
                        v___f_2153_,
                    );
                    return v___x_2156_;
                }
            }
            1 => {
                v___x_2044_ = l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__0;
                leanh::lean_inc_ref(v___x_2033_);
                leanh::lean_inc_ref(v___x_2032_);
                leanh::lean_inc_ref(v___x_2031_);
                v___x_2045_ =
                    l_Lean_Name_mkStr4(v___x_2031_, v___x_2032_, v___x_2033_, v___x_2044_);
                leanh::lean_inc(v_val_2040_);
                v___x_2046_ = l_Lean_Syntax_isOfKind(v_val_2040_, v___x_2045_);
                leanh::lean_dec(v___x_2045_);
                if v___x_2046_ == 0 {
                    leanh::lean_del_object(v___x_2042_);
                    leanh::lean_dec(v___x_2025_);
                    v___x_2047_ = l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__1;
                    leanh::lean_inc_ref(v___x_2033_);
                    leanh::lean_inc_ref(v___x_2032_);
                    leanh::lean_inc_ref(v___x_2031_);
                    v___x_2048_ =
                        l_Lean_Name_mkStr4(v___x_2031_, v___x_2032_, v___x_2033_, v___x_2047_);
                    leanh::lean_inc(v_val_2040_);
                    v___x_2049_ = l_Lean_Syntax_isOfKind(v_val_2040_, v___x_2048_);
                    leanh::lean_dec(v___x_2048_);
                    if v___x_2049_ == 0 {
                        v___x_2050_ =
                            l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__0;
                        leanh::lean_inc_ref(v___x_2033_);
                        leanh::lean_inc_ref(v___x_2032_);
                        leanh::lean_inc_ref(v___x_2031_);
                        v___x_2051_ =
                            l_Lean_Name_mkStr4(v___x_2031_, v___x_2032_, v___x_2033_, v___x_2050_);
                        leanh::lean_inc(v_val_2040_);
                        v___x_2052_ = l_Lean_Syntax_isOfKind(v_val_2040_, v___x_2051_);
                        leanh::lean_dec(v___x_2051_);
                        if v___x_2052_ == 0 {
                            v___x_2053_ =
                                l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__1;
                            leanh::lean_inc_ref(v___x_2033_);
                            leanh::lean_inc_ref(v___x_2032_);
                            leanh::lean_inc_ref(v___x_2031_);
                            v___x_2054_ = l_Lean_Name_mkStr4(
                                v___x_2031_,
                                v___x_2032_,
                                v___x_2033_,
                                v___x_2053_,
                            );
                            leanh::lean_inc(v_val_2040_);
                            v___x_2055_ = l_Lean_Syntax_isOfKind(v_val_2040_, v___x_2054_);
                            leanh::lean_dec(v___x_2054_);
                            if v___x_2055_ == 0 {
                                v___x_2056_ =
                                    l_Lean_Elab_elabTerminationHints___redArg___lam__11___closed__2;
                                v___x_2057_ = l_Lean_Name_mkStr4(
                                    v___x_2031_,
                                    v___x_2032_,
                                    v___x_2033_,
                                    v___x_2056_,
                                );
                                leanh::lean_inc(v_val_2040_);
                                v___x_2058_ = l_Lean_Syntax_isOfKind(v_val_2040_, v___x_2057_);
                                leanh::lean_dec(v___x_2057_);
                                if v___x_2058_ == 0 {
                                    leanh::lean_dec(v___x_2036_);
                                    leanh::lean_dec(v_toPure_2026_);
                                    v___f_2059_ = leanh::lean_alloc_closure(
                                        l_Lean_Elab_elabTerminationHints___redArg___lam__4
                                            as *mut core::ffi::c_void,
                                        2,
                                        1,
                                    );
                                    leanh::lean_closure_set(v___f_2059_, 0, v___f_2039_);
                                    v___x_2060_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once), _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
                                    v___x_2061_ = l_Lean_throwErrorAt___redArg(
                                        v_inst_2034_,
                                        v_inst_2035_,
                                        v_val_2040_,
                                        v___x_2060_,
                                    );
                                    v___x_2062_ = leanh::lean_apply_4(
                                        v_toBind_2028_,
                                        leanh::lean_box(0),
                                        leanh::lean_box(0),
                                        v___x_2061_,
                                        v___f_2059_,
                                    );
                                    return v___x_2062_;
                                } else {
                                    v___f_2063_ = leanh::lean_alloc_closure(
                                        l_Lean_Elab_elabTerminationHints___redArg___lam__4
                                            as *mut core::ffi::c_void,
                                        2,
                                        1,
                                    );
                                    leanh::lean_closure_set(v___f_2063_, 0, v___f_2039_);
                                    v___x_2068_ = l_Lean_Syntax_getArg(v_val_2040_, v___x_2036_);
                                    leanh::lean_dec(v___x_2036_);
                                    v___x_2069_ = l_Lean_Syntax_isNone(v___x_2068_);
                                    if v___x_2069_ == 0 {
                                        v___x_2070_ = leanh::lean_unsigned_to_nat(2);
                                        v___x_2071_ =
                                            l_Lean_Syntax_matchesNull(v___x_2068_, v___x_2070_);
                                        if v___x_2071_ == 0 {
                                            leanh::lean_dec(v_toPure_2026_);
                                            v___x_2072_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once), _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
                                            v___x_2073_ = l_Lean_throwErrorAt___redArg(
                                                v_inst_2034_,
                                                v_inst_2035_,
                                                v_val_2040_,
                                                v___x_2072_,
                                            );
                                            v___x_2074_ = leanh::lean_apply_4(
                                                v_toBind_2028_,
                                                leanh::lean_box(0),
                                                leanh::lean_box(0),
                                                v___x_2073_,
                                                v___f_2063_,
                                            );
                                            return v___x_2074_;
                                        } else {
                                            leanh::lean_dec(v_val_2040_);
                                            leanh::lean_dec_ref(v_inst_2035_);
                                            leanh::lean_dec_ref(v_inst_2034_);
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v___x_2068_);
                                        leanh::lean_dec(v_val_2040_);
                                        leanh::lean_dec_ref(v_inst_2035_);
                                        leanh::lean_dec_ref(v_inst_2034_);
                                        state = 2;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_2033_);
                                leanh::lean_dec_ref(v___x_2032_);
                                leanh::lean_dec_ref(v___x_2031_);
                                v___f_2075_ = leanh::lean_alloc_closure(
                                    l_Lean_Elab_elabTerminationHints___redArg___lam__4
                                        as *mut core::ffi::c_void,
                                    2,
                                    1,
                                );
                                leanh::lean_closure_set(v___f_2075_, 0, v___f_2039_);
                                v___x_2080_ = l_Lean_Syntax_getArg(v_val_2040_, v___x_2036_);
                                leanh::lean_dec(v___x_2036_);
                                v___x_2081_ = l_Lean_Syntax_isNone(v___x_2080_);
                                if v___x_2081_ == 0 {
                                    v___x_2082_ = leanh::lean_unsigned_to_nat(2);
                                    v___x_2083_ =
                                        l_Lean_Syntax_matchesNull(v___x_2080_, v___x_2082_);
                                    if v___x_2083_ == 0 {
                                        leanh::lean_dec(v_toPure_2026_);
                                        v___x_2084_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once), _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
                                        v___x_2085_ = l_Lean_throwErrorAt___redArg(
                                            v_inst_2034_,
                                            v_inst_2035_,
                                            v_val_2040_,
                                            v___x_2084_,
                                        );
                                        v___x_2086_ = leanh::lean_apply_4(
                                            v_toBind_2028_,
                                            leanh::lean_box(0),
                                            leanh::lean_box(0),
                                            v___x_2085_,
                                            v___f_2075_,
                                        );
                                        return v___x_2086_;
                                    } else {
                                        leanh::lean_dec(v_val_2040_);
                                        leanh::lean_dec_ref(v_inst_2035_);
                                        leanh::lean_dec_ref(v_inst_2034_);
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v___x_2080_);
                                    leanh::lean_dec(v_val_2040_);
                                    leanh::lean_dec_ref(v_inst_2035_);
                                    leanh::lean_dec_ref(v_inst_2034_);
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_2033_);
                            leanh::lean_dec_ref(v___x_2032_);
                            leanh::lean_dec_ref(v___x_2031_);
                            v___f_2087_ = leanh::lean_alloc_closure(
                                l_Lean_Elab_elabTerminationHints___redArg___lam__4
                                    as *mut core::ffi::c_void,
                                2,
                                1,
                            );
                            leanh::lean_closure_set(v___f_2087_, 0, v___f_2039_);
                            v___x_2092_ = l_Lean_Syntax_getArg(v_val_2040_, v___x_2036_);
                            leanh::lean_dec(v___x_2036_);
                            v___x_2093_ = l_Lean_Syntax_isNone(v___x_2092_);
                            if v___x_2093_ == 0 {
                                v___x_2094_ = leanh::lean_unsigned_to_nat(2);
                                v___x_2095_ = l_Lean_Syntax_matchesNull(v___x_2092_, v___x_2094_);
                                if v___x_2095_ == 0 {
                                    leanh::lean_dec(v_toPure_2026_);
                                    v___x_2096_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once), _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
                                    v___x_2097_ = l_Lean_throwErrorAt___redArg(
                                        v_inst_2034_,
                                        v_inst_2035_,
                                        v_val_2040_,
                                        v___x_2096_,
                                    );
                                    v___x_2098_ = leanh::lean_apply_4(
                                        v_toBind_2028_,
                                        leanh::lean_box(0),
                                        leanh::lean_box(0),
                                        v___x_2097_,
                                        v___f_2087_,
                                    );
                                    return v___x_2098_;
                                } else {
                                    leanh::lean_dec(v_val_2040_);
                                    leanh::lean_dec_ref(v_inst_2035_);
                                    leanh::lean_dec_ref(v_inst_2034_);
                                    state = 4;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v___x_2092_);
                                leanh::lean_dec(v_val_2040_);
                                leanh::lean_dec_ref(v_inst_2035_);
                                leanh::lean_dec_ref(v_inst_2034_);
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_val_2040_);
                        leanh::lean_dec(v___x_2036_);
                        leanh::lean_dec_ref(v_inst_2035_);
                        leanh::lean_dec_ref(v_inst_2034_);
                        leanh::lean_dec_ref(v___x_2033_);
                        leanh::lean_dec_ref(v___x_2032_);
                        leanh::lean_dec_ref(v___x_2031_);
                        v___f_2099_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_elabTerminationHints___redArg___lam__4
                                as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        leanh::lean_closure_set(v___f_2099_, 0, v___f_2039_);
                        v___x_2100_ = leanh::lean_box(0);
                        v___x_2101_ = leanh::lean_apply_2(
                            v_toPure_2026_,
                            leanh::lean_box(0),
                            v___x_2100_,
                        );
                        v___x_2102_ = leanh::lean_apply_4(
                            v_toBind_2028_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_2101_,
                            v___f_2099_,
                        );
                        return v___x_2102_;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_2033_);
                    leanh::lean_dec_ref(v___x_2032_);
                    leanh::lean_dec_ref(v___x_2031_);
                    v___f_2103_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_elabTerminationHints___redArg___lam__4
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_2103_, 0, v___f_2039_);
                    v___x_2143_ = l_Lean_Syntax_getArg(v_val_2040_, v___x_2036_);
                    v___x_2144_ = l_Lean_Syntax_isNone(v___x_2143_);
                    if v___x_2144_ == 0 {
                        leanh::lean_inc(v___x_2143_);
                        v___x_2145_ = l_Lean_Syntax_matchesNull(v___x_2143_, v___x_2036_);
                        leanh::lean_dec(v___x_2036_);
                        if v___x_2145_ == 0 {
                            leanh::lean_dec(v___x_2143_);
                            leanh::lean_del_object(v___x_2042_);
                            leanh::lean_dec(v_toPure_2026_);
                            leanh::lean_dec(v___x_2025_);
                            v___x_2146_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once), _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
                            v___x_2147_ = l_Lean_throwErrorAt___redArg(
                                v_inst_2034_,
                                v_inst_2035_,
                                v_val_2040_,
                                v___x_2146_,
                            );
                            v___x_2148_ = leanh::lean_apply_4(
                                v_toBind_2028_,
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v___x_2147_,
                                v___f_2103_,
                            );
                            return v___x_2148_;
                        } else {
                            v_s_2149_ = l_Lean_Syntax_getArg(v___x_2143_, v___x_2025_);
                            leanh::lean_dec(v___x_2143_);
                            v___x_2150_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2150_, 0, v_s_2149_);
                            v_s_2125_ = v___x_2150_;
                            state = 8;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_2143_);
                        leanh::lean_dec(v___x_2036_);
                        v___x_2151_ = leanh::lean_box(0);
                        v_s_2125_ = v___x_2151_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2065_ = leanh::lean_box(0);
                v___x_2066_ = leanh::lean_apply_2(
                    v_toPure_2026_,
                    leanh::lean_box(0),
                    v___x_2065_,
                );
                v___x_2067_ = leanh::lean_apply_4(
                    v_toBind_2028_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2066_,
                    v___f_2063_,
                );
                return v___x_2067_;
            }
            3 => {
                v___x_2077_ = leanh::lean_box(0);
                v___x_2078_ = leanh::lean_apply_2(
                    v_toPure_2026_,
                    leanh::lean_box(0),
                    v___x_2077_,
                );
                v___x_2079_ = leanh::lean_apply_4(
                    v_toBind_2028_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2078_,
                    v___f_2075_,
                );
                return v___x_2079_;
            }
            4 => {
                v___x_2089_ = leanh::lean_box(0);
                v___x_2090_ = leanh::lean_apply_2(
                    v_toPure_2026_,
                    leanh::lean_box(0),
                    v___x_2089_,
                );
                v___x_2091_ = leanh::lean_apply_4(
                    v_toBind_2028_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2090_,
                    v___f_2087_,
                );
                return v___x_2091_;
            }
            5 => {
                v___x_2109_ = leanh::lean_alloc_ctor(0, 3, (2) as u32);
                leanh::lean_ctor_set(v___x_2109_, 0, v_val_2040_);
                leanh::lean_ctor_set(v___x_2109_, 1, v___y_2105_);
                leanh::lean_ctor_set(v___x_2109_, 2, v___y_2106_);
                leanh::lean_ctor_set_uint8(
                    v___x_2109_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___y_2108_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2109_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                    v___y_2107_,
                );
                if v_isShared_2043_ == 0 {
                    leanh::lean_ctor_set(v___x_2042_, 0, v___x_2109_);
                    v___x_2111_ = v___x_2042_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2114_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2109_);
                    v___x_2111_ = v_reuseFailAlloc_2114_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2112_ = leanh::lean_apply_2(
                    v_toPure_2026_,
                    leanh::lean_box(0),
                    v___x_2111_,
                );
                v___x_2113_ = leanh::lean_apply_4(
                    v_toBind_2028_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2112_,
                    v___f_2103_,
                );
                return v___x_2113_;
            }
            7 => {
                v___x_2119_ = lean_mk_empty_array_with_capacity(v___x_2025_);
                leanh::lean_dec(v___x_2025_);
                v___x_2120_ = leanh::lean_alloc_ctor(0, 3, (2) as u32);
                leanh::lean_ctor_set(v___x_2120_, 0, v_val_2040_);
                leanh::lean_ctor_set(v___x_2120_, 1, v___x_2119_);
                leanh::lean_ctor_set(v___x_2120_, 2, v___y_2116_);
                leanh::lean_ctor_set_uint8(
                    v___x_2120_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___y_2118_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2120_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                    v___y_2117_,
                );
                v___x_2121_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2121_, 0, v___x_2120_);
                v___x_2122_ = leanh::lean_apply_2(
                    v_toPure_2026_,
                    leanh::lean_box(0),
                    v___x_2121_,
                );
                v___x_2123_ = leanh::lean_apply_4(
                    v_toBind_2028_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2122_,
                    v___f_2103_,
                );
                return v___x_2123_;
            }
            8 => {
                v___x_2126_ = leanh::lean_unsigned_to_nat(2);
                v___x_2127_ = l_Lean_Syntax_getArg(v_val_2040_, v___x_2126_);
                leanh::lean_inc(v___x_2127_);
                v___x_2128_ = l_Lean_Syntax_matchesNull(v___x_2127_, v___x_2126_);
                if v___x_2128_ == 0 {
                    leanh::lean_del_object(v___x_2042_);
                    v___x_2129_ = l_Lean_Syntax_matchesNull(v___x_2127_, v___x_2025_);
                    if v___x_2129_ == 0 {
                        leanh::lean_dec(v_s_2125_);
                        leanh::lean_dec(v_toPure_2026_);
                        leanh::lean_dec(v___x_2025_);
                        v___x_2130_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3_once), _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__3);
                        v___x_2131_ = l_Lean_throwErrorAt___redArg(
                            v_inst_2034_,
                            v_inst_2035_,
                            v_val_2040_,
                            v___x_2130_,
                        );
                        v___x_2132_ = leanh::lean_apply_4(
                            v_toBind_2028_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_2131_,
                            v___f_2103_,
                        );
                        return v___x_2132_;
                    } else {
                        leanh::lean_dec_ref(v_inst_2035_);
                        leanh::lean_dec_ref(v_inst_2034_);
                        v___x_2133_ = leanh::lean_unsigned_to_nat(3);
                        v_body_2134_ = l_Lean_Syntax_getArg(v_val_2040_, v___x_2133_);
                        if leanh::lean_obj_tag(v_s_2125_) == 0 {
                            v___y_2116_ = v_body_2134_;
                            v___y_2117_ = v___x_2128_;
                            v___y_2118_ = v___x_2128_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_dec_ref_known(v_s_2125_, 1);
                            v___y_2116_ = v_body_2134_;
                            v___y_2117_ = v___x_2128_;
                            v___y_2118_ = v___x_2129_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v___x_2135_ = l_Lean_Syntax_getArg(v___x_2127_, v___x_2025_);
                    leanh::lean_dec(v___x_2127_);
                    leanh::lean_inc(v___x_2135_);
                    v___x_2136_ = l_Lean_Syntax_matchesNull(v___x_2135_, v___x_2025_);
                    leanh::lean_dec(v___x_2025_);
                    if v___x_2136_ == 0 {
                        leanh::lean_dec_ref(v_inst_2035_);
                        leanh::lean_dec_ref(v_inst_2034_);
                        v___x_2137_ = leanh::lean_unsigned_to_nat(3);
                        v_body_2138_ = l_Lean_Syntax_getArg(v_val_2040_, v___x_2137_);
                        v_vars_2139_ = l_Lean_Syntax_getArgs(v___x_2135_);
                        leanh::lean_dec(v___x_2135_);
                        if leanh::lean_obj_tag(v_s_2125_) == 0 {
                            v___y_2105_ = v_vars_2139_;
                            v___y_2106_ = v_body_2138_;
                            v___y_2107_ = v___x_2136_;
                            v___y_2108_ = v___x_2136_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_dec_ref_known(v_s_2125_, 1);
                            v___y_2105_ = v_vars_2139_;
                            v___y_2106_ = v_body_2138_;
                            v___y_2107_ = v___x_2136_;
                            v___y_2108_ = v___x_2128_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_2135_);
                        leanh::lean_dec(v_s_2125_);
                        leanh::lean_del_object(v___x_2042_);
                        leanh::lean_dec(v_toPure_2026_);
                        v___x_2140_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5_once), _init_l_Lean_Elab_elabTerminationHints___redArg___lam__19___closed__5);
                        v___x_2141_ = l_Lean_throwErrorAt___redArg(
                            v_inst_2034_,
                            v_inst_2035_,
                            v_val_2040_,
                            v___x_2140_,
                        );
                        v___x_2142_ = leanh::lean_apply_4(
                            v_toBind_2028_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
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
    mut v___f_2157_: *mut leanh::LeanObject,
    mut v_terminationBy_x3f_x3f_2158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2159_ = leanh::lean_apply_1(v___f_2157_, v_terminationBy_x3f_x3f_2158_);
    return v___x_2159_;
}
pub unsafe fn l_Lean_Elab_elabTerminationHints___redArg(
    mut v_inst_2182_: *mut leanh::LeanObject,
    mut v_inst_2183_: *mut leanh::LeanObject,
    mut v_stx_2184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: u8 = 0;
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: u8 = 0;
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_x3f_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2226_: u8 = 0;
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: u8 = 0;
    let mut v___f_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2239_: u8 = 0;
    let mut v___f_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_x3f_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: u8 = 0;
    let mut v___x_2249_: u8 = 0;
    let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_x3f_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: u8 = 0;
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: u8 = 0;
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: u8 = 0;
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_x3f_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_stx_2184_) == 0 {
                    v_toApplicative_2185_ = leanh::lean_ctor_get(v_inst_2182_, 0);
                    leanh::lean_inc_ref(v_toApplicative_2185_);
                    leanh::lean_dec_ref(v_inst_2183_);
                    leanh::lean_dec_ref(v_inst_2182_);
                    v_toPure_2186_ = leanh::lean_ctor_get(v_toApplicative_2185_, 1);
                    leanh::lean_inc(v_toPure_2186_);
                    leanh::lean_dec_ref(v_toApplicative_2185_);
                    v___x_2187_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2188_ = leanh::lean_box(0);
                    v___x_2189_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v___x_2189_, 0, v_stx_2184_);
                    leanh::lean_ctor_set(v___x_2189_, 1, v___x_2188_);
                    leanh::lean_ctor_set(v___x_2189_, 2, v___x_2188_);
                    leanh::lean_ctor_set(v___x_2189_, 3, v___x_2188_);
                    leanh::lean_ctor_set(v___x_2189_, 4, v___x_2188_);
                    leanh::lean_ctor_set(v___x_2189_, 5, v___x_2187_);
                    v___x_2190_ = leanh::lean_apply_2(
                        v_toPure_2186_,
                        leanh::lean_box(0),
                        v___x_2189_,
                    );
                    return v___x_2190_;
                } else {
                    v_toApplicative_2191_ = leanh::lean_ctor_get(v_inst_2182_, 0);
                    v_toBind_2192_ = leanh::lean_ctor_get(v_inst_2182_, 1);
                    v_toFunctor_2193_ = leanh::lean_ctor_get(v_toApplicative_2191_, 0);
                    v_toPure_2194_ = leanh::lean_ctor_get(v_toApplicative_2191_, 1);
                    v___x_2195_ = l_Lean_Elab_elabTerminationHints___redArg___closed__0;
                    v___x_2196_ = l_Lean_Elab_elabTerminationHints___redArg___closed__1;
                    v___x_2197_ = l_Lean_Elab_elabTerminationHints___redArg___closed__2;
                    v___x_2198_ = l_Lean_Elab_elabTerminationHints___redArg___closed__4;
                    leanh::lean_inc(v_stx_2184_);
                    v___x_2199_ = l_Lean_Syntax_isOfKind(v_stx_2184_, v___x_2198_);
                    if v___x_2199_ == 0 {
                        v___x_2200_ = l_Lean_Elab_elabTerminationHints___redArg___closed__5;
                        v___x_2201_ = leanh::lean_box(0);
                        leanh::lean_inc_n(v_stx_2184_, 2);
                        v___x_2202_ =
                            l_Lean_Syntax_formatStx(v_stx_2184_, v___x_2201_, v___x_2199_);
                        v___x_2203_ = l_Std_Format_defWidth;
                        v___x_2204_ = leanh::lean_unsigned_to_nat(0);
                        v___x_2205_ =
                            l_Std_Format_pretty(v___x_2202_, v___x_2203_, v___x_2204_, v___x_2204_);
                        v___x_2206_ = lean_string_append(v___x_2200_, v___x_2205_);
                        leanh::lean_dec_ref(v___x_2205_);
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
                        leanh::lean_dec_ref(v___x_2211_);
                        v___x_2213_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2213_, 0, v___x_2212_);
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
                        v___x_2217_ = leanh::lean_unsigned_to_nat(0);
                        v___x_2283_ = l_Lean_Syntax_getArg(v_stx_2184_, v___x_2217_);
                        v___x_2284_ = l_Lean_Syntax_isNone(v___x_2283_);
                        if v___x_2284_ == 0 {
                            v___x_2285_ = leanh::lean_unsigned_to_nat(1);
                            leanh::lean_inc(v___x_2283_);
                            v___x_2286_ = l_Lean_Syntax_matchesNull(v___x_2283_, v___x_2285_);
                            if v___x_2286_ == 0 {
                                leanh::lean_dec(v___x_2283_);
                                v___x_2287_ = l_Lean_Elab_elabTerminationHints___redArg___closed__5;
                                v___x_2288_ = leanh::lean_box(0);
                                leanh::lean_inc_n(v_stx_2184_, 2);
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
                                leanh::lean_dec_ref(v___x_2291_);
                                v___x_2293_ = l_Lean_Elab_elabTerminationHints___redArg___closed__6;
                                v___x_2294_ = lean_string_append(v___x_2292_, v___x_2293_);
                                v___x_2295_ = l_Lean_Syntax_getKind(v_stx_2184_);
                                v___x_2296_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2295_, v___x_2199_);
                                v___x_2297_ = lean_string_append(v___x_2294_, v___x_2296_);
                                leanh::lean_dec_ref(v___x_2296_);
                                v___x_2298_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_2298_, 0, v___x_2297_);
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
                                leanh::lean_dec(v___x_2283_);
                                v___x_2302_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_2302_, 0, v_t_x3f_2301_);
                                v_t_x3f_2245_ = v___x_2302_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_2283_);
                            v___x_2303_ = leanh::lean_box(0);
                            v_t_x3f_2245_ = v___x_2303_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc(v___y_2219_);
                leanh::lean_inc(v_toBind_2192_);
                leanh::lean_inc(v_toPure_2194_);
                v___f_2222_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_elabTerminationHints___redArg___lam__19 as *mut core::ffi::c_void,
                    15,
                    14,
                );
                leanh::lean_closure_set(v___f_2222_, 0, v_stx_2184_);
                leanh::lean_closure_set(v___f_2222_, 1, v___x_2217_);
                leanh::lean_closure_set(v___f_2222_, 2, v_toPure_2194_);
                leanh::lean_closure_set(v___f_2222_, 3, v_d_x3f_2221_);
                leanh::lean_closure_set(v___f_2222_, 4, v_toBind_2192_);
                leanh::lean_closure_set(v___f_2222_, 5, v_toFunctor_2193_);
                leanh::lean_closure_set(v___f_2222_, 6, v___f_2216_);
                leanh::lean_closure_set(v___f_2222_, 7, v___x_2195_);
                leanh::lean_closure_set(v___f_2222_, 8, v___x_2196_);
                leanh::lean_closure_set(v___f_2222_, 9, v___x_2197_);
                leanh::lean_closure_set(v___f_2222_, 10, v_inst_2182_);
                leanh::lean_closure_set(v___f_2222_, 11, v_inst_2183_);
                leanh::lean_closure_set(v___f_2222_, 12, v___y_2220_);
                leanh::lean_closure_set(v___f_2222_, 13, v___y_2219_);
                if leanh::lean_obj_tag(v___y_2219_) == 1 {
                    v_val_2223_ = leanh::lean_ctor_get(v___y_2219_, 0);
                    v_isSharedCheck_2239_ = (!leanh::lean_is_exclusive(v___y_2219_)) as u8;
                    if v_isSharedCheck_2239_ == 0 {
                        v___x_2225_ = v___y_2219_;
                        v_isShared_2226_ = v_isSharedCheck_2239_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2223_);
                        leanh::lean_dec(v___y_2219_);
                        v___x_2225_ = leanh::lean_box(0);
                        v_isShared_2226_ = v_isSharedCheck_2239_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_2219_);
                    v___f_2240_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_elabTerminationHints___redArg___lam__5
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_2240_, 0, v___f_2222_);
                    v___x_2241_ = leanh::lean_box(0);
                    v___x_2242_ = leanh::lean_apply_2(
                        v_toPure_2194_,
                        leanh::lean_box(0),
                        v___x_2241_,
                    );
                    v___x_2243_ = leanh::lean_apply_4(
                        v_toBind_2192_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2242_,
                        v___f_2240_,
                    );
                    return v___x_2243_;
                }
            }
            2 => {
                v___x_2227_ = l_Lean_Elab_elabTerminationHints___redArg___closed__8;
                leanh::lean_inc(v_val_2223_);
                v___x_2228_ = l_Lean_Syntax_isOfKind(v_val_2223_, v___x_2227_);
                if v___x_2228_ == 0 {
                    leanh::lean_del_object(v___x_2225_);
                    leanh::lean_dec(v_val_2223_);
                    v___f_2229_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_elabTerminationHints___redArg___lam__5
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_2229_, 0, v___f_2222_);
                    v___x_2230_ = leanh::lean_box(0);
                    v___x_2231_ = leanh::lean_apply_2(
                        v_toPure_2194_,
                        leanh::lean_box(0),
                        v___x_2230_,
                    );
                    v___x_2232_ = leanh::lean_apply_4(
                        v_toBind_2192_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2231_,
                        v___f_2229_,
                    );
                    return v___x_2232_;
                } else {
                    v___f_2233_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_elabTerminationHints___redArg___lam__5
                            as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_2233_, 0, v___f_2222_);
                    if v_isShared_2226_ == 0 {
                        v___x_2235_ = v___x_2225_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2238_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_val_2223_);
                        v___x_2235_ = v_reuseFailAlloc_2238_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2236_ = leanh::lean_apply_2(
                    v_toPure_2194_,
                    leanh::lean_box(0),
                    v___x_2235_,
                );
                v___x_2237_ = leanh::lean_apply_4(
                    v_toBind_2192_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2236_,
                    v___f_2233_,
                );
                return v___x_2237_;
            }
            4 => {
                v___x_2246_ = leanh::lean_unsigned_to_nat(1);
                v___x_2247_ = l_Lean_Syntax_getArg(v_stx_2184_, v___x_2246_);
                v___x_2248_ = l_Lean_Syntax_isNone(v___x_2247_);
                if v___x_2248_ == 0 {
                    leanh::lean_inc(v___x_2247_);
                    v___x_2249_ = l_Lean_Syntax_matchesNull(v___x_2247_, v___x_2246_);
                    if v___x_2249_ == 0 {
                        leanh::lean_dec(v___x_2247_);
                        leanh::lean_dec(v_t_x3f_2245_);
                        v___x_2250_ = l_Lean_Elab_elabTerminationHints___redArg___closed__5;
                        v___x_2251_ = leanh::lean_box(0);
                        leanh::lean_inc_n(v_stx_2184_, 2);
                        v___x_2252_ =
                            l_Lean_Syntax_formatStx(v_stx_2184_, v___x_2251_, v___x_2249_);
                        v___x_2253_ = l_Std_Format_defWidth;
                        v___x_2254_ =
                            l_Std_Format_pretty(v___x_2252_, v___x_2253_, v___x_2217_, v___x_2217_);
                        v___x_2255_ = lean_string_append(v___x_2250_, v___x_2254_);
                        leanh::lean_dec_ref(v___x_2254_);
                        v___x_2256_ = l_Lean_Elab_elabTerminationHints___redArg___closed__6;
                        v___x_2257_ = lean_string_append(v___x_2255_, v___x_2256_);
                        v___x_2258_ = l_Lean_Syntax_getKind(v_stx_2184_);
                        v___x_2259_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v___x_2258_,
                                v___x_2199_,
                            );
                        v___x_2260_ = lean_string_append(v___x_2257_, v___x_2259_);
                        leanh::lean_dec_ref(v___x_2259_);
                        v___x_2261_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2261_, 0, v___x_2260_);
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
                        leanh::lean_dec(v___x_2247_);
                        v___x_2265_ = l_Lean_Elab_elabTerminationHints___redArg___closed__9;
                        leanh::lean_inc(v_d_x3f_2264_);
                        v___x_2266_ = l_Lean_Syntax_isOfKind(v_d_x3f_2264_, v___x_2265_);
                        if v___x_2266_ == 0 {
                            leanh::lean_dec(v_d_x3f_2264_);
                            leanh::lean_dec(v_t_x3f_2245_);
                            v___x_2267_ = l_Lean_Elab_elabTerminationHints___redArg___closed__5;
                            v___x_2268_ = leanh::lean_box(0);
                            leanh::lean_inc_n(v_stx_2184_, 2);
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
                            leanh::lean_dec_ref(v___x_2271_);
                            v___x_2273_ = l_Lean_Elab_elabTerminationHints___redArg___closed__6;
                            v___x_2274_ = lean_string_append(v___x_2272_, v___x_2273_);
                            v___x_2275_ = l_Lean_Syntax_getKind(v_stx_2184_);
                            v___x_2276_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v___x_2275_,
                                    v___x_2249_,
                                );
                            v___x_2277_ = lean_string_append(v___x_2274_, v___x_2276_);
                            leanh::lean_dec_ref(v___x_2276_);
                            v___x_2278_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2278_, 0, v___x_2277_);
                            v___x_2279_ = l_Lean_MessageData_ofFormat(v___x_2278_);
                            v___x_2280_ = l_Lean_throwErrorAt___redArg(
                                v_inst_2182_,
                                v_inst_2183_,
                                v_stx_2184_,
                                v___x_2279_,
                            );
                            return v___x_2280_;
                        } else {
                            leanh::lean_inc(v_toPure_2194_);
                            leanh::lean_inc_ref(v_toFunctor_2193_);
                            leanh::lean_inc(v_toBind_2192_);
                            v___x_2281_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2281_, 0, v_d_x3f_2264_);
                            v___y_2219_ = v_t_x3f_2245_;
                            v___y_2220_ = v___x_2246_;
                            v_d_x3f_2221_ = v___x_2281_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_toPure_2194_);
                    leanh::lean_inc_ref(v_toFunctor_2193_);
                    leanh::lean_inc(v_toBind_2192_);
                    leanh::lean_dec(v___x_2247_);
                    v___x_2282_ = leanh::lean_box(0);
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
    mut v_m_2304_: *mut leanh::LeanObject,
    mut v_inst_2305_: *mut leanh::LeanObject,
    mut v_inst_2306_: *mut leanh::LeanObject,
    mut v_stx_2307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2308_ =
        l_Lean_Elab_elabTerminationHints___redArg(v_inst_2305_, v_inst_2306_, v_stx_2307_);
    return v___x_2308_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_TerminationHint(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Term(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Elab_instInhabitedPartialFixpointType_default =
        _init_l_Lean_Elab_instInhabitedPartialFixpointType_default();
    l_Lean_Elab_instInhabitedPartialFixpointType =
        _init_l_Lean_Elab_instInhabitedPartialFixpointType();
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_TerminationHint(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Parser_Term(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_PreDefinition_TerminationHint(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Term(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Term(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_TerminationHint(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_TerminationHint(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_TerminationHint(builtin);
}
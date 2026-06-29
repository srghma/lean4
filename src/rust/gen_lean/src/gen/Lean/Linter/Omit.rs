// Lean compiler output
// Module: Lean.Linter.Omit
// Imports: Lean.Elab.Command Lean.Linter.Util
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_find_x3f;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind,
    l_Lean_replaceRef,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_addLinter,
    l_Lean_Elab_Command_getRef___redArg, l_Lean_Elab_Command_getScope___redArg,
    runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Linter::Init::{
    l_Lean_Linter_getLinterValue, l_Lean_Linter_linterMessageTag, l_Lean_Linter_linterSetsExt,
};
use crate::r#gen::Lean::Linter::Util::{
    initialize_Lean_Linter_Util, runtime_initialize_Lean_Linter_Util,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_note,
    l_Lean_MessageData_ofName, l_Lean_MessageLog_add, l_Lean_instBEqMessageSeverity_beq,
    l_Lean_stringToMessageData,
};
use crate::ffi::{
    lean_mk_empty_array_with_capacity, lean_string_dec_eq,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [111, 109, 105, 116, 0]};
static mut l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5701751079888345786 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,1170131724013778820 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [101, 110, 97, 98, 108, 101, 32, 116, 104, 101, 32, 39, 97, 118, 111, 105, 100, 32, 111, 109, 105, 116, 39, 32, 108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8071394701935581384 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,6326339448686113589 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16012274839969563159 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_linter_omit: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_omit___lam__0___closed__0_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Linter_omit___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_omit___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_omit___lam__0___closed__1_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [67, 111, 109, 109, 97, 110, 100, 0],
    };
static mut l_Lean_Linter_omit___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_omit___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Linter_omit___lam__0___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_omit___lam__0___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_omit___lam__0___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_omit___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Linter_omit___lam__0___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Linter_omit___lam__0___closed__2_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_omit___lam__0___closed__1_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Linter_omit___lam__0___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_omit___lam__0___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,17954277902228494328 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Linter_omit___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_omit___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__0_value:
    crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 45,
    m_data: [
        84, 104, 105, 115, 32, 108, 105, 110, 116, 101, 114, 32, 99, 97, 110, 32, 98, 101, 32, 100,
        105, 115, 97, 98, 108, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111,
        112, 116, 105, 111, 110, 32, 0,
    ],
};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__2_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [32, 102, 97, 108, 115, 101, 96, 0],
};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_omit___lam__1___closed__0_value: crate::leanh::LeanStringObject<80> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 80,
        m_capacity: 80,
        m_length: 79,
        m_data: [
            96, 111, 109, 105, 116, 96, 32, 115, 104, 111, 117, 108, 100, 32, 98, 101, 32, 97, 118,
            111, 105, 100, 101, 100, 32, 105, 110, 32, 102, 97, 118, 111, 114, 32, 111, 102, 32,
            114, 101, 115, 116, 114, 117, 99, 116, 117, 114, 105, 110, 103, 32, 121, 111, 117, 114,
            32, 96, 118, 97, 114, 105, 97, 98, 108, 101, 96, 32, 100, 101, 99, 108, 97, 114, 97,
            116, 105, 111, 110, 115, 0,
        ],
    };
static mut l_Lean_Linter_omit___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_omit___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_omit___lam__1___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_omit___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_omit___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Linter_omit___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Linter_omit___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_omit___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_omit___closed__1_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Linter_omit___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [core::ptr::addr_of!(l_Lean_Linter_omit___closed__0_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Linter_omit___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_omit___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_Linter_omit___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_omit___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_omit___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8071394701935581384 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Linter_omit___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_omit___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,2874839555205088126 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Linter_omit___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_omit___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_omit___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Linter_omit___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Linter_omit___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Linter_omit___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_omit___closed__3_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_omit: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_omit___closed__3_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__spec__0(
    mut v_name_446_: *mut crate::leanh::LeanObject,
    mut v_decl_447_: *mut crate::leanh::LeanObject,
    mut v_ref_448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: u8 = 0;
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_459_: u8 = 0;
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_464_: u8 = 0;
    let mut v_unused_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_469_: u8 = 0;
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_450_ = crate::leanh::lean_ctor_get(v_decl_447_, 0);
                v_descr_451_ = crate::leanh::lean_ctor_get(v_decl_447_, 1);
                v_deprecation_x3f_452_ = crate::leanh::lean_ctor_get(v_decl_447_, 2);
                v___x_453_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_454_ = (crate::leanh::lean_unbox(v_defValue_450_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_453_, 0 as u32, v___x_454_);
                crate::leanh::lean_inc(v_deprecation_x3f_452_);
                crate::leanh::lean_inc_ref(v_descr_451_);
                crate::leanh::lean_inc_n(v_name_446_, 2);
                v___x_455_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_455_, 0, v_name_446_);
                crate::leanh::lean_ctor_set(v___x_455_, 1, v_ref_448_);
                crate::leanh::lean_ctor_set(v___x_455_, 2, v___x_453_);
                crate::leanh::lean_ctor_set(v___x_455_, 3, v_descr_451_);
                crate::leanh::lean_ctor_set(v___x_455_, 4, v_deprecation_x3f_452_);
                v___x_456_ = lean_register_option(v_name_446_, v___x_455_);
                if crate::leanh::lean_obj_tag(v___x_456_) == 0 {
                    v_isSharedCheck_464_ = (!crate::leanh::lean_is_exclusive(v___x_456_)) as u8;
                    if v_isSharedCheck_464_ == 0 {
                        v_unused_465_ = crate::leanh::lean_ctor_get(v___x_456_, 0);
                        crate::leanh::lean_dec(v_unused_465_);
                        v___x_458_ = v___x_456_;
                        v_isShared_459_ = v_isSharedCheck_464_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_456_);
                        v___x_458_ = crate::leanh::lean_box(0);
                        v_isShared_459_ = v_isSharedCheck_464_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_446_);
                    v_a_466_ = crate::leanh::lean_ctor_get(v___x_456_, 0);
                    v_isSharedCheck_473_ = (!crate::leanh::lean_is_exclusive(v___x_456_)) as u8;
                    if v_isSharedCheck_473_ == 0 {
                        v___x_468_ = v___x_456_;
                        v_isShared_469_ = v_isSharedCheck_473_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_466_);
                        crate::leanh::lean_dec(v___x_456_);
                        v___x_468_ = crate::leanh::lean_box(0);
                        v_isShared_469_ = v_isSharedCheck_473_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_450_);
                v___x_460_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_460_, 0, v_name_446_);
                crate::leanh::lean_ctor_set(v___x_460_, 1, v_defValue_450_);
                if v_isShared_459_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_458_, 0, v___x_460_);
                    v___x_462_ = v___x_458_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_463_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
                    v___x_462_ = v_reuseFailAlloc_463_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_462_;
            }
            3 => {
                if v_isShared_469_ == 0 {
                    v___x_471_ = v___x_468_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_472_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
                    v___x_471_ = v_reuseFailAlloc_472_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_471_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_474_: *mut crate::leanh::LeanObject,
    mut v_decl_475_: *mut crate::leanh::LeanObject,
    mut v_ref_476_: *mut crate::leanh::LeanObject,
    mut v_a_477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_478_ = l_Lean_Option_register___at___00__private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__spec__0(v_name_474_, v_decl_475_, v_ref_476_);
    crate::leanh::lean_dec_ref(v_decl_475_);
    return v_res_478_;
}
pub unsafe fn l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_498_ = l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_;
    v___x_499_ = l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_;
    v___x_500_ = l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_;
    v___x_501_ = l_Lean_Option_register___at___00__private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__spec__0(v___x_498_, v___x_499_, v___x_500_);
    return v___x_501_;
}
pub unsafe fn l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4____boxed(
    mut v_a_502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_503_ = l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_();
    return v_res_503_;
}
pub unsafe fn l_Lean_Linter_omit___lam__0(mut v_x_511_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: u8 = 0;
    v___x_512_ = l_Lean_Linter_omit___lam__0___closed__2;
    v___x_513_ = l_Lean_Syntax_isOfKind(v_x_511_, v___x_512_);
    return v___x_513_;
}
pub unsafe fn l_Lean_Linter_omit___lam__0___boxed(
    mut v_x_514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_515_: u8 = 0;
    let mut v_r_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_515_ = l_Lean_Linter_omit___lam__0(v_x_514_);
    v_r_516_ = crate::leanh::lean_box((v_res_515_) as usize);
    return v_r_516_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__5(
    mut v_opts_517_: *mut crate::leanh::LeanObject,
    mut v_opt_518_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_519_ = crate::leanh::lean_ctor_get(v_opt_518_, 0);
    v_defValue_520_ = crate::leanh::lean_ctor_get(v_opt_518_, 1);
    v_map_521_ = crate::leanh::lean_ctor_get(v_opts_517_, 0);
    v___x_522_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_521_,
            v_name_519_,
        );
    if crate::leanh::lean_obj_tag(v___x_522_) == 0 {
        let mut v___x_523_: u8 = 0;
        v___x_523_ = (crate::leanh::lean_unbox(v_defValue_520_) as u8);
        return v___x_523_;
    } else {
        let mut v_val_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_524_ = crate::leanh::lean_ctor_get(v___x_522_, 0);
        crate::leanh::lean_inc(v_val_524_);
        crate::leanh::lean_dec_ref_known(v___x_522_, 1);
        if crate::leanh::lean_obj_tag(v_val_524_) == 1 {
            let mut v_v_525_: u8 = 0;
            v_v_525_ = crate::leanh::lean_ctor_get_uint8(v_val_524_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_524_, 0);
            return v_v_525_;
        } else {
            let mut v___x_526_: u8 = 0;
            crate::leanh::lean_dec(v_val_524_);
            v___x_526_ = (crate::leanh::lean_unbox(v_defValue_520_) as u8);
            return v___x_526_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__5___boxed(
    mut v_opts_527_: *mut crate::leanh::LeanObject,
    mut v_opt_528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_529_: u8 = 0;
    let mut v_r_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_529_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__5(v_opts_527_, v_opt_528_);
    crate::leanh::lean_dec_ref(v_opt_528_);
    crate::leanh::lean_dec_ref(v_opts_527_);
    v_r_530_ = crate::leanh::lean_box((v_res_529_) as usize);
    return v_r_530_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_531_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_531_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_532_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
    v___x_533_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_533_, 0, v___x_532_);
    return v___x_533_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_534_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_535_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_536_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_536_, 0, v___x_535_);
    crate::leanh::lean_ctor_set(v___x_536_, 1, v___x_535_);
    crate::leanh::lean_ctor_set(v___x_536_, 2, v___x_535_);
    crate::leanh::lean_ctor_set(v___x_536_, 3, v___x_535_);
    crate::leanh::lean_ctor_set(v___x_536_, 4, v___x_534_);
    crate::leanh::lean_ctor_set(v___x_536_, 5, v___x_534_);
    crate::leanh::lean_ctor_set(v___x_536_, 6, v___x_534_);
    crate::leanh::lean_ctor_set(v___x_536_, 7, v___x_534_);
    crate::leanh::lean_ctor_set(v___x_536_, 8, v___x_534_);
    crate::leanh::lean_ctor_set(v___x_536_, 9, v___x_534_);
    return v___x_536_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_537_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_538_ = lean_mk_empty_array_with_capacity(v___x_537_);
    v___x_539_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_539_, 0, v___x_538_);
    return v___x_539_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_540_: usize = 0;
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_540_ = 5usize;
    v___x_541_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_542_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_543_ = lean_mk_empty_array_with_capacity(v___x_542_);
    v___x_544_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
    v___x_545_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_545_, 0, v___x_544_);
    crate::leanh::lean_ctor_set(v___x_545_, 1, v___x_543_);
    crate::leanh::lean_ctor_set(v___x_545_, 2, v___x_541_);
    crate::leanh::lean_ctor_set(v___x_545_, 3, v___x_541_);
    crate::leanh::lean_ctor_set_usize(v___x_545_, 4, v___x_540_);
    return v___x_545_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_546_ = crate::leanh::lean_box(1);
    v___x_547_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
    v___x_548_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_549_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_549_, 0, v___x_548_);
    crate::leanh::lean_ctor_set(v___x_549_, 1, v___x_547_);
    crate::leanh::lean_ctor_set(v___x_549_, 2, v___x_546_);
    return v___x_549_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_msgData_550_: *mut crate::leanh::LeanObject,
    mut v___y_551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_553_ = lean_st_ref_get(v___y_551_);
    v_env_554_ = crate::leanh::lean_ctor_get(v___x_553_, 0);
    crate::leanh::lean_inc_ref(v_env_554_);
    crate::leanh::lean_dec(v___x_553_);
    v___x_555_ = lean_st_ref_get(v___y_551_);
    v_scopes_556_ = crate::leanh::lean_ctor_get(v___x_555_, 2);
    crate::leanh::lean_inc(v_scopes_556_);
    crate::leanh::lean_dec(v___x_555_);
    v___x_557_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_558_ = l_List_head_x21___redArg(v___x_557_, v_scopes_556_);
    crate::leanh::lean_dec(v_scopes_556_);
    v_opts_559_ = crate::leanh::lean_ctor_get(v___x_558_, 1);
    crate::leanh::lean_inc_ref(v_opts_559_);
    crate::leanh::lean_dec(v___x_558_);
    v___x_560_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
    v___x_561_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
    v___x_562_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_562_, 0, v_env_554_);
    crate::leanh::lean_ctor_set(v___x_562_, 1, v___x_560_);
    crate::leanh::lean_ctor_set(v___x_562_, 2, v___x_561_);
    crate::leanh::lean_ctor_set(v___x_562_, 3, v_opts_559_);
    v___x_563_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_563_, 0, v___x_562_);
    crate::leanh::lean_ctor_set(v___x_563_, 1, v_msgData_550_);
    v___x_564_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_564_, 0, v___x_563_);
    return v___x_564_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_msgData_565_: *mut crate::leanh::LeanObject,
    mut v___y_566_: *mut crate::leanh::LeanObject,
    mut v___y_567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_568_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg(v_msgData_565_, v___y_566_);
    crate::leanh::lean_dec(v___y_566_);
    return v_res_568_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0(
    mut v___y_570_: u8,
    mut v_suppressElabErrors_571_: u8,
    mut v_x_572_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_572_) == 1 {
        let mut v_pre_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_573_ = crate::leanh::lean_ctor_get(v_x_572_, 0);
        if crate::leanh::lean_obj_tag(v_pre_573_) == 0 {
            let mut v_str_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_576_: u8 = 0;
            v_str_574_ = crate::leanh::lean_ctor_get(v_x_572_, 1);
            v___x_575_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0___closed__0;
            v___x_576_ = lean_string_dec_eq(v_str_574_, v___x_575_);
            if v___x_576_ == 0 {
                return v___y_570_;
            } else {
                return v_suppressElabErrors_571_;
            }
        } else {
            return v___y_570_;
        }
    } else {
        return v___y_570_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0___boxed(
    mut v___y_577_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_578_: *mut crate::leanh::LeanObject,
    mut v_x_579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3058__boxed_580_: u8 = 0;
    let mut v_suppressElabErrors_boxed_581_: u8 = 0;
    let mut v_res_582_: u8 = 0;
    let mut v_r_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_3058__boxed_580_ = (crate::leanh::lean_unbox(v___y_577_) as u8);
    v_suppressElabErrors_boxed_581_ = (crate::leanh::lean_unbox(v_suppressElabErrors_578_) as u8);
    v_res_582_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0(v___y_3058__boxed_580_, v_suppressElabErrors_boxed_581_, v_x_579_);
    crate::leanh::lean_dec(v_x_579_);
    v_r_583_ = crate::leanh::lean_box((v_res_582_) as usize);
    return v_r_583_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3(
    mut v_ref_585_: *mut crate::leanh::LeanObject,
    mut v_msgData_586_: *mut crate::leanh::LeanObject,
    mut v_severity_587_: u8,
    mut v_isSilent_588_: u8,
    mut v___y_589_: *mut crate::leanh::LeanObject,
    mut v___y_590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_593_: u8 = 0;
    let mut v___y_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_596_: u8 = 0;
    let mut v___y_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_607_: u8 = 0;
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_624_: u8 = 0;
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_637_: u8 = 0;
    let mut v_isSharedCheck_638_: u8 = 0;
    let mut v_a_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_642_: u8 = 0;
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_646_: u8 = 0;
    let mut v_a_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_650_: u8 = 0;
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_654_: u8 = 0;
    let mut v___y_656_: u8 = 0;
    let mut v___y_657_: u8 = 0;
    let mut v___y_658_: u8 = 0;
    let mut v___y_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_663_: u8 = 0;
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_669_: u8 = 0;
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: u8 = 0;
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_682_: u8 = 0;
    let mut v___y_684_: u8 = 0;
    let mut v___y_685_: u8 = 0;
    let mut v___y_686_: u8 = 0;
    let mut v___y_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_692_: u8 = 0;
    let mut v___y_693_: u8 = 0;
    let mut v___y_694_: u8 = 0;
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_704_: u8 = 0;
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_708_: u8 = 0;
    let mut v___x_709_: u8 = 0;
    let mut v___y_711_: u8 = 0;
    let mut v___y_712_: u8 = 0;
    let mut v___y_713_: u8 = 0;
    let mut v___y_715_: u8 = 0;
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: u8 = 0;
    let mut v___x_722_: u8 = 0;
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: u8 = 0;
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: u8 = 0;
    let mut v___x_728_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_709_ = 2;
                v___x_727_ = l_Lean_instBEqMessageSeverity_beq(v_severity_587_, v___x_709_);
                if v___x_727_ == 0 {
                    v___y_715_ = v___x_727_;
                    state = 18;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_586_);
                    v___x_728_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_586_);
                    v___y_715_ = v___x_728_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                v___x_601_ = l_Lean_Elab_Command_getScope___redArg(v___y_600_);
                if crate::leanh::lean_obj_tag(v___x_601_) == 0 {
                    v_a_602_ = crate::leanh::lean_ctor_get(v___x_601_, 0);
                    crate::leanh::lean_inc(v_a_602_);
                    crate::leanh::lean_dec_ref_known(v___x_601_, 1);
                    v___x_603_ = l_Lean_Elab_Command_getScope___redArg(v___y_600_);
                    if crate::leanh::lean_obj_tag(v___x_603_) == 0 {
                        v_a_604_ = crate::leanh::lean_ctor_get(v___x_603_, 0);
                        v_isSharedCheck_638_ = (!crate::leanh::lean_is_exclusive(v___x_603_)) as u8;
                        if v_isSharedCheck_638_ == 0 {
                            v___x_606_ = v___x_603_;
                            v_isShared_607_ = v_isSharedCheck_638_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_604_);
                            crate::leanh::lean_dec(v___x_603_);
                            v___x_606_ = crate::leanh::lean_box(0);
                            v_isShared_607_ = v_isSharedCheck_638_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_602_);
                        crate::leanh::lean_dec_ref(v___y_598_);
                        crate::leanh::lean_dec(v___y_595_);
                        crate::leanh::lean_dec_ref(v___y_594_);
                        v_a_639_ = crate::leanh::lean_ctor_get(v___x_603_, 0);
                        v_isSharedCheck_646_ = (!crate::leanh::lean_is_exclusive(v___x_603_)) as u8;
                        if v_isSharedCheck_646_ == 0 {
                            v___x_641_ = v___x_603_;
                            v_isShared_642_ = v_isSharedCheck_646_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_639_);
                            crate::leanh::lean_dec(v___x_603_);
                            v___x_641_ = crate::leanh::lean_box(0);
                            v_isShared_642_ = v_isSharedCheck_646_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_598_);
                    crate::leanh::lean_dec(v___y_595_);
                    crate::leanh::lean_dec_ref(v___y_594_);
                    v_a_647_ = crate::leanh::lean_ctor_get(v___x_601_, 0);
                    v_isSharedCheck_654_ = (!crate::leanh::lean_is_exclusive(v___x_601_)) as u8;
                    if v_isSharedCheck_654_ == 0 {
                        v___x_649_ = v___x_601_;
                        v_isShared_650_ = v_isSharedCheck_654_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_647_);
                        crate::leanh::lean_dec(v___x_601_);
                        v___x_649_ = crate::leanh::lean_box(0);
                        v_isShared_650_ = v_isSharedCheck_654_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_608_ = lean_st_ref_take(v___y_600_);
                v_currNamespace_609_ = crate::leanh::lean_ctor_get(v_a_602_, 2);
                crate::leanh::lean_inc(v_currNamespace_609_);
                crate::leanh::lean_dec(v_a_602_);
                v_openDecls_610_ = crate::leanh::lean_ctor_get(v_a_604_, 3);
                crate::leanh::lean_inc(v_openDecls_610_);
                crate::leanh::lean_dec(v_a_604_);
                v_env_611_ = crate::leanh::lean_ctor_get(v___x_608_, 0);
                v_messages_612_ = crate::leanh::lean_ctor_get(v___x_608_, 1);
                v_scopes_613_ = crate::leanh::lean_ctor_get(v___x_608_, 2);
                v_usedQuotCtxts_614_ = crate::leanh::lean_ctor_get(v___x_608_, 3);
                v_nextMacroScope_615_ = crate::leanh::lean_ctor_get(v___x_608_, 4);
                v_maxRecDepth_616_ = crate::leanh::lean_ctor_get(v___x_608_, 5);
                v_ngen_617_ = crate::leanh::lean_ctor_get(v___x_608_, 6);
                v_auxDeclNGen_618_ = crate::leanh::lean_ctor_get(v___x_608_, 7);
                v_infoState_619_ = crate::leanh::lean_ctor_get(v___x_608_, 8);
                v_traceState_620_ = crate::leanh::lean_ctor_get(v___x_608_, 9);
                v_snapshotTasks_621_ = crate::leanh::lean_ctor_get(v___x_608_, 10);
                v_isSharedCheck_637_ = (!crate::leanh::lean_is_exclusive(v___x_608_)) as u8;
                if v_isSharedCheck_637_ == 0 {
                    v___x_623_ = v___x_608_;
                    v_isShared_624_ = v_isSharedCheck_637_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_621_);
                    crate::leanh::lean_inc(v_traceState_620_);
                    crate::leanh::lean_inc(v_infoState_619_);
                    crate::leanh::lean_inc(v_auxDeclNGen_618_);
                    crate::leanh::lean_inc(v_ngen_617_);
                    crate::leanh::lean_inc(v_maxRecDepth_616_);
                    crate::leanh::lean_inc(v_nextMacroScope_615_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_614_);
                    crate::leanh::lean_inc(v_scopes_613_);
                    crate::leanh::lean_inc(v_messages_612_);
                    crate::leanh::lean_inc(v_env_611_);
                    crate::leanh::lean_dec(v___x_608_);
                    v___x_623_ = crate::leanh::lean_box(0);
                    v_isShared_624_ = v_isSharedCheck_637_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_625_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_625_, 0, v_currNamespace_609_);
                crate::leanh::lean_ctor_set(v___x_625_, 1, v_openDecls_610_);
                v___x_626_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_626_, 0, v___x_625_);
                crate::leanh::lean_ctor_set(v___x_626_, 1, v___y_594_);
                crate::leanh::lean_inc_ref(v___y_599_);
                crate::leanh::lean_inc_ref(v___y_597_);
                v___x_627_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_627_, 0, v___y_597_);
                crate::leanh::lean_ctor_set(v___x_627_, 1, v___y_598_);
                crate::leanh::lean_ctor_set(v___x_627_, 2, v___y_595_);
                crate::leanh::lean_ctor_set(v___x_627_, 3, v___y_599_);
                crate::leanh::lean_ctor_set(v___x_627_, 4, v___x_626_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_627_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_596_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_627_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_593_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_627_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_588_,
                );
                v___x_628_ = l_Lean_MessageLog_add(v___x_627_, v_messages_612_);
                if v_isShared_624_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_623_, 1, v___x_628_);
                    v___x_630_ = v___x_623_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_636_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_636_, 0, v_env_611_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_636_, 1, v___x_628_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_636_, 2, v_scopes_613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_636_, 3, v_usedQuotCtxts_614_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_636_, 4, v_nextMacroScope_615_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_636_, 5, v_maxRecDepth_616_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_636_, 6, v_ngen_617_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_636_, 7, v_auxDeclNGen_618_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_636_, 8, v_infoState_619_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_636_, 9, v_traceState_620_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_636_, 10, v_snapshotTasks_621_);
                    v___x_630_ = v_reuseFailAlloc_636_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_631_ = lean_st_ref_set(v___y_600_, v___x_630_);
                v___x_632_ = crate::leanh::lean_box(0);
                if v_isShared_607_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_606_, 0, v___x_632_);
                    v___x_634_ = v___x_606_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_635_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_632_);
                    v___x_634_ = v_reuseFailAlloc_635_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_634_;
            }
            6 => {
                if v_isShared_642_ == 0 {
                    v___x_644_ = v___x_641_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_645_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
                    v___x_644_ = v_reuseFailAlloc_645_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_644_;
            }
            8 => {
                if v_isShared_650_ == 0 {
                    v___x_652_ = v___x_649_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_653_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
                    v___x_652_ = v_reuseFailAlloc_653_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_652_;
            }
            10 => {
                v_fileName_661_ = crate::leanh::lean_ctor_get(v___y_589_, 0);
                v_fileMap_662_ = crate::leanh::lean_ctor_get(v___y_589_, 1);
                v_suppressElabErrors_663_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_589_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v___x_664_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_586_,
                    );
                v___x_665_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg(v___x_664_, v___y_590_);
                v_a_666_ = crate::leanh::lean_ctor_get(v___x_665_, 0);
                v_isSharedCheck_682_ = (!crate::leanh::lean_is_exclusive(v___x_665_)) as u8;
                if v_isSharedCheck_682_ == 0 {
                    v___x_668_ = v___x_665_;
                    v_isShared_669_ = v_isSharedCheck_682_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_666_);
                    crate::leanh::lean_dec(v___x_665_);
                    v___x_668_ = crate::leanh::lean_box(0);
                    v_isShared_669_ = v_isSharedCheck_682_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_inc_ref_n(v_fileMap_662_, 2);
                v___x_670_ = l_Lean_FileMap_toPosition(v_fileMap_662_, v___y_659_);
                crate::leanh::lean_dec(v___y_659_);
                v___x_671_ = l_Lean_FileMap_toPosition(v_fileMap_662_, v___y_660_);
                crate::leanh::lean_dec(v___y_660_);
                v___x_672_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_672_, 0, v___x_671_);
                v___x_673_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___closed__0;
                if v_suppressElabErrors_663_ == 0 {
                    crate::leanh::lean_del_object(v___x_668_);
                    v___y_593_ = v___y_657_;
                    v___y_594_ = v_a_666_;
                    v___y_595_ = v___x_672_;
                    v___y_596_ = v___y_658_;
                    v___y_597_ = v_fileName_661_;
                    v___y_598_ = v___x_670_;
                    v___y_599_ = v___x_673_;
                    v___y_600_ = v___y_590_;
                    state = 1;
                    continue;
                } else {
                    v___x_674_ = crate::leanh::lean_box((v___y_656_) as usize);
                    v___x_675_ = crate::leanh::lean_box((v_suppressElabErrors_663_) as usize);
                    v___f_676_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_676_, 0, v___x_674_);
                    crate::leanh::lean_closure_set(v___f_676_, 1, v___x_675_);
                    crate::leanh::lean_inc(v_a_666_);
                    v___x_677_ = l_Lean_MessageData_hasTag(v___f_676_, v_a_666_);
                    if v___x_677_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_672_, 1);
                        crate::leanh::lean_dec_ref(v___x_670_);
                        crate::leanh::lean_dec(v_a_666_);
                        v___x_678_ = crate::leanh::lean_box(0);
                        if v_isShared_669_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_668_, 0, v___x_678_);
                            v___x_680_ = v___x_668_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_681_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_678_);
                            v___x_680_ = v_reuseFailAlloc_681_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_668_);
                        v___y_593_ = v___y_657_;
                        v___y_594_ = v_a_666_;
                        v___y_595_ = v___x_672_;
                        v___y_596_ = v___y_658_;
                        v___y_597_ = v_fileName_661_;
                        v___y_598_ = v___x_670_;
                        v___y_599_ = v___x_673_;
                        v___y_600_ = v___y_590_;
                        state = 1;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_680_;
            }
            13 => {
                v___x_689_ = l_Lean_Syntax_getTailPos_x3f(v___y_687_, v___y_686_);
                crate::leanh::lean_dec(v___y_687_);
                if crate::leanh::lean_obj_tag(v___x_689_) == 0 {
                    crate::leanh::lean_inc(v___y_688_);
                    v___y_656_ = v___y_684_;
                    v___y_657_ = v___y_685_;
                    v___y_658_ = v___y_686_;
                    v___y_659_ = v___y_688_;
                    v___y_660_ = v___y_688_;
                    state = 10;
                    continue;
                } else {
                    v_val_690_ = crate::leanh::lean_ctor_get(v___x_689_, 0);
                    crate::leanh::lean_inc(v_val_690_);
                    crate::leanh::lean_dec_ref_known(v___x_689_, 1);
                    v___y_656_ = v___y_684_;
                    v___y_657_ = v___y_685_;
                    v___y_658_ = v___y_686_;
                    v___y_659_ = v___y_688_;
                    v___y_660_ = v_val_690_;
                    state = 10;
                    continue;
                }
            }
            14 => {
                v___x_695_ = l_Lean_Elab_Command_getRef___redArg(v___y_589_);
                if crate::leanh::lean_obj_tag(v___x_695_) == 0 {
                    v_a_696_ = crate::leanh::lean_ctor_get(v___x_695_, 0);
                    crate::leanh::lean_inc(v_a_696_);
                    crate::leanh::lean_dec_ref_known(v___x_695_, 1);
                    v_ref_697_ = l_Lean_replaceRef(v_ref_585_, v_a_696_);
                    crate::leanh::lean_dec(v_a_696_);
                    v___x_698_ = l_Lean_Syntax_getPos_x3f(v_ref_697_, v___y_693_);
                    if crate::leanh::lean_obj_tag(v___x_698_) == 0 {
                        v___x_699_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___y_684_ = v___y_692_;
                        v___y_685_ = v___y_694_;
                        v___y_686_ = v___y_693_;
                        v___y_687_ = v_ref_697_;
                        v___y_688_ = v___x_699_;
                        state = 13;
                        continue;
                    } else {
                        v_val_700_ = crate::leanh::lean_ctor_get(v___x_698_, 0);
                        crate::leanh::lean_inc(v_val_700_);
                        crate::leanh::lean_dec_ref_known(v___x_698_, 1);
                        v___y_684_ = v___y_692_;
                        v___y_685_ = v___y_694_;
                        v___y_686_ = v___y_693_;
                        v___y_687_ = v_ref_697_;
                        v___y_688_ = v_val_700_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_586_);
                    v_a_701_ = crate::leanh::lean_ctor_get(v___x_695_, 0);
                    v_isSharedCheck_708_ = (!crate::leanh::lean_is_exclusive(v___x_695_)) as u8;
                    if v_isSharedCheck_708_ == 0 {
                        v___x_703_ = v___x_695_;
                        v_isShared_704_ = v_isSharedCheck_708_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_701_);
                        crate::leanh::lean_dec(v___x_695_);
                        v___x_703_ = crate::leanh::lean_box(0);
                        v_isShared_704_ = v_isSharedCheck_708_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_704_ == 0 {
                    v___x_706_ = v___x_703_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_707_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
                    v___x_706_ = v_reuseFailAlloc_707_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_706_;
            }
            17 => {
                if v___y_713_ == 0 {
                    v___y_692_ = v___y_711_;
                    v___y_693_ = v___y_712_;
                    v___y_694_ = v_severity_587_;
                    state = 14;
                    continue;
                } else {
                    v___y_692_ = v___y_711_;
                    v___y_693_ = v___y_712_;
                    v___y_694_ = v___x_709_;
                    state = 14;
                    continue;
                }
            }
            18 => {
                if v___y_715_ == 0 {
                    v___x_716_ = lean_st_ref_get(v___y_590_);
                    v_scopes_717_ = crate::leanh::lean_ctor_get(v___x_716_, 2);
                    crate::leanh::lean_inc(v_scopes_717_);
                    crate::leanh::lean_dec(v___x_716_);
                    v___x_718_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_719_ = l_List_head_x21___redArg(v___x_718_, v_scopes_717_);
                    crate::leanh::lean_dec(v_scopes_717_);
                    v_opts_720_ = crate::leanh::lean_ctor_get(v___x_719_, 1);
                    crate::leanh::lean_inc_ref(v_opts_720_);
                    crate::leanh::lean_dec(v___x_719_);
                    v___x_721_ = 1;
                    v___x_722_ = l_Lean_instBEqMessageSeverity_beq(v_severity_587_, v___x_721_);
                    if v___x_722_ == 0 {
                        crate::leanh::lean_dec_ref(v_opts_720_);
                        v___y_711_ = v___y_715_;
                        v___y_712_ = v___y_715_;
                        v___y_713_ = v___x_722_;
                        state = 17;
                        continue;
                    } else {
                        v___x_723_ = l_Lean_warningAsError;
                        v___x_724_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__5(v_opts_720_, v___x_723_);
                        crate::leanh::lean_dec_ref(v_opts_720_);
                        v___y_711_ = v___y_715_;
                        v___y_712_ = v___y_715_;
                        v___y_713_ = v___x_724_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_586_);
                    v___x_725_ = crate::leanh::lean_box(0);
                    v___x_726_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_726_, 0, v___x_725_);
                    return v___x_726_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___boxed(
    mut v_ref_729_: *mut crate::leanh::LeanObject,
    mut v_msgData_730_: *mut crate::leanh::LeanObject,
    mut v_severity_731_: *mut crate::leanh::LeanObject,
    mut v_isSilent_732_: *mut crate::leanh::LeanObject,
    mut v___y_733_: *mut crate::leanh::LeanObject,
    mut v___y_734_: *mut crate::leanh::LeanObject,
    mut v___y_735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_736_: u8 = 0;
    let mut v_isSilent_boxed_737_: u8 = 0;
    let mut v_res_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_736_ = (crate::leanh::lean_unbox(v_severity_731_) as u8);
    v_isSilent_boxed_737_ = (crate::leanh::lean_unbox(v_isSilent_732_) as u8);
    v_res_738_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3(v_ref_729_, v_msgData_730_, v_severity_boxed_736_, v_isSilent_boxed_737_, v___y_733_, v___y_734_);
    crate::leanh::lean_dec(v___y_734_);
    crate::leanh::lean_dec_ref(v___y_733_);
    crate::leanh::lean_dec(v_ref_729_);
    return v_res_738_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2(
    mut v_ref_739_: *mut crate::leanh::LeanObject,
    mut v_msgData_740_: *mut crate::leanh::LeanObject,
    mut v___y_741_: *mut crate::leanh::LeanObject,
    mut v___y_742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_744_: u8 = 0;
    let mut v___x_745_: u8 = 0;
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_744_ = 1;
    v___x_745_ = 0;
    v___x_746_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3(v_ref_739_, v_msgData_740_, v___x_744_, v___x_745_, v___y_741_, v___y_742_);
    return v___x_746_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2___boxed(
    mut v_ref_747_: *mut crate::leanh::LeanObject,
    mut v_msgData_748_: *mut crate::leanh::LeanObject,
    mut v___y_749_: *mut crate::leanh::LeanObject,
    mut v___y_750_: *mut crate::leanh::LeanObject,
    mut v___y_751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_752_ =
        l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2(
            v_ref_747_,
            v_msgData_748_,
            v___y_749_,
            v___y_750_,
        );
    crate::leanh::lean_dec(v___y_750_);
    crate::leanh::lean_dec_ref(v___y_749_);
    crate::leanh::lean_dec(v_ref_747_);
    return v_res_752_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_754_ = l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__0;
    v___x_755_ = l_Lean_stringToMessageData(v___x_754_);
    return v___x_755_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_757_ = l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__2;
    v___x_758_ = l_Lean_stringToMessageData(v___x_757_);
    return v___x_758_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1(
    mut v_linterOption_759_: *mut crate::leanh::LeanObject,
    mut v_stx_760_: *mut crate::leanh::LeanObject,
    mut v_msg_761_: *mut crate::leanh::LeanObject,
    mut v___y_762_: *mut crate::leanh::LeanObject,
    mut v___y_763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_768_: u8 = 0;
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_disable_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_782_: u8 = 0;
    let mut v_unused_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_765_ = crate::leanh::lean_ctor_get(v_linterOption_759_, 0);
                v_isSharedCheck_782_ =
                    (!crate::leanh::lean_is_exclusive(v_linterOption_759_)) as u8;
                if v_isSharedCheck_782_ == 0 {
                    v_unused_783_ = crate::leanh::lean_ctor_get(v_linterOption_759_, 1);
                    crate::leanh::lean_dec(v_unused_783_);
                    v___x_767_ = v_linterOption_759_;
                    v_isShared_768_ = v_isSharedCheck_782_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_765_);
                    crate::leanh::lean_dec(v_linterOption_759_);
                    v___x_767_ = crate::leanh::lean_box(0);
                    v_isShared_768_ = v_isSharedCheck_782_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_769_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1_once
                    ),
                    _init_l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1,
                );
                crate::leanh::lean_inc(v_name_765_);
                v___x_770_ = l_Lean_MessageData_ofName(v_name_765_);
                if v_isShared_768_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_767_, 7);
                    crate::leanh::lean_ctor_set(v___x_767_, 1, v___x_770_);
                    crate::leanh::lean_ctor_set(v___x_767_, 0, v___x_769_);
                    v___x_772_ = v___x_767_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_781_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_781_, 1, v___x_770_);
                    v___x_772_ = v_reuseFailAlloc_781_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_773_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3_once
                    ),
                    _init_l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3,
                );
                v___x_774_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_774_, 0, v___x_772_);
                crate::leanh::lean_ctor_set(v___x_774_, 1, v___x_773_);
                v_disable_775_ = l_Lean_MessageData_note(v___x_774_);
                v___x_776_ = l_Lean_Linter_linterMessageTag;
                v___x_777_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_777_, 0, v_msg_761_);
                crate::leanh::lean_ctor_set(v___x_777_, 1, v_disable_775_);
                v___x_778_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_778_, 0, v___x_776_);
                crate::leanh::lean_ctor_set(v___x_778_, 1, v___x_777_);
                v___x_779_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_779_, 0, v_name_765_);
                crate::leanh::lean_ctor_set(v___x_779_, 1, v___x_778_);
                v___x_780_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2(v_stx_760_, v___x_779_, v___y_762_, v___y_763_);
                return v___x_780_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___boxed(
    mut v_linterOption_784_: *mut crate::leanh::LeanObject,
    mut v_stx_785_: *mut crate::leanh::LeanObject,
    mut v_msg_786_: *mut crate::leanh::LeanObject,
    mut v___y_787_: *mut crate::leanh::LeanObject,
    mut v___y_788_: *mut crate::leanh::LeanObject,
    mut v___y_789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_790_ = l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1(
        v_linterOption_784_,
        v_stx_785_,
        v_msg_786_,
        v___y_787_,
        v___y_788_,
    );
    crate::leanh::lean_dec(v___y_788_);
    crate::leanh::lean_dec_ref(v___y_787_);
    crate::leanh::lean_dec(v_stx_785_);
    return v_res_790_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg(
    mut v_o_791_: *mut crate::leanh::LeanObject,
    mut v___y_792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_linterSets_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_794_ = lean_st_ref_get(v___y_792_);
    v_env_795_ = crate::leanh::lean_ctor_get(v___x_794_, 0);
    crate::leanh::lean_inc_ref(v_env_795_);
    crate::leanh::lean_dec(v___x_794_);
    v___x_796_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_797_ = crate::leanh::lean_ctor_get(v___x_796_, 0);
    v_asyncMode_798_ = crate::leanh::lean_ctor_get(v_toEnvExtension_797_, 2);
    v___x_799_ = crate::leanh::lean_box(1);
    v___x_800_ = crate::leanh::lean_box(0);
    v_linterSets_801_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_799_,
        v___x_796_,
        v_env_795_,
        v_asyncMode_798_,
        v___x_800_,
    );
    v___x_802_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_802_, 0, v_o_791_);
    crate::leanh::lean_ctor_set(v___x_802_, 1, v_linterSets_801_);
    v___x_803_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_803_, 0, v___x_802_);
    return v___x_803_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg___boxed(
    mut v_o_804_: *mut crate::leanh::LeanObject,
    mut v___y_805_: *mut crate::leanh::LeanObject,
    mut v___y_806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_807_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg(v_o_804_, v___y_805_);
    crate::leanh::lean_dec(v___y_805_);
    return v_res_807_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0(
    mut v___y_808_: *mut crate::leanh::LeanObject,
    mut v___y_809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_811_ = lean_st_ref_get(v___y_809_);
    v_scopes_812_ = crate::leanh::lean_ctor_get(v___x_811_, 2);
    crate::leanh::lean_inc(v_scopes_812_);
    crate::leanh::lean_dec(v___x_811_);
    v___x_813_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_814_ = l_List_head_x21___redArg(v___x_813_, v_scopes_812_);
    crate::leanh::lean_dec(v_scopes_812_);
    v_opts_815_ = crate::leanh::lean_ctor_get(v___x_814_, 1);
    crate::leanh::lean_inc_ref(v_opts_815_);
    crate::leanh::lean_dec(v___x_814_);
    v___x_816_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg(v_opts_815_, v___y_809_);
    return v___x_816_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0___boxed(
    mut v___y_817_: *mut crate::leanh::LeanObject,
    mut v___y_818_: *mut crate::leanh::LeanObject,
    mut v___y_819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_820_ =
        l_Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0(v___y_817_, v___y_818_);
    crate::leanh::lean_dec(v___y_818_);
    crate::leanh::lean_dec_ref(v___y_817_);
    return v_res_820_;
}
pub unsafe fn _init_l_Lean_Linter_omit___lam__1___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_822_ = l_Lean_Linter_omit___lam__1___closed__0;
    v___x_823_ = l_Lean_stringToMessageData(v___x_822_);
    return v___x_823_;
}
pub unsafe fn l_Lean_Linter_omit___lam__1(
    mut v___f_824_: *mut crate::leanh::LeanObject,
    mut v_stx_825_: *mut crate::leanh::LeanObject,
    mut v___y_826_: *mut crate::leanh::LeanObject,
    mut v___y_827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_833_: u8 = 0;
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: u8 = 0;
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_848_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_829_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0(
                    v___y_826_, v___y_827_,
                );
                v_a_830_ = crate::leanh::lean_ctor_get(v___x_829_, 0);
                v_isSharedCheck_848_ = (!crate::leanh::lean_is_exclusive(v___x_829_)) as u8;
                if v_isSharedCheck_848_ == 0 {
                    v___x_832_ = v___x_829_;
                    v_isShared_833_ = v_isSharedCheck_848_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_830_);
                    crate::leanh::lean_dec(v___x_829_);
                    v___x_832_ = crate::leanh::lean_box(0);
                    v_isShared_833_ = v_isSharedCheck_848_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_834_ = l_Lean_Linter_linter_omit;
                v___x_835_ = l_Lean_Linter_getLinterValue(v___x_834_, v_a_830_);
                crate::leanh::lean_dec(v_a_830_);
                if v___x_835_ == 0 {
                    crate::leanh::lean_dec(v_stx_825_);
                    crate::leanh::lean_dec_ref(v___f_824_);
                    v___x_836_ = crate::leanh::lean_box(0);
                    if v_isShared_833_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_832_, 0, v___x_836_);
                        v___x_838_ = v___x_832_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_839_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
                        v___x_838_ = v_reuseFailAlloc_839_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_840_ = l_Lean_Syntax_find_x3f(v_stx_825_, v___f_824_);
                    if crate::leanh::lean_obj_tag(v___x_840_) == 1 {
                        crate::leanh::lean_del_object(v___x_832_);
                        v_val_841_ = crate::leanh::lean_ctor_get(v___x_840_, 0);
                        crate::leanh::lean_inc(v_val_841_);
                        crate::leanh::lean_dec_ref_known(v___x_840_, 1);
                        v___x_842_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Linter_omit___lam__1___closed__1),
                            core::ptr::addr_of_mut!(l_Lean_Linter_omit___lam__1___closed__1_once),
                            _init_l_Lean_Linter_omit___lam__1___closed__1,
                        );
                        v___x_843_ = l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1(
                            v___x_834_, v_val_841_, v___x_842_, v___y_826_, v___y_827_,
                        );
                        crate::leanh::lean_dec(v_val_841_);
                        return v___x_843_;
                    } else {
                        crate::leanh::lean_dec(v___x_840_);
                        v___x_844_ = crate::leanh::lean_box(0);
                        if v_isShared_833_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_832_, 0, v___x_844_);
                            v___x_846_ = v___x_832_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_847_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
                            v___x_846_ = v_reuseFailAlloc_847_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_838_;
            }
            3 => {
                return v___x_846_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_omit___lam__1___boxed(
    mut v___f_849_: *mut crate::leanh::LeanObject,
    mut v_stx_850_: *mut crate::leanh::LeanObject,
    mut v___y_851_: *mut crate::leanh::LeanObject,
    mut v___y_852_: *mut crate::leanh::LeanObject,
    mut v___y_853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_854_ = l_Lean_Linter_omit___lam__1(v___f_849_, v_stx_850_, v___y_851_, v___y_852_);
    crate::leanh::lean_dec(v___y_852_);
    crate::leanh::lean_dec_ref(v___y_851_);
    return v_res_854_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0(
    mut v_o_866_: *mut crate::leanh::LeanObject,
    mut v___y_867_: *mut crate::leanh::LeanObject,
    mut v___y_868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_870_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg(v_o_866_, v___y_868_);
    return v___x_870_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___boxed(
    mut v_o_871_: *mut crate::leanh::LeanObject,
    mut v___y_872_: *mut crate::leanh::LeanObject,
    mut v___y_873_: *mut crate::leanh::LeanObject,
    mut v___y_874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_875_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0(v_o_871_, v___y_872_, v___y_873_);
    crate::leanh::lean_dec(v___y_873_);
    crate::leanh::lean_dec_ref(v___y_872_);
    return v_res_875_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4(
    mut v_msgData_876_: *mut crate::leanh::LeanObject,
    mut v___y_877_: *mut crate::leanh::LeanObject,
    mut v___y_878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_880_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg(v_msgData_876_, v___y_878_);
    return v___x_880_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msgData_881_: *mut crate::leanh::LeanObject,
    mut v___y_882_: *mut crate::leanh::LeanObject,
    mut v___y_883_: *mut crate::leanh::LeanObject,
    mut v___y_884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_885_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4(v_msgData_881_, v___y_882_, v___y_883_);
    crate::leanh::lean_dec(v___y_883_);
    crate::leanh::lean_dec_ref(v___y_882_);
    return v_res_885_;
}
pub unsafe fn l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3756037646____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_887_ = l_Lean_Linter_omit;
    v___x_888_ = l_Lean_Elab_Command_addLinter(v___x_887_);
    return v___x_888_;
}
pub unsafe fn l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3756037646____hygCtx___hyg_2____boxed(
    mut v_a_889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_890_ = l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3756037646____hygCtx___hyg_2_();
    return v_res_890_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_Omit(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_linter_omit = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Linter_linter_omit);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3756037646____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_Omit(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter_Omit(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Omit(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_Omit(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Linter_Omit(builtin);
}

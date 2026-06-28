// Lean compiler output
// Module: Lean.Linter.Omit
// Imports: Lean.Elab.Command Lean.Linter.Util
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_find_x3f;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind, l_Lean_replaceRef,
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
use crate::lean_imports_rs::Init::Prelude::{
    lean_mk_empty_array_with_capacity, lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_get_value,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [111, 109, 105, 116, 0]};
static mut l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut LeanObject,5701751079888345786 as *mut LeanObject] };
pub static l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut LeanObject,1170131724013778820 as *mut LeanObject] };
static mut l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [101, 110, 97, 98, 108, 101, 32, 116, 104, 101, 32, 39, 97, 118, 111, 105, 100, 32, 111, 109, 105, 116, 39, 32, 108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
static l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut LeanObject,6326339448686113589 as *mut LeanObject] };
pub static l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut LeanObject,16012274839969563159 as *mut LeanObject] };
static mut l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l_Lean_Linter_omit___lam__0___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Linter_omit___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_omit___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_omit___lam__0___closed__1_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Linter_omit___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_omit___lam__0___closed__1_value) as *mut LeanObject;
static l_Lean_Linter_omit___lam__0___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter_omit___lam__0___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_omit___lam__0___closed__2_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_omit___lam__0___closed__0_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Linter_omit___lam__0___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_omit___lam__0___closed__2_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_omit___lam__0___closed__1_value) as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
pub static l_Lean_Linter_omit___lam__0___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_omit___lam__0___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut LeanObject,17954277902228494328 as *mut LeanObject] };
static mut l_Lean_Linter_omit___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_omit___lam__0___closed__2_value) as *mut LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__0_value:
    LeanStringObject<46> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__2_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Linter_omit___lam__1___closed__0_value: LeanStringObject<80> = LeanStringObject {
    m_header: LeanObject {
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
        111, 105, 100, 101, 100, 32, 105, 110, 32, 102, 97, 118, 111, 114, 32, 111, 102, 32, 114,
        101, 115, 116, 114, 117, 99, 116, 117, 114, 105, 110, 103, 32, 121, 111, 117, 114, 32, 96,
        118, 97, 114, 105, 97, 98, 108, 101, 96, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111,
        110, 115, 0,
    ],
};
static mut l_Lean_Linter_omit___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_omit___lam__1___closed__0_value) as *mut LeanObject;
static mut l_Lean_Linter_omit___lam__1___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_omit___lam__1___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_omit___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Linter_omit___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Linter_omit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_omit___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_omit___closed__1_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Linter_omit___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(l_Lean_Linter_omit___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_Linter_omit___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_omit___closed__1_value) as *mut LeanObject;
static l_Lean_Linter_omit___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter_omit___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_omit___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
pub static l_Lean_Linter_omit___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_omit___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__value) as *mut LeanObject,2874839555205088126 as *mut LeanObject] };
static mut l_Lean_Linter_omit___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_omit___closed__2_value) as *mut LeanObject;
pub static l_Lean_Linter_omit___closed__3_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_omit___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_omit___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_omit___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_omit___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Linter_omit: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_omit___closed__3_value) as *mut LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__spec__0(
    mut v_name_446_: *mut LeanObject,
    mut v_decl_447_: *mut LeanObject,
    mut v_ref_448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_454_: u8 = 0;
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_459_: u8 = 0;
    let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_464_: u8 = 0;
    let mut v_unused_465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_469_: u8 = 0;
    let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_450_ = lean_ctor_get(v_decl_447_, 0);
                v_descr_451_ = lean_ctor_get(v_decl_447_, 1);
                v_deprecation_x3f_452_ = lean_ctor_get(v_decl_447_, 2);
                v___x_453_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_454_ = (lean_unbox(v_defValue_450_) as u8);
                lean_ctor_set_uint8(v___x_453_, 0 as u32, v___x_454_);
                lean_inc(v_deprecation_x3f_452_);
                lean_inc_ref(v_descr_451_);
                lean_inc_n(v_name_446_, 2);
                v___x_455_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_455_, 0, v_name_446_);
                lean_ctor_set(v___x_455_, 1, v_ref_448_);
                lean_ctor_set(v___x_455_, 2, v___x_453_);
                lean_ctor_set(v___x_455_, 3, v_descr_451_);
                lean_ctor_set(v___x_455_, 4, v_deprecation_x3f_452_);
                v___x_456_ = lean_register_option(v_name_446_, v___x_455_);
                if lean_obj_tag(v___x_456_) == 0 {
                    v_isSharedCheck_464_ = (!lean_is_exclusive(v___x_456_)) as u8;
                    if v_isSharedCheck_464_ == 0 {
                        v_unused_465_ = lean_ctor_get(v___x_456_, 0);
                        lean_dec(v_unused_465_);
                        v___x_458_ = v___x_456_;
                        v_isShared_459_ = v_isSharedCheck_464_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_456_);
                        v___x_458_ = lean_box(0);
                        v_isShared_459_ = v_isSharedCheck_464_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_446_);
                    v_a_466_ = lean_ctor_get(v___x_456_, 0);
                    v_isSharedCheck_473_ = (!lean_is_exclusive(v___x_456_)) as u8;
                    if v_isSharedCheck_473_ == 0 {
                        v___x_468_ = v___x_456_;
                        v_isShared_469_ = v_isSharedCheck_473_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_466_);
                        lean_dec(v___x_456_);
                        v___x_468_ = lean_box(0);
                        v_isShared_469_ = v_isSharedCheck_473_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_450_);
                v___x_460_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_460_, 0, v_name_446_);
                lean_ctor_set(v___x_460_, 1, v_defValue_450_);
                if v_isShared_459_ == 0 {
                    lean_ctor_set(v___x_458_, 0, v___x_460_);
                    v___x_462_ = v___x_458_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
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
                    v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
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
    mut v_name_474_: *mut LeanObject,
    mut v_decl_475_: *mut LeanObject,
    mut v_ref_476_: *mut LeanObject,
    mut v_a_477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_478_: *mut LeanObject = core::ptr::null_mut();
    v_res_478_ = l_Lean_Option_register___at___00__private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__spec__0(v_name_474_, v_decl_475_, v_ref_476_);
    lean_dec_ref(v_decl_475_);
    return v_res_478_;
}
pub unsafe fn l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
    v___x_498_ = l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_;
    v___x_499_ = l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_;
    v___x_500_ = l___private_Lean_Linter_Omit_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_;
    v___x_501_ = l_Lean_Option_register___at___00__private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4__spec__0(v___x_498_, v___x_499_, v___x_500_);
    return v___x_501_;
}
pub unsafe fn l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4____boxed(
    mut v_a_502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_503_: *mut LeanObject = core::ptr::null_mut();
    v_res_503_ = l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_();
    return v_res_503_;
}
pub unsafe fn l_Lean_Linter_omit___lam__0(mut v_x_511_: *mut LeanObject) -> u8 {
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_513_: u8 = 0;
    v___x_512_ = l_Lean_Linter_omit___lam__0___closed__2;
    v___x_513_ = l_Lean_Syntax_isOfKind(v_x_511_, v___x_512_);
    return v___x_513_;
}
pub unsafe fn l_Lean_Linter_omit___lam__0___boxed(
    mut v_x_514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_515_: u8 = 0;
    let mut v_r_516_: *mut LeanObject = core::ptr::null_mut();
    v_res_515_ = l_Lean_Linter_omit___lam__0(v_x_514_);
    v_r_516_ = lean_box((v_res_515_) as usize);
    return v_r_516_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__5(
    mut v_opts_517_: *mut LeanObject,
    mut v_opt_518_: *mut LeanObject,
) -> u8 {
    let mut v_name_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
    v_name_519_ = lean_ctor_get(v_opt_518_, 0);
    v_defValue_520_ = lean_ctor_get(v_opt_518_, 1);
    v_map_521_ = lean_ctor_get(v_opts_517_, 0);
    v___x_522_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_521_,
            v_name_519_,
        );
    if lean_obj_tag(v___x_522_) == 0 {
        let mut v___x_523_: u8 = 0;
        v___x_523_ = (lean_unbox(v_defValue_520_) as u8);
        return v___x_523_;
    } else {
        let mut v_val_524_: *mut LeanObject = core::ptr::null_mut();
        v_val_524_ = lean_ctor_get(v___x_522_, 0);
        lean_inc(v_val_524_);
        lean_dec_ref_known(v___x_522_, 1);
        if lean_obj_tag(v_val_524_) == 1 {
            let mut v_v_525_: u8 = 0;
            v_v_525_ = lean_ctor_get_uint8(v_val_524_, 0 as u32);
            lean_dec_ref_known(v_val_524_, 0);
            return v_v_525_;
        } else {
            let mut v___x_526_: u8 = 0;
            lean_dec(v_val_524_);
            v___x_526_ = (lean_unbox(v_defValue_520_) as u8);
            return v___x_526_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__5___boxed(
    mut v_opts_527_: *mut LeanObject,
    mut v_opt_528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_529_: u8 = 0;
    let mut v_r_530_: *mut LeanObject = core::ptr::null_mut();
    v_res_529_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__5(v_opts_527_, v_opt_528_);
    lean_dec_ref(v_opt_528_);
    lean_dec_ref(v_opts_527_);
    v_r_530_ = lean_box((v_res_529_) as usize);
    return v_r_530_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
    v___x_531_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_531_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    v___x_532_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
    v___x_533_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_533_, 0, v___x_532_);
    return v___x_533_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    v___x_534_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_535_ = lean_unsigned_to_nat(0);
    v___x_536_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_536_, 0, v___x_535_);
    lean_ctor_set(v___x_536_, 1, v___x_535_);
    lean_ctor_set(v___x_536_, 2, v___x_535_);
    lean_ctor_set(v___x_536_, 3, v___x_535_);
    lean_ctor_set(v___x_536_, 4, v___x_534_);
    lean_ctor_set(v___x_536_, 5, v___x_534_);
    lean_ctor_set(v___x_536_, 6, v___x_534_);
    lean_ctor_set(v___x_536_, 7, v___x_534_);
    lean_ctor_set(v___x_536_, 8, v___x_534_);
    lean_ctor_set(v___x_536_, 9, v___x_534_);
    return v___x_536_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    v___x_537_ = lean_unsigned_to_nat(32);
    v___x_538_ = lean_mk_empty_array_with_capacity(v___x_537_);
    v___x_539_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_539_, 0, v___x_538_);
    return v___x_539_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_540_: usize = 0;
    let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
    v___x_540_ = 5usize;
    v___x_541_ = lean_unsigned_to_nat(0);
    v___x_542_ = lean_unsigned_to_nat(32);
    v___x_543_ = lean_mk_empty_array_with_capacity(v___x_542_);
    v___x_544_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
    v___x_545_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_545_, 0, v___x_544_);
    lean_ctor_set(v___x_545_, 1, v___x_543_);
    lean_ctor_set(v___x_545_, 2, v___x_541_);
    lean_ctor_set(v___x_545_, 3, v___x_541_);
    lean_ctor_set_usize(v___x_545_, 4, v___x_540_);
    return v___x_545_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    v___x_546_ = lean_box(1);
    v___x_547_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
    v___x_548_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_549_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_549_, 0, v___x_548_);
    lean_ctor_set(v___x_549_, 1, v___x_547_);
    lean_ctor_set(v___x_549_, 2, v___x_546_);
    return v___x_549_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_msgData_550_: *mut LeanObject,
    mut v___y_551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    v___x_553_ = lean_st_ref_get(v___y_551_);
    v_env_554_ = lean_ctor_get(v___x_553_, 0);
    lean_inc_ref(v_env_554_);
    lean_dec(v___x_553_);
    v___x_555_ = lean_st_ref_get(v___y_551_);
    v_scopes_556_ = lean_ctor_get(v___x_555_, 2);
    lean_inc(v_scopes_556_);
    lean_dec(v___x_555_);
    v___x_557_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_558_ = l_List_head_x21___redArg(v___x_557_, v_scopes_556_);
    lean_dec(v_scopes_556_);
    v_opts_559_ = lean_ctor_get(v___x_558_, 1);
    lean_inc_ref(v_opts_559_);
    lean_dec(v___x_558_);
    v___x_560_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
    v___x_561_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
    v___x_562_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_562_, 0, v_env_554_);
    lean_ctor_set(v___x_562_, 1, v___x_560_);
    lean_ctor_set(v___x_562_, 2, v___x_561_);
    lean_ctor_set(v___x_562_, 3, v_opts_559_);
    v___x_563_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_563_, 0, v___x_562_);
    lean_ctor_set(v___x_563_, 1, v_msgData_550_);
    v___x_564_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_564_, 0, v___x_563_);
    return v___x_564_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_msgData_565_: *mut LeanObject,
    mut v___y_566_: *mut LeanObject,
    mut v___y_567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_568_: *mut LeanObject = core::ptr::null_mut();
    v_res_568_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg(v_msgData_565_, v___y_566_);
    lean_dec(v___y_566_);
    return v_res_568_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0(
    mut v___y_570_: u8,
    mut v_suppressElabErrors_571_: u8,
    mut v_x_572_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_572_) == 1 {
        let mut v_pre_573_: *mut LeanObject = core::ptr::null_mut();
        v_pre_573_ = lean_ctor_get(v_x_572_, 0);
        if lean_obj_tag(v_pre_573_) == 0 {
            let mut v_str_574_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_576_: u8 = 0;
            v_str_574_ = lean_ctor_get(v_x_572_, 1);
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
    mut v___y_577_: *mut LeanObject,
    mut v_suppressElabErrors_578_: *mut LeanObject,
    mut v_x_579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3058__boxed_580_: u8 = 0;
    let mut v_suppressElabErrors_boxed_581_: u8 = 0;
    let mut v_res_582_: u8 = 0;
    let mut v_r_583_: *mut LeanObject = core::ptr::null_mut();
    v___y_3058__boxed_580_ = (lean_unbox(v___y_577_) as u8);
    v_suppressElabErrors_boxed_581_ = (lean_unbox(v_suppressElabErrors_578_) as u8);
    v_res_582_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0(v___y_3058__boxed_580_, v_suppressElabErrors_boxed_581_, v_x_579_);
    lean_dec(v_x_579_);
    v_r_583_ = lean_box((v_res_582_) as usize);
    return v_r_583_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3(
    mut v_ref_585_: *mut LeanObject,
    mut v_msgData_586_: *mut LeanObject,
    mut v_severity_587_: u8,
    mut v_isSilent_588_: u8,
    mut v___y_589_: *mut LeanObject,
    mut v___y_590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_593_: u8 = 0;
    let mut v___y_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_596_: u8 = 0;
    let mut v___y_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_607_: u8 = 0;
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_624_: u8 = 0;
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_637_: u8 = 0;
    let mut v_isSharedCheck_638_: u8 = 0;
    let mut v_a_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_642_: u8 = 0;
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_646_: u8 = 0;
    let mut v_a_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_650_: u8 = 0;
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_654_: u8 = 0;
    let mut v___y_656_: u8 = 0;
    let mut v___y_657_: u8 = 0;
    let mut v___y_658_: u8 = 0;
    let mut v___y_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_663_: u8 = 0;
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_669_: u8 = 0;
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_677_: u8 = 0;
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_682_: u8 = 0;
    let mut v___y_684_: u8 = 0;
    let mut v___y_685_: u8 = 0;
    let mut v___y_686_: u8 = 0;
    let mut v___y_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_692_: u8 = 0;
    let mut v___y_693_: u8 = 0;
    let mut v___y_694_: u8 = 0;
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_704_: u8 = 0;
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_708_: u8 = 0;
    let mut v___x_709_: u8 = 0;
    let mut v___y_711_: u8 = 0;
    let mut v___y_712_: u8 = 0;
    let mut v___y_713_: u8 = 0;
    let mut v___y_715_: u8 = 0;
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: u8 = 0;
    let mut v___x_722_: u8 = 0;
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_724_: u8 = 0;
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_msgData_586_);
                    v___x_728_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_586_);
                    v___y_715_ = v___x_728_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                v___x_601_ = l_Lean_Elab_Command_getScope___redArg(v___y_600_);
                if lean_obj_tag(v___x_601_) == 0 {
                    v_a_602_ = lean_ctor_get(v___x_601_, 0);
                    lean_inc(v_a_602_);
                    lean_dec_ref_known(v___x_601_, 1);
                    v___x_603_ = l_Lean_Elab_Command_getScope___redArg(v___y_600_);
                    if lean_obj_tag(v___x_603_) == 0 {
                        v_a_604_ = lean_ctor_get(v___x_603_, 0);
                        v_isSharedCheck_638_ = (!lean_is_exclusive(v___x_603_)) as u8;
                        if v_isSharedCheck_638_ == 0 {
                            v___x_606_ = v___x_603_;
                            v_isShared_607_ = v_isSharedCheck_638_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_604_);
                            lean_dec(v___x_603_);
                            v___x_606_ = lean_box(0);
                            v_isShared_607_ = v_isSharedCheck_638_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_602_);
                        lean_dec_ref(v___y_598_);
                        lean_dec(v___y_595_);
                        lean_dec_ref(v___y_594_);
                        v_a_639_ = lean_ctor_get(v___x_603_, 0);
                        v_isSharedCheck_646_ = (!lean_is_exclusive(v___x_603_)) as u8;
                        if v_isSharedCheck_646_ == 0 {
                            v___x_641_ = v___x_603_;
                            v_isShared_642_ = v_isSharedCheck_646_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_639_);
                            lean_dec(v___x_603_);
                            v___x_641_ = lean_box(0);
                            v_isShared_642_ = v_isSharedCheck_646_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_598_);
                    lean_dec(v___y_595_);
                    lean_dec_ref(v___y_594_);
                    v_a_647_ = lean_ctor_get(v___x_601_, 0);
                    v_isSharedCheck_654_ = (!lean_is_exclusive(v___x_601_)) as u8;
                    if v_isSharedCheck_654_ == 0 {
                        v___x_649_ = v___x_601_;
                        v_isShared_650_ = v_isSharedCheck_654_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_647_);
                        lean_dec(v___x_601_);
                        v___x_649_ = lean_box(0);
                        v_isShared_650_ = v_isSharedCheck_654_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_608_ = lean_st_ref_take(v___y_600_);
                v_currNamespace_609_ = lean_ctor_get(v_a_602_, 2);
                lean_inc(v_currNamespace_609_);
                lean_dec(v_a_602_);
                v_openDecls_610_ = lean_ctor_get(v_a_604_, 3);
                lean_inc(v_openDecls_610_);
                lean_dec(v_a_604_);
                v_env_611_ = lean_ctor_get(v___x_608_, 0);
                v_messages_612_ = lean_ctor_get(v___x_608_, 1);
                v_scopes_613_ = lean_ctor_get(v___x_608_, 2);
                v_usedQuotCtxts_614_ = lean_ctor_get(v___x_608_, 3);
                v_nextMacroScope_615_ = lean_ctor_get(v___x_608_, 4);
                v_maxRecDepth_616_ = lean_ctor_get(v___x_608_, 5);
                v_ngen_617_ = lean_ctor_get(v___x_608_, 6);
                v_auxDeclNGen_618_ = lean_ctor_get(v___x_608_, 7);
                v_infoState_619_ = lean_ctor_get(v___x_608_, 8);
                v_traceState_620_ = lean_ctor_get(v___x_608_, 9);
                v_snapshotTasks_621_ = lean_ctor_get(v___x_608_, 10);
                v_isSharedCheck_637_ = (!lean_is_exclusive(v___x_608_)) as u8;
                if v_isSharedCheck_637_ == 0 {
                    v___x_623_ = v___x_608_;
                    v_isShared_624_ = v_isSharedCheck_637_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_621_);
                    lean_inc(v_traceState_620_);
                    lean_inc(v_infoState_619_);
                    lean_inc(v_auxDeclNGen_618_);
                    lean_inc(v_ngen_617_);
                    lean_inc(v_maxRecDepth_616_);
                    lean_inc(v_nextMacroScope_615_);
                    lean_inc(v_usedQuotCtxts_614_);
                    lean_inc(v_scopes_613_);
                    lean_inc(v_messages_612_);
                    lean_inc(v_env_611_);
                    lean_dec(v___x_608_);
                    v___x_623_ = lean_box(0);
                    v_isShared_624_ = v_isSharedCheck_637_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_625_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_625_, 0, v_currNamespace_609_);
                lean_ctor_set(v___x_625_, 1, v_openDecls_610_);
                v___x_626_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_626_, 0, v___x_625_);
                lean_ctor_set(v___x_626_, 1, v___y_594_);
                lean_inc_ref(v___y_599_);
                lean_inc_ref(v___y_597_);
                v___x_627_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_627_, 0, v___y_597_);
                lean_ctor_set(v___x_627_, 1, v___y_598_);
                lean_ctor_set(v___x_627_, 2, v___y_595_);
                lean_ctor_set(v___x_627_, 3, v___y_599_);
                lean_ctor_set(v___x_627_, 4, v___x_626_);
                lean_ctor_set_uint8(
                    v___x_627_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_596_,
                );
                lean_ctor_set_uint8(
                    v___x_627_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_593_,
                );
                lean_ctor_set_uint8(
                    v___x_627_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_588_,
                );
                v___x_628_ = l_Lean_MessageLog_add(v___x_627_, v_messages_612_);
                if v_isShared_624_ == 0 {
                    lean_ctor_set(v___x_623_, 1, v___x_628_);
                    v___x_630_ = v___x_623_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_636_, 0, v_env_611_);
                    lean_ctor_set(v_reuseFailAlloc_636_, 1, v___x_628_);
                    lean_ctor_set(v_reuseFailAlloc_636_, 2, v_scopes_613_);
                    lean_ctor_set(v_reuseFailAlloc_636_, 3, v_usedQuotCtxts_614_);
                    lean_ctor_set(v_reuseFailAlloc_636_, 4, v_nextMacroScope_615_);
                    lean_ctor_set(v_reuseFailAlloc_636_, 5, v_maxRecDepth_616_);
                    lean_ctor_set(v_reuseFailAlloc_636_, 6, v_ngen_617_);
                    lean_ctor_set(v_reuseFailAlloc_636_, 7, v_auxDeclNGen_618_);
                    lean_ctor_set(v_reuseFailAlloc_636_, 8, v_infoState_619_);
                    lean_ctor_set(v_reuseFailAlloc_636_, 9, v_traceState_620_);
                    lean_ctor_set(v_reuseFailAlloc_636_, 10, v_snapshotTasks_621_);
                    v___x_630_ = v_reuseFailAlloc_636_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_631_ = lean_st_ref_set(v___y_600_, v___x_630_);
                v___x_632_ = lean_box(0);
                if v_isShared_607_ == 0 {
                    lean_ctor_set(v___x_606_, 0, v___x_632_);
                    v___x_634_ = v___x_606_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_632_);
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
                    v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
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
                    v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
                    v___x_652_ = v_reuseFailAlloc_653_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_652_;
            }
            10 => {
                v_fileName_661_ = lean_ctor_get(v___y_589_, 0);
                v_fileMap_662_ = lean_ctor_get(v___y_589_, 1);
                v_suppressElabErrors_663_ = lean_ctor_get_uint8(
                    v___y_589_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v___x_664_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_586_,
                    );
                v___x_665_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg(v___x_664_, v___y_590_);
                v_a_666_ = lean_ctor_get(v___x_665_, 0);
                v_isSharedCheck_682_ = (!lean_is_exclusive(v___x_665_)) as u8;
                if v_isSharedCheck_682_ == 0 {
                    v___x_668_ = v___x_665_;
                    v_isShared_669_ = v_isSharedCheck_682_;
                    state = 11;
                    continue;
                } else {
                    lean_inc(v_a_666_);
                    lean_dec(v___x_665_);
                    v___x_668_ = lean_box(0);
                    v_isShared_669_ = v_isSharedCheck_682_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                lean_inc_ref_n(v_fileMap_662_, 2);
                v___x_670_ = l_Lean_FileMap_toPosition(v_fileMap_662_, v___y_659_);
                lean_dec(v___y_659_);
                v___x_671_ = l_Lean_FileMap_toPosition(v_fileMap_662_, v___y_660_);
                lean_dec(v___y_660_);
                v___x_672_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_672_, 0, v___x_671_);
                v___x_673_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___closed__0;
                if v_suppressElabErrors_663_ == 0 {
                    lean_del_object(v___x_668_);
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
                    v___x_674_ = lean_box((v___y_656_) as usize);
                    v___x_675_ = lean_box((v_suppressElabErrors_663_) as usize);
                    v___f_676_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_676_, 0, v___x_674_);
                    lean_closure_set(v___f_676_, 1, v___x_675_);
                    lean_inc(v_a_666_);
                    v___x_677_ = l_Lean_MessageData_hasTag(v___f_676_, v_a_666_);
                    if v___x_677_ == 0 {
                        lean_dec_ref_known(v___x_672_, 1);
                        lean_dec_ref(v___x_670_);
                        lean_dec(v_a_666_);
                        v___x_678_ = lean_box(0);
                        if v_isShared_669_ == 0 {
                            lean_ctor_set(v___x_668_, 0, v___x_678_);
                            v___x_680_ = v___x_668_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_678_);
                            v___x_680_ = v_reuseFailAlloc_681_;
                            state = 12;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_668_);
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
                lean_dec(v___y_687_);
                if lean_obj_tag(v___x_689_) == 0 {
                    lean_inc(v___y_688_);
                    v___y_656_ = v___y_684_;
                    v___y_657_ = v___y_685_;
                    v___y_658_ = v___y_686_;
                    v___y_659_ = v___y_688_;
                    v___y_660_ = v___y_688_;
                    state = 10;
                    continue;
                } else {
                    v_val_690_ = lean_ctor_get(v___x_689_, 0);
                    lean_inc(v_val_690_);
                    lean_dec_ref_known(v___x_689_, 1);
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
                if lean_obj_tag(v___x_695_) == 0 {
                    v_a_696_ = lean_ctor_get(v___x_695_, 0);
                    lean_inc(v_a_696_);
                    lean_dec_ref_known(v___x_695_, 1);
                    v_ref_697_ = l_Lean_replaceRef(v_ref_585_, v_a_696_);
                    lean_dec(v_a_696_);
                    v___x_698_ = l_Lean_Syntax_getPos_x3f(v_ref_697_, v___y_693_);
                    if lean_obj_tag(v___x_698_) == 0 {
                        v___x_699_ = lean_unsigned_to_nat(0);
                        v___y_684_ = v___y_692_;
                        v___y_685_ = v___y_694_;
                        v___y_686_ = v___y_693_;
                        v___y_687_ = v_ref_697_;
                        v___y_688_ = v___x_699_;
                        state = 13;
                        continue;
                    } else {
                        v_val_700_ = lean_ctor_get(v___x_698_, 0);
                        lean_inc(v_val_700_);
                        lean_dec_ref_known(v___x_698_, 1);
                        v___y_684_ = v___y_692_;
                        v___y_685_ = v___y_694_;
                        v___y_686_ = v___y_693_;
                        v___y_687_ = v_ref_697_;
                        v___y_688_ = v_val_700_;
                        state = 13;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_586_);
                    v_a_701_ = lean_ctor_get(v___x_695_, 0);
                    v_isSharedCheck_708_ = (!lean_is_exclusive(v___x_695_)) as u8;
                    if v_isSharedCheck_708_ == 0 {
                        v___x_703_ = v___x_695_;
                        v_isShared_704_ = v_isSharedCheck_708_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_701_);
                        lean_dec(v___x_695_);
                        v___x_703_ = lean_box(0);
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
                    v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
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
                    v_scopes_717_ = lean_ctor_get(v___x_716_, 2);
                    lean_inc(v_scopes_717_);
                    lean_dec(v___x_716_);
                    v___x_718_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_719_ = l_List_head_x21___redArg(v___x_718_, v_scopes_717_);
                    lean_dec(v_scopes_717_);
                    v_opts_720_ = lean_ctor_get(v___x_719_, 1);
                    lean_inc_ref(v_opts_720_);
                    lean_dec(v___x_719_);
                    v___x_721_ = 1;
                    v___x_722_ = l_Lean_instBEqMessageSeverity_beq(v_severity_587_, v___x_721_);
                    if v___x_722_ == 0 {
                        lean_dec_ref(v_opts_720_);
                        v___y_711_ = v___y_715_;
                        v___y_712_ = v___y_715_;
                        v___y_713_ = v___x_722_;
                        state = 17;
                        continue;
                    } else {
                        v___x_723_ = l_Lean_warningAsError;
                        v___x_724_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__5(v_opts_720_, v___x_723_);
                        lean_dec_ref(v_opts_720_);
                        v___y_711_ = v___y_715_;
                        v___y_712_ = v___y_715_;
                        v___y_713_ = v___x_724_;
                        state = 17;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_586_);
                    v___x_725_ = lean_box(0);
                    v___x_726_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_726_, 0, v___x_725_);
                    return v___x_726_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3___boxed(
    mut v_ref_729_: *mut LeanObject,
    mut v_msgData_730_: *mut LeanObject,
    mut v_severity_731_: *mut LeanObject,
    mut v_isSilent_732_: *mut LeanObject,
    mut v___y_733_: *mut LeanObject,
    mut v___y_734_: *mut LeanObject,
    mut v___y_735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_736_: u8 = 0;
    let mut v_isSilent_boxed_737_: u8 = 0;
    let mut v_res_738_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_736_ = (lean_unbox(v_severity_731_) as u8);
    v_isSilent_boxed_737_ = (lean_unbox(v_isSilent_732_) as u8);
    v_res_738_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3(v_ref_729_, v_msgData_730_, v_severity_boxed_736_, v_isSilent_boxed_737_, v___y_733_, v___y_734_);
    lean_dec(v___y_734_);
    lean_dec_ref(v___y_733_);
    lean_dec(v_ref_729_);
    return v_res_738_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2(
    mut v_ref_739_: *mut LeanObject,
    mut v_msgData_740_: *mut LeanObject,
    mut v___y_741_: *mut LeanObject,
    mut v___y_742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_744_: u8 = 0;
    let mut v___x_745_: u8 = 0;
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    v___x_744_ = 1;
    v___x_745_ = 0;
    v___x_746_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3(v_ref_739_, v_msgData_740_, v___x_744_, v___x_745_, v___y_741_, v___y_742_);
    return v___x_746_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2___boxed(
    mut v_ref_747_: *mut LeanObject,
    mut v_msgData_748_: *mut LeanObject,
    mut v___y_749_: *mut LeanObject,
    mut v___y_750_: *mut LeanObject,
    mut v___y_751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_752_: *mut LeanObject = core::ptr::null_mut();
    v_res_752_ =
        l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2(
            v_ref_747_,
            v_msgData_748_,
            v___y_749_,
            v___y_750_,
        );
    lean_dec(v___y_750_);
    lean_dec_ref(v___y_749_);
    lean_dec(v_ref_747_);
    return v_res_752_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    v___x_754_ = l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__0;
    v___x_755_ = l_Lean_stringToMessageData(v___x_754_);
    return v___x_755_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3()
-> *mut LeanObject {
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    v___x_757_ = l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__2;
    v___x_758_ = l_Lean_stringToMessageData(v___x_757_);
    return v___x_758_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1(
    mut v_linterOption_759_: *mut LeanObject,
    mut v_stx_760_: *mut LeanObject,
    mut v_msg_761_: *mut LeanObject,
    mut v___y_762_: *mut LeanObject,
    mut v___y_763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_768_: u8 = 0;
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_disable_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_782_: u8 = 0;
    let mut v_unused_783_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_765_ = lean_ctor_get(v_linterOption_759_, 0);
                v_isSharedCheck_782_ = (!lean_is_exclusive(v_linterOption_759_)) as u8;
                if v_isSharedCheck_782_ == 0 {
                    v_unused_783_ = lean_ctor_get(v_linterOption_759_, 1);
                    lean_dec(v_unused_783_);
                    v___x_767_ = v_linterOption_759_;
                    v_isShared_768_ = v_isSharedCheck_782_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_name_765_);
                    lean_dec(v_linterOption_759_);
                    v___x_767_ = lean_box(0);
                    v_isShared_768_ = v_isSharedCheck_782_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_769_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1_once
                    ),
                    _init_l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__1,
                );
                lean_inc(v_name_765_);
                v___x_770_ = l_Lean_MessageData_ofName(v_name_765_);
                if v_isShared_768_ == 0 {
                    lean_ctor_set_tag(v___x_767_, 7);
                    lean_ctor_set(v___x_767_, 1, v___x_770_);
                    lean_ctor_set(v___x_767_, 0, v___x_769_);
                    v___x_772_ = v___x_767_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_781_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_769_);
                    lean_ctor_set(v_reuseFailAlloc_781_, 1, v___x_770_);
                    v___x_772_ = v_reuseFailAlloc_781_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_773_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3_once
                    ),
                    _init_l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___closed__3,
                );
                v___x_774_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_774_, 0, v___x_772_);
                lean_ctor_set(v___x_774_, 1, v___x_773_);
                v_disable_775_ = l_Lean_MessageData_note(v___x_774_);
                v___x_776_ = l_Lean_Linter_linterMessageTag;
                v___x_777_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_777_, 0, v_msg_761_);
                lean_ctor_set(v___x_777_, 1, v_disable_775_);
                v___x_778_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_778_, 0, v___x_776_);
                lean_ctor_set(v___x_778_, 1, v___x_777_);
                v___x_779_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_779_, 0, v_name_765_);
                lean_ctor_set(v___x_779_, 1, v___x_778_);
                v___x_780_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2(v_stx_760_, v___x_779_, v___y_762_, v___y_763_);
                return v___x_780_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1___boxed(
    mut v_linterOption_784_: *mut LeanObject,
    mut v_stx_785_: *mut LeanObject,
    mut v_msg_786_: *mut LeanObject,
    mut v___y_787_: *mut LeanObject,
    mut v___y_788_: *mut LeanObject,
    mut v___y_789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_790_: *mut LeanObject = core::ptr::null_mut();
    v_res_790_ = l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1(
        v_linterOption_784_,
        v_stx_785_,
        v_msg_786_,
        v___y_787_,
        v___y_788_,
    );
    lean_dec(v___y_788_);
    lean_dec_ref(v___y_787_);
    lean_dec(v_stx_785_);
    return v_res_790_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg(
    mut v_o_791_: *mut LeanObject,
    mut v___y_792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linterSets_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    v___x_794_ = lean_st_ref_get(v___y_792_);
    v_env_795_ = lean_ctor_get(v___x_794_, 0);
    lean_inc_ref(v_env_795_);
    lean_dec(v___x_794_);
    v___x_796_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_797_ = lean_ctor_get(v___x_796_, 0);
    v_asyncMode_798_ = lean_ctor_get(v_toEnvExtension_797_, 2);
    v___x_799_ = lean_box(1);
    v___x_800_ = lean_box(0);
    v_linterSets_801_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_799_,
        v___x_796_,
        v_env_795_,
        v_asyncMode_798_,
        v___x_800_,
    );
    v___x_802_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_802_, 0, v_o_791_);
    lean_ctor_set(v___x_802_, 1, v_linterSets_801_);
    v___x_803_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_803_, 0, v___x_802_);
    return v___x_803_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg___boxed(
    mut v_o_804_: *mut LeanObject,
    mut v___y_805_: *mut LeanObject,
    mut v___y_806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_807_: *mut LeanObject = core::ptr::null_mut();
    v_res_807_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg(v_o_804_, v___y_805_);
    lean_dec(v___y_805_);
    return v_res_807_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0(
    mut v___y_808_: *mut LeanObject,
    mut v___y_809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    v___x_811_ = lean_st_ref_get(v___y_809_);
    v_scopes_812_ = lean_ctor_get(v___x_811_, 2);
    lean_inc(v_scopes_812_);
    lean_dec(v___x_811_);
    v___x_813_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_814_ = l_List_head_x21___redArg(v___x_813_, v_scopes_812_);
    lean_dec(v_scopes_812_);
    v_opts_815_ = lean_ctor_get(v___x_814_, 1);
    lean_inc_ref(v_opts_815_);
    lean_dec(v___x_814_);
    v___x_816_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg(v_opts_815_, v___y_809_);
    return v___x_816_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0___boxed(
    mut v___y_817_: *mut LeanObject,
    mut v___y_818_: *mut LeanObject,
    mut v___y_819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_820_: *mut LeanObject = core::ptr::null_mut();
    v_res_820_ =
        l_Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0(v___y_817_, v___y_818_);
    lean_dec(v___y_818_);
    lean_dec_ref(v___y_817_);
    return v_res_820_;
}
pub unsafe fn _init_l_Lean_Linter_omit___lam__1___closed__1() -> *mut LeanObject {
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    v___x_822_ = l_Lean_Linter_omit___lam__1___closed__0;
    v___x_823_ = l_Lean_stringToMessageData(v___x_822_);
    return v___x_823_;
}
pub unsafe fn l_Lean_Linter_omit___lam__1(
    mut v___f_824_: *mut LeanObject,
    mut v_stx_825_: *mut LeanObject,
    mut v___y_826_: *mut LeanObject,
    mut v___y_827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_833_: u8 = 0;
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_835_: u8 = 0;
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_848_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_829_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0(
                    v___y_826_, v___y_827_,
                );
                v_a_830_ = lean_ctor_get(v___x_829_, 0);
                v_isSharedCheck_848_ = (!lean_is_exclusive(v___x_829_)) as u8;
                if v_isSharedCheck_848_ == 0 {
                    v___x_832_ = v___x_829_;
                    v_isShared_833_ = v_isSharedCheck_848_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_830_);
                    lean_dec(v___x_829_);
                    v___x_832_ = lean_box(0);
                    v_isShared_833_ = v_isSharedCheck_848_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_834_ = l_Lean_Linter_linter_omit;
                v___x_835_ = l_Lean_Linter_getLinterValue(v___x_834_, v_a_830_);
                lean_dec(v_a_830_);
                if v___x_835_ == 0 {
                    lean_dec(v_stx_825_);
                    lean_dec_ref(v___f_824_);
                    v___x_836_ = lean_box(0);
                    if v_isShared_833_ == 0 {
                        lean_ctor_set(v___x_832_, 0, v___x_836_);
                        v___x_838_ = v___x_832_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
                        v___x_838_ = v_reuseFailAlloc_839_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_840_ = l_Lean_Syntax_find_x3f(v_stx_825_, v___f_824_);
                    if lean_obj_tag(v___x_840_) == 1 {
                        lean_del_object(v___x_832_);
                        v_val_841_ = lean_ctor_get(v___x_840_, 0);
                        lean_inc(v_val_841_);
                        lean_dec_ref_known(v___x_840_, 1);
                        v___x_842_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Linter_omit___lam__1___closed__1),
                            core::ptr::addr_of_mut!(l_Lean_Linter_omit___lam__1___closed__1_once),
                            _init_l_Lean_Linter_omit___lam__1___closed__1,
                        );
                        v___x_843_ = l_Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1(
                            v___x_834_, v_val_841_, v___x_842_, v___y_826_, v___y_827_,
                        );
                        lean_dec(v_val_841_);
                        return v___x_843_;
                    } else {
                        lean_dec(v___x_840_);
                        v___x_844_ = lean_box(0);
                        if v_isShared_833_ == 0 {
                            lean_ctor_set(v___x_832_, 0, v___x_844_);
                            v___x_846_ = v___x_832_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
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
    mut v___f_849_: *mut LeanObject,
    mut v_stx_850_: *mut LeanObject,
    mut v___y_851_: *mut LeanObject,
    mut v___y_852_: *mut LeanObject,
    mut v___y_853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_854_: *mut LeanObject = core::ptr::null_mut();
    v_res_854_ = l_Lean_Linter_omit___lam__1(v___f_849_, v_stx_850_, v___y_851_, v___y_852_);
    lean_dec(v___y_852_);
    lean_dec_ref(v___y_851_);
    return v_res_854_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0(
    mut v_o_866_: *mut LeanObject,
    mut v___y_867_: *mut LeanObject,
    mut v___y_868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    v___x_870_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___redArg(v_o_866_, v___y_868_);
    return v___x_870_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0___boxed(
    mut v_o_871_: *mut LeanObject,
    mut v___y_872_: *mut LeanObject,
    mut v___y_873_: *mut LeanObject,
    mut v___y_874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_875_: *mut LeanObject = core::ptr::null_mut();
    v_res_875_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_omit_spec__0_spec__0(v_o_871_, v___y_872_, v___y_873_);
    lean_dec(v___y_873_);
    lean_dec_ref(v___y_872_);
    return v_res_875_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4(
    mut v_msgData_876_: *mut LeanObject,
    mut v___y_877_: *mut LeanObject,
    mut v___y_878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    v___x_880_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___redArg(v_msgData_876_, v___y_878_);
    return v___x_880_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msgData_881_: *mut LeanObject,
    mut v___y_882_: *mut LeanObject,
    mut v___y_883_: *mut LeanObject,
    mut v___y_884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_885_: *mut LeanObject = core::ptr::null_mut();
    v_res_885_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_omit_spec__1_spec__2_spec__3_spec__4(v_msgData_881_, v___y_882_, v___y_883_);
    lean_dec(v___y_883_);
    lean_dec_ref(v___y_882_);
    return v_res_885_;
}
pub unsafe fn l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3756037646____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    v___x_887_ = l_Lean_Linter_omit;
    v___x_888_ = l_Lean_Elab_Command_addLinter(v___x_887_);
    return v___x_888_;
}
pub unsafe fn l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3756037646____hygCtx___hyg_2____boxed(
    mut v_a_889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_890_: *mut LeanObject = core::ptr::null_mut();
    v_res_890_ = l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3756037646____hygCtx___hyg_2_();
    return v_res_890_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_Omit(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3596935212____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_linter_omit = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Linter_linter_omit);
    lean_dec_ref(res);
    res = l___private_Lean_Linter_Omit_0__Lean_Linter_initFn_00___x40_Lean_Linter_Omit_3756037646____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_Omit(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter_Omit(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Linter_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Omit(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_Omit(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Linter_Omit(builtin);
}

// Lean compiler output
// Module: Lean.Elab.Time
// Imports: Lean.Elab.Command
use crate::ffi::{
    lean_io_mono_ms_now, lean_mk_empty_array_with_capacity, lean_nat_sub, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_string_dec_eq,
};
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    l_Lean_Syntax_isOfKind, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_commandElabAttribute,
    l_Lean_Elab_Command_elabCommand, l_Lean_Elab_Command_getRef___redArg,
    l_Lean_Elab_Command_getScope___redArg, runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_ofFormat,
    l_Lean_MessageLog_add, l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___closed__0_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Time_elabTimeCmd___closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Elab_Time_elabTimeCmd___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Time_elabTimeCmd___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Time_elabTimeCmd___closed__1_value: leanh::LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Elab_Time_elabTimeCmd___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Time_elabTimeCmd___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Time_elabTimeCmd___closed__2_value: leanh::LeanStringObject<8> =
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
        m_data: [116, 105, 109, 101, 67, 109, 100, 0],
    };
static mut l_Lean_Elab_Time_elabTimeCmd___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Time_elabTimeCmd___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Time_elabTimeCmd___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Time_elabTimeCmd___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Time_elabTimeCmd___closed__3_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Time_elabTimeCmd___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Time_elabTimeCmd___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Time_elabTimeCmd___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Time_elabTimeCmd___closed__3_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Time_elabTimeCmd___closed__2_value)
                as *mut leanh::LeanObject,
            2369326432666722033 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Time_elabTimeCmd___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Time_elabTimeCmd___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Time_elabTimeCmd___closed__4_value: leanh::LeanStringObject<7> =
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
        m_data: [116, 105, 109, 101, 58, 32, 0],
    };
static mut l_Lean_Elab_Time_elabTimeCmd___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Time_elabTimeCmd___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Time_elabTimeCmd___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Time_elabTimeCmd___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Time_elabTimeCmd___closed__6_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [109, 115, 0],
    };
static mut l_Lean_Elab_Time_elabTimeCmd___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Time_elabTimeCmd___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Time_elabTimeCmd___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Time_elabTimeCmd___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__1_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 105, 109, 101, 0]};
static mut l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__2_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 108, 97, 98, 84, 105, 109, 101, 67, 109, 100, 0]};
static mut l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Time_elabTimeCmd___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__1_value) as *mut leanh::LeanObject,7452066385500794260 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__2_value) as *mut leanh::LeanObject,3428595919141693260 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_329_ = leanh::lean_box(0);
    v___x_330_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_331_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_331_, 0, v___x_330_);
    leanh::lean_ctor_set(v___x_331_, 1, v___x_329_);
    return v___x_331_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_333_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg___closed__0);
    v___x_334_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_334_, 0, v___x_333_);
    return v___x_334_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg___boxed(
    mut v___y_335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_336_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg();
    return v_res_336_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0(
    mut v_00_u03b1_337_: *mut leanh::LeanObject,
    mut v___y_338_: *mut leanh::LeanObject,
    mut v___y_339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_341_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg();
    return v___x_341_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___boxed(
    mut v_00_u03b1_342_: *mut leanh::LeanObject,
    mut v___y_343_: *mut leanh::LeanObject,
    mut v___y_344_: *mut leanh::LeanObject,
    mut v___y_345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_346_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0(
        v_00_u03b1_342_,
        v___y_343_,
        v___y_344_,
    );
    leanh::lean_dec(v___y_344_);
    leanh::lean_dec_ref(v___y_343_);
    return v_res_346_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0(
    mut v___y_348_: u8,
    mut v_suppressElabErrors_349_: u8,
    mut v_x_350_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_350_) == 1 {
        let mut v_pre_351_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_351_ = leanh::lean_ctor_get(v_x_350_, 0);
        if leanh::lean_obj_tag(v_pre_351_) == 0 {
            let mut v_str_352_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_353_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_354_: u8 = 0;
            v_str_352_ = leanh::lean_ctor_get(v_x_350_, 1);
            v___x_353_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0___closed__0;
            v___x_354_ = lean_string_dec_eq(v_str_352_, v___x_353_);
            if v___x_354_ == 0 {
                return v___y_348_;
            } else {
                return v_suppressElabErrors_349_;
            }
        } else {
            return v___y_348_;
        }
    } else {
        return v___y_348_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0___boxed(
    mut v___y_355_: *mut leanh::LeanObject,
    mut v_suppressElabErrors_356_: *mut leanh::LeanObject,
    mut v_x_357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2778__boxed_358_: u8 = 0;
    let mut v_suppressElabErrors_boxed_359_: u8 = 0;
    let mut v_res_360_: u8 = 0;
    let mut v_r_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_2778__boxed_358_ = (leanh::lean_unbox(v___y_355_) as u8);
    v_suppressElabErrors_boxed_359_ = (leanh::lean_unbox(v_suppressElabErrors_356_) as u8);
    v_res_360_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0(v___y_2778__boxed_358_, v_suppressElabErrors_boxed_359_, v_x_357_);
    leanh::lean_dec(v_x_357_);
    v_r_361_ = leanh::lean_box((v_res_360_) as usize);
    return v_r_361_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__3(
    mut v_opts_362_: *mut leanh::LeanObject,
    mut v_opt_363_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_364_ = leanh::lean_ctor_get(v_opt_363_, 0);
    v_defValue_365_ = leanh::lean_ctor_get(v_opt_363_, 1);
    v_map_366_ = leanh::lean_ctor_get(v_opts_362_, 0);
    v___x_367_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_366_,
            v_name_364_,
        );
    if leanh::lean_obj_tag(v___x_367_) == 0 {
        let mut v___x_368_: u8 = 0;
        v___x_368_ = (leanh::lean_unbox(v_defValue_365_) as u8);
        return v___x_368_;
    } else {
        let mut v_val_369_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_369_ = leanh::lean_ctor_get(v___x_367_, 0);
        leanh::lean_inc(v_val_369_);
        leanh::lean_dec_ref_known(v___x_367_, 1);
        if leanh::lean_obj_tag(v_val_369_) == 1 {
            let mut v_v_370_: u8 = 0;
            v_v_370_ = leanh::lean_ctor_get_uint8(v_val_369_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_369_, 0);
            return v_v_370_;
        } else {
            let mut v___x_371_: u8 = 0;
            leanh::lean_dec(v_val_369_);
            v___x_371_ = (leanh::lean_unbox(v_defValue_365_) as u8);
            return v___x_371_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__3___boxed(
    mut v_opts_372_: *mut leanh::LeanObject,
    mut v_opt_373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_374_: u8 = 0;
    let mut v_r_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_374_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__3(v_opts_372_, v_opt_373_);
    leanh::lean_dec_ref(v_opt_373_);
    leanh::lean_dec_ref(v_opts_372_);
    v_r_375_ = leanh::lean_box((v_res_374_) as usize);
    return v_r_375_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_376_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_376_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_377_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__0);
    v___x_378_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_378_, 0, v___x_377_);
    return v___x_378_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_379_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1);
    v___x_380_ = leanh::lean_unsigned_to_nat(0);
    v___x_381_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_381_, 0, v___x_380_);
    leanh::lean_ctor_set(v___x_381_, 1, v___x_380_);
    leanh::lean_ctor_set(v___x_381_, 2, v___x_380_);
    leanh::lean_ctor_set(v___x_381_, 3, v___x_380_);
    leanh::lean_ctor_set(v___x_381_, 4, v___x_379_);
    leanh::lean_ctor_set(v___x_381_, 5, v___x_379_);
    leanh::lean_ctor_set(v___x_381_, 6, v___x_379_);
    leanh::lean_ctor_set(v___x_381_, 7, v___x_379_);
    leanh::lean_ctor_set(v___x_381_, 8, v___x_379_);
    leanh::lean_ctor_set(v___x_381_, 9, v___x_379_);
    return v___x_381_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_382_ = leanh::lean_unsigned_to_nat(32);
    v___x_383_ = lean_mk_empty_array_with_capacity(v___x_382_);
    v___x_384_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_384_, 0, v___x_383_);
    return v___x_384_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_385_: usize = 0;
    let mut v___x_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_385_ = 5usize;
    v___x_386_ = leanh::lean_unsigned_to_nat(0);
    v___x_387_ = leanh::lean_unsigned_to_nat(32);
    v___x_388_ = lean_mk_empty_array_with_capacity(v___x_387_);
    v___x_389_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__3);
    v___x_390_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_390_, 0, v___x_389_);
    leanh::lean_ctor_set(v___x_390_, 1, v___x_388_);
    leanh::lean_ctor_set(v___x_390_, 2, v___x_386_);
    leanh::lean_ctor_set(v___x_390_, 3, v___x_386_);
    leanh::lean_ctor_set_usize(v___x_390_, 4, v___x_385_);
    return v___x_390_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_391_ = leanh::lean_box(1);
    v___x_392_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__4);
    v___x_393_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__1);
    v___x_394_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_394_, 0, v___x_393_);
    leanh::lean_ctor_set(v___x_394_, 1, v___x_392_);
    leanh::lean_ctor_set(v___x_394_, 2, v___x_391_);
    return v___x_394_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg(
    mut v_msgData_395_: *mut leanh::LeanObject,
    mut v___y_396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_398_ = lean_st_ref_get(v___y_396_);
    v_env_399_ = leanh::lean_ctor_get(v___x_398_, 0);
    leanh::lean_inc_ref(v_env_399_);
    leanh::lean_dec(v___x_398_);
    v___x_400_ = lean_st_ref_get(v___y_396_);
    v_scopes_401_ = leanh::lean_ctor_get(v___x_400_, 2);
    leanh::lean_inc(v_scopes_401_);
    leanh::lean_dec(v___x_400_);
    v___x_402_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_403_ = l_List_head_x21___redArg(v___x_402_, v_scopes_401_);
    leanh::lean_dec(v_scopes_401_);
    v_opts_404_ = leanh::lean_ctor_get(v___x_403_, 1);
    leanh::lean_inc_ref(v_opts_404_);
    leanh::lean_dec(v___x_403_);
    v___x_405_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__2);
    v___x_406_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___closed__5);
    v___x_407_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_407_, 0, v_env_399_);
    leanh::lean_ctor_set(v___x_407_, 1, v___x_405_);
    leanh::lean_ctor_set(v___x_407_, 2, v___x_406_);
    leanh::lean_ctor_set(v___x_407_, 3, v_opts_404_);
    v___x_408_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_408_, 0, v___x_407_);
    leanh::lean_ctor_set(v___x_408_, 1, v_msgData_395_);
    v___x_409_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_409_, 0, v___x_408_);
    return v___x_409_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_msgData_410_: *mut leanh::LeanObject,
    mut v___y_411_: *mut leanh::LeanObject,
    mut v___y_412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_413_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg(v_msgData_410_, v___y_411_);
    leanh::lean_dec(v___y_411_);
    return v_res_413_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1(
    mut v_ref_415_: *mut leanh::LeanObject,
    mut v_msgData_416_: *mut leanh::LeanObject,
    mut v_severity_417_: u8,
    mut v_isSilent_418_: u8,
    mut v___y_419_: *mut leanh::LeanObject,
    mut v___y_420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_428_: u8 = 0;
    let mut v___y_429_: u8 = 0;
    let mut v___y_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_437_: u8 = 0;
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_454_: u8 = 0;
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_467_: u8 = 0;
    let mut v_isSharedCheck_468_: u8 = 0;
    let mut v_a_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_472_: u8 = 0;
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_476_: u8 = 0;
    let mut v_a_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_480_: u8 = 0;
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_484_: u8 = 0;
    let mut v___y_486_: u8 = 0;
    let mut v___y_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_488_: u8 = 0;
    let mut v___y_489_: u8 = 0;
    let mut v___y_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_493_: u8 = 0;
    let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_499_: u8 = 0;
    let mut v___x_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: u8 = 0;
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_512_: u8 = 0;
    let mut v___y_514_: u8 = 0;
    let mut v___y_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_516_: u8 = 0;
    let mut v___y_517_: u8 = 0;
    let mut v___y_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_522_: u8 = 0;
    let mut v___y_523_: u8 = 0;
    let mut v___y_524_: u8 = 0;
    let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_534_: u8 = 0;
    let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_538_: u8 = 0;
    let mut v___x_539_: u8 = 0;
    let mut v___y_541_: u8 = 0;
    let mut v___y_542_: u8 = 0;
    let mut v___y_543_: u8 = 0;
    let mut v___y_545_: u8 = 0;
    let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: u8 = 0;
    let mut v___x_552_: u8 = 0;
    let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: u8 = 0;
    let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: u8 = 0;
    let mut v___x_558_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_539_ = 2;
                v___x_557_ = l_Lean_instBEqMessageSeverity_beq(v_severity_417_, v___x_539_);
                if v___x_557_ == 0 {
                    v___y_545_ = v___x_557_;
                    state = 18;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_msgData_416_);
                    v___x_558_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_416_);
                    v___y_545_ = v___x_558_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                v___x_431_ = l_Lean_Elab_Command_getScope___redArg(v___y_430_);
                if leanh::lean_obj_tag(v___x_431_) == 0 {
                    v_a_432_ = leanh::lean_ctor_get(v___x_431_, 0);
                    leanh::lean_inc(v_a_432_);
                    leanh::lean_dec_ref_known(v___x_431_, 1);
                    v___x_433_ = l_Lean_Elab_Command_getScope___redArg(v___y_430_);
                    if leanh::lean_obj_tag(v___x_433_) == 0 {
                        v_a_434_ = leanh::lean_ctor_get(v___x_433_, 0);
                        v_isSharedCheck_468_ = (!leanh::lean_is_exclusive(v___x_433_)) as u8;
                        if v_isSharedCheck_468_ == 0 {
                            v___x_436_ = v___x_433_;
                            v_isShared_437_ = v_isSharedCheck_468_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_434_);
                            leanh::lean_dec(v___x_433_);
                            v___x_436_ = leanh::lean_box(0);
                            v_isShared_437_ = v_isSharedCheck_468_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_432_);
                        leanh::lean_dec_ref(v___y_426_);
                        leanh::lean_dec(v___y_425_);
                        leanh::lean_dec_ref(v___y_423_);
                        v_a_469_ = leanh::lean_ctor_get(v___x_433_, 0);
                        v_isSharedCheck_476_ = (!leanh::lean_is_exclusive(v___x_433_)) as u8;
                        if v_isSharedCheck_476_ == 0 {
                            v___x_471_ = v___x_433_;
                            v_isShared_472_ = v_isSharedCheck_476_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_469_);
                            leanh::lean_dec(v___x_433_);
                            v___x_471_ = leanh::lean_box(0);
                            v_isShared_472_ = v_isSharedCheck_476_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_426_);
                    leanh::lean_dec(v___y_425_);
                    leanh::lean_dec_ref(v___y_423_);
                    v_a_477_ = leanh::lean_ctor_get(v___x_431_, 0);
                    v_isSharedCheck_484_ = (!leanh::lean_is_exclusive(v___x_431_)) as u8;
                    if v_isSharedCheck_484_ == 0 {
                        v___x_479_ = v___x_431_;
                        v_isShared_480_ = v_isSharedCheck_484_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_477_);
                        leanh::lean_dec(v___x_431_);
                        v___x_479_ = leanh::lean_box(0);
                        v_isShared_480_ = v_isSharedCheck_484_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_438_ = lean_st_ref_take(v___y_430_);
                v_currNamespace_439_ = leanh::lean_ctor_get(v_a_432_, 2);
                leanh::lean_inc(v_currNamespace_439_);
                leanh::lean_dec(v_a_432_);
                v_openDecls_440_ = leanh::lean_ctor_get(v_a_434_, 3);
                leanh::lean_inc(v_openDecls_440_);
                leanh::lean_dec(v_a_434_);
                v_env_441_ = leanh::lean_ctor_get(v___x_438_, 0);
                v_messages_442_ = leanh::lean_ctor_get(v___x_438_, 1);
                v_scopes_443_ = leanh::lean_ctor_get(v___x_438_, 2);
                v_usedQuotCtxts_444_ = leanh::lean_ctor_get(v___x_438_, 3);
                v_nextMacroScope_445_ = leanh::lean_ctor_get(v___x_438_, 4);
                v_maxRecDepth_446_ = leanh::lean_ctor_get(v___x_438_, 5);
                v_ngen_447_ = leanh::lean_ctor_get(v___x_438_, 6);
                v_auxDeclNGen_448_ = leanh::lean_ctor_get(v___x_438_, 7);
                v_infoState_449_ = leanh::lean_ctor_get(v___x_438_, 8);
                v_traceState_450_ = leanh::lean_ctor_get(v___x_438_, 9);
                v_snapshotTasks_451_ = leanh::lean_ctor_get(v___x_438_, 10);
                v_isSharedCheck_467_ = (!leanh::lean_is_exclusive(v___x_438_)) as u8;
                if v_isSharedCheck_467_ == 0 {
                    v___x_453_ = v___x_438_;
                    v_isShared_454_ = v_isSharedCheck_467_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_451_);
                    leanh::lean_inc(v_traceState_450_);
                    leanh::lean_inc(v_infoState_449_);
                    leanh::lean_inc(v_auxDeclNGen_448_);
                    leanh::lean_inc(v_ngen_447_);
                    leanh::lean_inc(v_maxRecDepth_446_);
                    leanh::lean_inc(v_nextMacroScope_445_);
                    leanh::lean_inc(v_usedQuotCtxts_444_);
                    leanh::lean_inc(v_scopes_443_);
                    leanh::lean_inc(v_messages_442_);
                    leanh::lean_inc(v_env_441_);
                    leanh::lean_dec(v___x_438_);
                    v___x_453_ = leanh::lean_box(0);
                    v_isShared_454_ = v_isSharedCheck_467_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_455_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_455_, 0, v_currNamespace_439_);
                leanh::lean_ctor_set(v___x_455_, 1, v_openDecls_440_);
                v___x_456_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_456_, 0, v___x_455_);
                leanh::lean_ctor_set(v___x_456_, 1, v___y_423_);
                leanh::lean_inc_ref(v___y_424_);
                leanh::lean_inc_ref(v___y_427_);
                v___x_457_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_457_, 0, v___y_427_);
                leanh::lean_ctor_set(v___x_457_, 1, v___y_426_);
                leanh::lean_ctor_set(v___x_457_, 2, v___y_425_);
                leanh::lean_ctor_set(v___x_457_, 3, v___y_424_);
                leanh::lean_ctor_set(v___x_457_, 4, v___x_456_);
                leanh::lean_ctor_set_uint8(
                    v___x_457_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___y_429_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_457_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_428_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_457_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_418_,
                );
                v___x_458_ = l_Lean_MessageLog_add(v___x_457_, v_messages_442_);
                if v_isShared_454_ == 0 {
                    leanh::lean_ctor_set(v___x_453_, 1, v___x_458_);
                    v___x_460_ = v___x_453_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_466_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_466_, 0, v_env_441_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_466_, 1, v___x_458_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_466_, 2, v_scopes_443_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_466_, 3, v_usedQuotCtxts_444_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_466_, 4, v_nextMacroScope_445_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_466_, 5, v_maxRecDepth_446_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_466_, 6, v_ngen_447_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_466_, 7, v_auxDeclNGen_448_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_466_, 8, v_infoState_449_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_466_, 9, v_traceState_450_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_466_, 10, v_snapshotTasks_451_);
                    v___x_460_ = v_reuseFailAlloc_466_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_461_ = lean_st_ref_set(v___y_430_, v___x_460_);
                v___x_462_ = leanh::lean_box(0);
                if v_isShared_437_ == 0 {
                    leanh::lean_ctor_set(v___x_436_, 0, v___x_462_);
                    v___x_464_ = v___x_436_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_465_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_462_);
                    v___x_464_ = v_reuseFailAlloc_465_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_464_;
            }
            6 => {
                if v_isShared_472_ == 0 {
                    v___x_474_ = v___x_471_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_475_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
                    v___x_474_ = v_reuseFailAlloc_475_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_474_;
            }
            8 => {
                if v_isShared_480_ == 0 {
                    v___x_482_ = v___x_479_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_483_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
                    v___x_482_ = v_reuseFailAlloc_483_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_482_;
            }
            10 => {
                v_fileName_491_ = leanh::lean_ctor_get(v___y_419_, 0);
                v_fileMap_492_ = leanh::lean_ctor_get(v___y_419_, 1);
                v_suppressElabErrors_493_ = leanh::lean_ctor_get_uint8(
                    v___y_419_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                );
                v___x_494_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_416_,
                    );
                v___x_495_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg(v___x_494_, v___y_420_);
                v_a_496_ = leanh::lean_ctor_get(v___x_495_, 0);
                v_isSharedCheck_512_ = (!leanh::lean_is_exclusive(v___x_495_)) as u8;
                if v_isSharedCheck_512_ == 0 {
                    v___x_498_ = v___x_495_;
                    v_isShared_499_ = v_isSharedCheck_512_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_inc(v_a_496_);
                    leanh::lean_dec(v___x_495_);
                    v___x_498_ = leanh::lean_box(0);
                    v_isShared_499_ = v_isSharedCheck_512_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                leanh::lean_inc_ref_n(v_fileMap_492_, 2);
                v___x_500_ = l_Lean_FileMap_toPosition(v_fileMap_492_, v___y_487_);
                leanh::lean_dec(v___y_487_);
                v___x_501_ = l_Lean_FileMap_toPosition(v_fileMap_492_, v___y_490_);
                leanh::lean_dec(v___y_490_);
                v___x_502_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_502_, 0, v___x_501_);
                v___x_503_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___closed__0;
                if v_suppressElabErrors_493_ == 0 {
                    leanh::lean_del_object(v___x_498_);
                    v___y_423_ = v_a_496_;
                    v___y_424_ = v___x_503_;
                    v___y_425_ = v___x_502_;
                    v___y_426_ = v___x_500_;
                    v___y_427_ = v_fileName_491_;
                    v___y_428_ = v___y_488_;
                    v___y_429_ = v___y_489_;
                    v___y_430_ = v___y_420_;
                    state = 1;
                    continue;
                } else {
                    v___x_504_ = leanh::lean_box((v___y_486_) as usize);
                    v___x_505_ = leanh::lean_box((v_suppressElabErrors_493_) as usize);
                    v___f_506_ = leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    leanh::lean_closure_set(v___f_506_, 0, v___x_504_);
                    leanh::lean_closure_set(v___f_506_, 1, v___x_505_);
                    leanh::lean_inc(v_a_496_);
                    v___x_507_ = l_Lean_MessageData_hasTag(v___f_506_, v_a_496_);
                    if v___x_507_ == 0 {
                        leanh::lean_dec_ref_known(v___x_502_, 1);
                        leanh::lean_dec_ref(v___x_500_);
                        leanh::lean_dec(v_a_496_);
                        v___x_508_ = leanh::lean_box(0);
                        if v_isShared_499_ == 0 {
                            leanh::lean_ctor_set(v___x_498_, 0, v___x_508_);
                            v___x_510_ = v___x_498_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_511_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
                            v___x_510_ = v_reuseFailAlloc_511_;
                            state = 12;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_498_);
                        v___y_423_ = v_a_496_;
                        v___y_424_ = v___x_503_;
                        v___y_425_ = v___x_502_;
                        v___y_426_ = v___x_500_;
                        v___y_427_ = v_fileName_491_;
                        v___y_428_ = v___y_488_;
                        v___y_429_ = v___y_489_;
                        v___y_430_ = v___y_420_;
                        state = 1;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_510_;
            }
            13 => {
                v___x_519_ = l_Lean_Syntax_getTailPos_x3f(v___y_515_, v___y_517_);
                leanh::lean_dec(v___y_515_);
                if leanh::lean_obj_tag(v___x_519_) == 0 {
                    leanh::lean_inc(v___y_518_);
                    v___y_486_ = v___y_514_;
                    v___y_487_ = v___y_518_;
                    v___y_488_ = v___y_516_;
                    v___y_489_ = v___y_517_;
                    v___y_490_ = v___y_518_;
                    state = 10;
                    continue;
                } else {
                    v_val_520_ = leanh::lean_ctor_get(v___x_519_, 0);
                    leanh::lean_inc(v_val_520_);
                    leanh::lean_dec_ref_known(v___x_519_, 1);
                    v___y_486_ = v___y_514_;
                    v___y_487_ = v___y_518_;
                    v___y_488_ = v___y_516_;
                    v___y_489_ = v___y_517_;
                    v___y_490_ = v_val_520_;
                    state = 10;
                    continue;
                }
            }
            14 => {
                v___x_525_ = l_Lean_Elab_Command_getRef___redArg(v___y_419_);
                if leanh::lean_obj_tag(v___x_525_) == 0 {
                    v_a_526_ = leanh::lean_ctor_get(v___x_525_, 0);
                    leanh::lean_inc(v_a_526_);
                    leanh::lean_dec_ref_known(v___x_525_, 1);
                    v_ref_527_ = l_Lean_replaceRef(v_ref_415_, v_a_526_);
                    leanh::lean_dec(v_a_526_);
                    v___x_528_ = l_Lean_Syntax_getPos_x3f(v_ref_527_, v___y_523_);
                    if leanh::lean_obj_tag(v___x_528_) == 0 {
                        v___x_529_ = leanh::lean_unsigned_to_nat(0);
                        v___y_514_ = v___y_522_;
                        v___y_515_ = v_ref_527_;
                        v___y_516_ = v___y_524_;
                        v___y_517_ = v___y_523_;
                        v___y_518_ = v___x_529_;
                        state = 13;
                        continue;
                    } else {
                        v_val_530_ = leanh::lean_ctor_get(v___x_528_, 0);
                        leanh::lean_inc(v_val_530_);
                        leanh::lean_dec_ref_known(v___x_528_, 1);
                        v___y_514_ = v___y_522_;
                        v___y_515_ = v_ref_527_;
                        v___y_516_ = v___y_524_;
                        v___y_517_ = v___y_523_;
                        v___y_518_ = v_val_530_;
                        state = 13;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msgData_416_);
                    v_a_531_ = leanh::lean_ctor_get(v___x_525_, 0);
                    v_isSharedCheck_538_ = (!leanh::lean_is_exclusive(v___x_525_)) as u8;
                    if v_isSharedCheck_538_ == 0 {
                        v___x_533_ = v___x_525_;
                        v_isShared_534_ = v_isSharedCheck_538_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_531_);
                        leanh::lean_dec(v___x_525_);
                        v___x_533_ = leanh::lean_box(0);
                        v_isShared_534_ = v_isSharedCheck_538_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_534_ == 0 {
                    v___x_536_ = v___x_533_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_537_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
                    v___x_536_ = v_reuseFailAlloc_537_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_536_;
            }
            17 => {
                if v___y_543_ == 0 {
                    v___y_522_ = v___y_541_;
                    v___y_523_ = v___y_542_;
                    v___y_524_ = v_severity_417_;
                    state = 14;
                    continue;
                } else {
                    v___y_522_ = v___y_541_;
                    v___y_523_ = v___y_542_;
                    v___y_524_ = v___x_539_;
                    state = 14;
                    continue;
                }
            }
            18 => {
                if v___y_545_ == 0 {
                    v___x_546_ = lean_st_ref_get(v___y_420_);
                    v_scopes_547_ = leanh::lean_ctor_get(v___x_546_, 2);
                    leanh::lean_inc(v_scopes_547_);
                    leanh::lean_dec(v___x_546_);
                    v___x_548_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_549_ = l_List_head_x21___redArg(v___x_548_, v_scopes_547_);
                    leanh::lean_dec(v_scopes_547_);
                    v_opts_550_ = leanh::lean_ctor_get(v___x_549_, 1);
                    leanh::lean_inc_ref(v_opts_550_);
                    leanh::lean_dec(v___x_549_);
                    v___x_551_ = 1;
                    v___x_552_ = l_Lean_instBEqMessageSeverity_beq(v_severity_417_, v___x_551_);
                    if v___x_552_ == 0 {
                        leanh::lean_dec_ref(v_opts_550_);
                        v___y_541_ = v___y_545_;
                        v___y_542_ = v___y_545_;
                        v___y_543_ = v___x_552_;
                        state = 17;
                        continue;
                    } else {
                        v___x_553_ = l_Lean_warningAsError;
                        v___x_554_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__3(v_opts_550_, v___x_553_);
                        leanh::lean_dec_ref(v_opts_550_);
                        v___y_541_ = v___y_545_;
                        v___y_542_ = v___y_545_;
                        v___y_543_ = v___x_554_;
                        state = 17;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msgData_416_);
                    v___x_555_ = leanh::lean_box(0);
                    v___x_556_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_556_, 0, v___x_555_);
                    return v___x_556_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1___boxed(
    mut v_ref_559_: *mut leanh::LeanObject,
    mut v_msgData_560_: *mut leanh::LeanObject,
    mut v_severity_561_: *mut leanh::LeanObject,
    mut v_isSilent_562_: *mut leanh::LeanObject,
    mut v___y_563_: *mut leanh::LeanObject,
    mut v___y_564_: *mut leanh::LeanObject,
    mut v___y_565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_566_: u8 = 0;
    let mut v_isSilent_boxed_567_: u8 = 0;
    let mut v_res_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_566_ = (leanh::lean_unbox(v_severity_561_) as u8);
    v_isSilent_boxed_567_ = (leanh::lean_unbox(v_isSilent_562_) as u8);
    v_res_568_ =
        l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1(
            v_ref_559_,
            v_msgData_560_,
            v_severity_boxed_566_,
            v_isSilent_boxed_567_,
            v___y_563_,
            v___y_564_,
        );
    leanh::lean_dec(v___y_564_);
    leanh::lean_dec_ref(v___y_563_);
    leanh::lean_dec(v_ref_559_);
    return v_res_568_;
}
pub unsafe fn l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1(
    mut v_ref_569_: *mut leanh::LeanObject,
    mut v_msgData_570_: *mut leanh::LeanObject,
    mut v___y_571_: *mut leanh::LeanObject,
    mut v___y_572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_574_: u8 = 0;
    let mut v___x_575_: u8 = 0;
    let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_574_ = 0;
    v___x_575_ = 0;
    v___x_576_ =
        l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1(
            v_ref_569_,
            v_msgData_570_,
            v___x_574_,
            v___x_575_,
            v___y_571_,
            v___y_572_,
        );
    return v___x_576_;
}
pub unsafe fn l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1___boxed(
    mut v_ref_577_: *mut leanh::LeanObject,
    mut v_msgData_578_: *mut leanh::LeanObject,
    mut v___y_579_: *mut leanh::LeanObject,
    mut v___y_580_: *mut leanh::LeanObject,
    mut v___y_581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_582_ = l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1(
        v_ref_577_,
        v_msgData_578_,
        v___y_579_,
        v___y_580_,
    );
    leanh::lean_dec(v___y_580_);
    leanh::lean_dec_ref(v___y_579_);
    leanh::lean_dec(v_ref_577_);
    return v_res_582_;
}
pub unsafe fn _init_l_Lean_Elab_Time_elabTimeCmd___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_591_ = l_Lean_Elab_Time_elabTimeCmd___closed__4;
    v___x_592_ = l_Lean_stringToMessageData(v___x_591_);
    return v___x_592_;
}
pub unsafe fn _init_l_Lean_Elab_Time_elabTimeCmd___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_594_ = l_Lean_Elab_Time_elabTimeCmd___closed__6;
    v___x_595_ = l_Lean_stringToMessageData(v___x_594_);
    return v___x_595_;
}
pub unsafe fn l_Lean_Elab_Time_elabTimeCmd(
    mut v_x_596_: *mut leanh::LeanObject,
    mut v_a_597_: *mut leanh::LeanObject,
    mut v_a_598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: u8 = 0;
    let mut v___x_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_609_: u8 = 0;
    let mut v___x_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_624_: u8 = 0;
    let mut v_unused_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_600_ = l_Lean_Elab_Time_elabTimeCmd___closed__3;
                leanh::lean_inc(v_x_596_);
                v___x_601_ = l_Lean_Syntax_isOfKind(v_x_596_, v___x_600_);
                if v___x_601_ == 0 {
                    leanh::lean_dec(v_x_596_);
                    v___x_602_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Time_elabTimeCmd_spec__0___redArg();
                    return v___x_602_;
                } else {
                    v___x_603_ = lean_io_mono_ms_now();
                    v___x_604_ = leanh::lean_unsigned_to_nat(1);
                    v___x_605_ = l_Lean_Syntax_getArg(v_x_596_, v___x_604_);
                    v___x_606_ = l_Lean_Elab_Command_elabCommand(v___x_605_, v_a_597_, v_a_598_);
                    if leanh::lean_obj_tag(v___x_606_) == 0 {
                        v_isSharedCheck_624_ = (!leanh::lean_is_exclusive(v___x_606_)) as u8;
                        if v_isSharedCheck_624_ == 0 {
                            v_unused_625_ = leanh::lean_ctor_get(v___x_606_, 0);
                            leanh::lean_dec(v_unused_625_);
                            v___x_608_ = v___x_606_;
                            v_isShared_609_ = v_isSharedCheck_624_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_606_);
                            v___x_608_ = leanh::lean_box(0);
                            v_isShared_609_ = v_isSharedCheck_624_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_603_);
                        leanh::lean_dec(v_x_596_);
                        return v___x_606_;
                    }
                }
            }
            1 => {
                v___x_610_ = lean_io_mono_ms_now();
                v___x_611_ = leanh::lean_unsigned_to_nat(0);
                v_tk_612_ = l_Lean_Syntax_getArg(v_x_596_, v___x_611_);
                leanh::lean_dec(v_x_596_);
                v___x_613_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Time_elabTimeCmd___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Time_elabTimeCmd___closed__5_once),
                    _init_l_Lean_Elab_Time_elabTimeCmd___closed__5,
                );
                v___x_614_ = lean_nat_sub(v___x_610_, v___x_603_);
                leanh::lean_dec(v___x_603_);
                leanh::lean_dec(v___x_610_);
                v___x_615_ = l_Nat_reprFast(v___x_614_);
                if v_isShared_609_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_608_, 3);
                    leanh::lean_ctor_set(v___x_608_, 0, v___x_615_);
                    v___x_617_ = v___x_608_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_623_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_615_);
                    v___x_617_ = v_reuseFailAlloc_623_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_618_ = l_Lean_MessageData_ofFormat(v___x_617_);
                v___x_619_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_619_, 0, v___x_613_);
                leanh::lean_ctor_set(v___x_619_, 1, v___x_618_);
                v___x_620_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Time_elabTimeCmd___closed__7),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Time_elabTimeCmd___closed__7_once),
                    _init_l_Lean_Elab_Time_elabTimeCmd___closed__7,
                );
                v___x_621_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_621_, 0, v___x_619_);
                leanh::lean_ctor_set(v___x_621_, 1, v___x_620_);
                v___x_622_ = l_Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1(
                    v_tk_612_, v___x_621_, v_a_597_, v_a_598_,
                );
                leanh::lean_dec(v_tk_612_);
                return v___x_622_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Time_elabTimeCmd___boxed(
    mut v_x_626_: *mut leanh::LeanObject,
    mut v_a_627_: *mut leanh::LeanObject,
    mut v_a_628_: *mut leanh::LeanObject,
    mut v_a_629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_630_ = l_Lean_Elab_Time_elabTimeCmd(v_x_626_, v_a_627_, v_a_628_);
    leanh::lean_dec(v_a_628_);
    leanh::lean_dec_ref(v_a_627_);
    return v_res_630_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2(
    mut v_msgData_631_: *mut leanh::LeanObject,
    mut v___y_632_: *mut leanh::LeanObject,
    mut v___y_633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_635_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___redArg(v_msgData_631_, v___y_633_);
    return v___x_635_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2___boxed(
    mut v_msgData_636_: *mut leanh::LeanObject,
    mut v___y_637_: *mut leanh::LeanObject,
    mut v___y_638_: *mut leanh::LeanObject,
    mut v___y_639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_640_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Time_elabTimeCmd_spec__1_spec__1_spec__2(v_msgData_636_, v___y_637_, v___y_638_);
    leanh::lean_dec(v___y_638_);
    leanh::lean_dec_ref(v___y_637_);
    return v_res_640_;
}
pub unsafe fn l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1()
-> *mut leanh::LeanObject {
    let mut v___x_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_650_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_651_ = l_Lean_Elab_Time_elabTimeCmd___closed__3;
    v___x_652_ = l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___closed__3;
    v___x_653_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Time_elabTimeCmd___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_654_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_650_, v___x_651_, v___x_652_, v___x_653_,
    );
    return v___x_654_;
}
pub unsafe fn l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1___boxed(
    mut v_a_655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_656_ = l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1();
    return v_res_656_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Time(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Time_0__Lean_Elab_Time_elabTimeCmd___regBuiltin_Lean_Elab_Time_elabTimeCmd__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Time(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Time(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Time(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Time(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Time(builtin);
}
// Lean compiler output
// Module: Lean.Elab.InfoTrees
// Imports: Lean.Elab.Command
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr2, l_Lean_Name_mkStr5, l_Lean_Syntax_getArg, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind, l_Lean_replaceRef,
};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
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
use crate::r#gen::Lean::Elab::InfoTree::Main::{
    l_Lean_Elab_InfoState_substituteLazy, l_Lean_Elab_InfoTree_format,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_ofFormat,
    l_Lean_MessageLog_add, l_Lean_instBEqMessageSeverity_beq,
};
use crate::lean_imports_rs::Init::Core::lean_task_get_own;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
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
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__1_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [105, 110, 102, 111, 84, 114, 101, 101, 115, 67, 109, 100, 0],
    };
static mut l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__1_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__1_value)
                as *mut LeanObject,
            7739505413878735095 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__3_value: LeanStringObject<52> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 52,
        m_capacity: 52,
        m_length: 51,
        m_data: [
            73, 110, 102, 111, 32, 116, 114, 101, 101, 115, 32, 97, 114, 101, 32, 100, 105, 115,
            97, 98, 108, 101, 100, 44, 32, 99, 97, 110, 32, 110, 111, 116, 32, 117, 115, 101, 32,
            96, 35, 105, 110, 102, 111, 95, 116, 114, 101, 101, 115, 96, 46, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__4_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__2_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [73, 110, 102, 111, 84, 114, 101, 101, 115, 0]};
static mut l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__3_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 108, 97, 98, 73, 110, 102, 111, 84, 114, 101, 101, 115, 0]};
static mut l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__3_value) as *mut LeanObject;
static l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__1_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__2_value) as *mut LeanObject,6423147367092110481 as *mut LeanObject] };
pub static l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__3_value) as *mut LeanObject,16504185875077482195 as *mut LeanObject] };
static mut l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    v___x_776_ = lean_box(0);
    v___x_777_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_778_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_778_, 0, v___x_777_);
    lean_ctor_set(v___x_778_, 1, v___x_776_);
    return v___x_778_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    v___x_780_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg___closed__0);
    v___x_781_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_781_, 0, v___x_780_);
    return v___x_781_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg___boxed(
    mut v___y_782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_783_: *mut LeanObject = core::ptr::null_mut();
    v_res_783_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg();
    return v_res_783_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0(
    mut v_00_u03b1_784_: *mut LeanObject,
    mut v___y_785_: *mut LeanObject,
    mut v___y_786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    v___x_788_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg();
    return v___x_788_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___boxed(
    mut v_00_u03b1_789_: *mut LeanObject,
    mut v___y_790_: *mut LeanObject,
    mut v___y_791_: *mut LeanObject,
    mut v___y_792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_793_: *mut LeanObject = core::ptr::null_mut();
    v_res_793_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0(v_00_u03b1_789_, v___y_790_, v___y_791_);
    lean_dec(v___y_791_);
    lean_dec_ref(v___y_790_);
    return v_res_793_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__3(
    mut v_opts_794_: *mut LeanObject,
    mut v_opt_795_: *mut LeanObject,
) -> u8 {
    let mut v_name_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    v_name_796_ = lean_ctor_get(v_opt_795_, 0);
    v_defValue_797_ = lean_ctor_get(v_opt_795_, 1);
    v_map_798_ = lean_ctor_get(v_opts_794_, 0);
    v___x_799_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_798_,
            v_name_796_,
        );
    if lean_obj_tag(v___x_799_) == 0 {
        let mut v___x_800_: u8 = 0;
        v___x_800_ = (lean_unbox(v_defValue_797_) as u8);
        return v___x_800_;
    } else {
        let mut v_val_801_: *mut LeanObject = core::ptr::null_mut();
        v_val_801_ = lean_ctor_get(v___x_799_, 0);
        lean_inc(v_val_801_);
        lean_dec_ref_known(v___x_799_, 1);
        if lean_obj_tag(v_val_801_) == 1 {
            let mut v_v_802_: u8 = 0;
            v_v_802_ = lean_ctor_get_uint8(v_val_801_, 0 as u32);
            lean_dec_ref_known(v_val_801_, 0);
            return v_v_802_;
        } else {
            let mut v___x_803_: u8 = 0;
            lean_dec(v_val_801_);
            v___x_803_ = (lean_unbox(v_defValue_797_) as u8);
            return v___x_803_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__3___boxed(
    mut v_opts_804_: *mut LeanObject,
    mut v_opt_805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_806_: u8 = 0;
    let mut v_r_807_: *mut LeanObject = core::ptr::null_mut();
    v_res_806_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__3(v_opts_804_, v_opt_805_);
    lean_dec_ref(v_opt_805_);
    lean_dec_ref(v_opts_804_);
    v_r_807_ = lean_box((v_res_806_) as usize);
    return v_r_807_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0(
    mut v___y_809_: u8,
    mut v_suppressElabErrors_810_: u8,
    mut v_x_811_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_811_) == 1 {
        let mut v_pre_812_: *mut LeanObject = core::ptr::null_mut();
        v_pre_812_ = lean_ctor_get(v_x_811_, 0);
        if lean_obj_tag(v_pre_812_) == 0 {
            let mut v_str_813_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_815_: u8 = 0;
            v_str_813_ = lean_ctor_get(v_x_811_, 1);
            v___x_814_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0___closed__0;
            v___x_815_ = lean_string_dec_eq(v_str_813_, v___x_814_);
            if v___x_815_ == 0 {
                return v___y_809_;
            } else {
                return v_suppressElabErrors_810_;
            }
        } else {
            return v___y_809_;
        }
    } else {
        return v___y_809_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0___boxed(
    mut v___y_816_: *mut LeanObject,
    mut v_suppressElabErrors_817_: *mut LeanObject,
    mut v_x_818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6638__boxed_819_: u8 = 0;
    let mut v_suppressElabErrors_boxed_820_: u8 = 0;
    let mut v_res_821_: u8 = 0;
    let mut v_r_822_: *mut LeanObject = core::ptr::null_mut();
    v___y_6638__boxed_819_ = (lean_unbox(v___y_816_) as u8);
    v_suppressElabErrors_boxed_820_ = (lean_unbox(v_suppressElabErrors_817_) as u8);
    v_res_821_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0(v___y_6638__boxed_819_, v_suppressElabErrors_boxed_820_, v_x_818_);
    lean_dec(v_x_818_);
    v_r_822_ = lean_box((v_res_821_) as usize);
    return v_r_822_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    v___x_823_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_823_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    v___x_824_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__0);
    v___x_825_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_825_, 0, v___x_824_);
    return v___x_825_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    v___x_826_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1);
    v___x_827_ = lean_unsigned_to_nat(0);
    v___x_828_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_828_, 0, v___x_827_);
    lean_ctor_set(v___x_828_, 1, v___x_827_);
    lean_ctor_set(v___x_828_, 2, v___x_827_);
    lean_ctor_set(v___x_828_, 3, v___x_827_);
    lean_ctor_set(v___x_828_, 4, v___x_826_);
    lean_ctor_set(v___x_828_, 5, v___x_826_);
    lean_ctor_set(v___x_828_, 6, v___x_826_);
    lean_ctor_set(v___x_828_, 7, v___x_826_);
    lean_ctor_set(v___x_828_, 8, v___x_826_);
    lean_ctor_set(v___x_828_, 9, v___x_826_);
    return v___x_828_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    v___x_829_ = lean_unsigned_to_nat(32);
    v___x_830_ = lean_mk_empty_array_with_capacity(v___x_829_);
    v___x_831_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_831_, 0, v___x_830_);
    return v___x_831_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_832_: usize = 0;
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
    v___x_832_ = 5usize;
    v___x_833_ = lean_unsigned_to_nat(0);
    v___x_834_ = lean_unsigned_to_nat(32);
    v___x_835_ = lean_mk_empty_array_with_capacity(v___x_834_);
    v___x_836_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__3);
    v___x_837_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_837_, 0, v___x_836_);
    lean_ctor_set(v___x_837_, 1, v___x_835_);
    lean_ctor_set(v___x_837_, 2, v___x_833_);
    lean_ctor_set(v___x_837_, 3, v___x_833_);
    lean_ctor_set_usize(v___x_837_, 4, v___x_832_);
    return v___x_837_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
    v___x_838_ = lean_box(1);
    v___x_839_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__4);
    v___x_840_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1);
    v___x_841_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_841_, 0, v___x_840_);
    lean_ctor_set(v___x_841_, 1, v___x_839_);
    lean_ctor_set(v___x_841_, 2, v___x_838_);
    return v___x_841_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg(
    mut v_msgData_842_: *mut LeanObject,
    mut v___y_843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    v___x_845_ = lean_st_ref_get(v___y_843_);
    v_env_846_ = lean_ctor_get(v___x_845_, 0);
    lean_inc_ref(v_env_846_);
    lean_dec(v___x_845_);
    v___x_847_ = lean_st_ref_get(v___y_843_);
    v_scopes_848_ = lean_ctor_get(v___x_847_, 2);
    lean_inc(v_scopes_848_);
    lean_dec(v___x_847_);
    v___x_849_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_850_ = l_List_head_x21___redArg(v___x_849_, v_scopes_848_);
    lean_dec(v_scopes_848_);
    v_opts_851_ = lean_ctor_get(v___x_850_, 1);
    lean_inc_ref(v_opts_851_);
    lean_dec(v___x_850_);
    v___x_852_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__2);
    v___x_853_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__5);
    v___x_854_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_854_, 0, v_env_846_);
    lean_ctor_set(v___x_854_, 1, v___x_852_);
    lean_ctor_set(v___x_854_, 2, v___x_853_);
    lean_ctor_set(v___x_854_, 3, v_opts_851_);
    v___x_855_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_855_, 0, v___x_854_);
    lean_ctor_set(v___x_855_, 1, v_msgData_842_);
    v___x_856_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_856_, 0, v___x_855_);
    return v___x_856_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_msgData_857_: *mut LeanObject,
    mut v___y_858_: *mut LeanObject,
    mut v___y_859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_860_: *mut LeanObject = core::ptr::null_mut();
    v_res_860_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg(v_msgData_857_, v___y_858_);
    lean_dec(v___y_858_);
    return v_res_860_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1(
    mut v_ref_862_: *mut LeanObject,
    mut v_msgData_863_: *mut LeanObject,
    mut v_severity_864_: u8,
    mut v_isSilent_865_: u8,
    mut v___y_866_: *mut LeanObject,
    mut v___y_867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_871_: u8 = 0;
    let mut v___y_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_875_: u8 = 0;
    let mut v___y_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_884_: u8 = 0;
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_901_: u8 = 0;
    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_914_: u8 = 0;
    let mut v_isSharedCheck_915_: u8 = 0;
    let mut v_a_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_919_: u8 = 0;
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_923_: u8 = 0;
    let mut v_a_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_927_: u8 = 0;
    let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_931_: u8 = 0;
    let mut v___y_933_: u8 = 0;
    let mut v___y_934_: u8 = 0;
    let mut v___y_935_: u8 = 0;
    let mut v___y_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_940_: u8 = 0;
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_946_: u8 = 0;
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_954_: u8 = 0;
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_959_: u8 = 0;
    let mut v___y_961_: u8 = 0;
    let mut v___y_962_: u8 = 0;
    let mut v___y_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_964_: u8 = 0;
    let mut v___y_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_969_: u8 = 0;
    let mut v___y_970_: u8 = 0;
    let mut v___y_971_: u8 = 0;
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_981_: u8 = 0;
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_985_: u8 = 0;
    let mut v___x_986_: u8 = 0;
    let mut v___y_988_: u8 = 0;
    let mut v___y_989_: u8 = 0;
    let mut v___y_990_: u8 = 0;
    let mut v___y_992_: u8 = 0;
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_998_: u8 = 0;
    let mut v___x_999_: u8 = 0;
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: u8 = 0;
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: u8 = 0;
    let mut v___x_1005_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_986_ = 2;
                v___x_1004_ = l_Lean_instBEqMessageSeverity_beq(v_severity_864_, v___x_986_);
                if v___x_1004_ == 0 {
                    v___y_992_ = v___x_1004_;
                    state = 18;
                    continue;
                } else {
                    lean_inc_ref(v_msgData_863_);
                    v___x_1005_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_863_);
                    v___y_992_ = v___x_1005_;
                    state = 18;
                    continue;
                }
            }
            1 => {
                v___x_878_ = l_Lean_Elab_Command_getScope___redArg(v___y_877_);
                if lean_obj_tag(v___x_878_) == 0 {
                    v_a_879_ = lean_ctor_get(v___x_878_, 0);
                    lean_inc(v_a_879_);
                    lean_dec_ref_known(v___x_878_, 1);
                    v___x_880_ = l_Lean_Elab_Command_getScope___redArg(v___y_877_);
                    if lean_obj_tag(v___x_880_) == 0 {
                        v_a_881_ = lean_ctor_get(v___x_880_, 0);
                        v_isSharedCheck_915_ = (!lean_is_exclusive(v___x_880_)) as u8;
                        if v_isSharedCheck_915_ == 0 {
                            v___x_883_ = v___x_880_;
                            v_isShared_884_ = v_isSharedCheck_915_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_881_);
                            lean_dec(v___x_880_);
                            v___x_883_ = lean_box(0);
                            v_isShared_884_ = v_isSharedCheck_915_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_879_);
                        lean_dec_ref(v___y_873_);
                        lean_dec_ref(v___y_872_);
                        lean_dec(v___y_870_);
                        v_a_916_ = lean_ctor_get(v___x_880_, 0);
                        v_isSharedCheck_923_ = (!lean_is_exclusive(v___x_880_)) as u8;
                        if v_isSharedCheck_923_ == 0 {
                            v___x_918_ = v___x_880_;
                            v_isShared_919_ = v_isSharedCheck_923_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_916_);
                            lean_dec(v___x_880_);
                            v___x_918_ = lean_box(0);
                            v_isShared_919_ = v_isSharedCheck_923_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_873_);
                    lean_dec_ref(v___y_872_);
                    lean_dec(v___y_870_);
                    v_a_924_ = lean_ctor_get(v___x_878_, 0);
                    v_isSharedCheck_931_ = (!lean_is_exclusive(v___x_878_)) as u8;
                    if v_isSharedCheck_931_ == 0 {
                        v___x_926_ = v___x_878_;
                        v_isShared_927_ = v_isSharedCheck_931_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_924_);
                        lean_dec(v___x_878_);
                        v___x_926_ = lean_box(0);
                        v_isShared_927_ = v_isSharedCheck_931_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_885_ = lean_st_ref_take(v___y_877_);
                v_currNamespace_886_ = lean_ctor_get(v_a_879_, 2);
                lean_inc(v_currNamespace_886_);
                lean_dec(v_a_879_);
                v_openDecls_887_ = lean_ctor_get(v_a_881_, 3);
                lean_inc(v_openDecls_887_);
                lean_dec(v_a_881_);
                v_env_888_ = lean_ctor_get(v___x_885_, 0);
                v_messages_889_ = lean_ctor_get(v___x_885_, 1);
                v_scopes_890_ = lean_ctor_get(v___x_885_, 2);
                v_usedQuotCtxts_891_ = lean_ctor_get(v___x_885_, 3);
                v_nextMacroScope_892_ = lean_ctor_get(v___x_885_, 4);
                v_maxRecDepth_893_ = lean_ctor_get(v___x_885_, 5);
                v_ngen_894_ = lean_ctor_get(v___x_885_, 6);
                v_auxDeclNGen_895_ = lean_ctor_get(v___x_885_, 7);
                v_infoState_896_ = lean_ctor_get(v___x_885_, 8);
                v_traceState_897_ = lean_ctor_get(v___x_885_, 9);
                v_snapshotTasks_898_ = lean_ctor_get(v___x_885_, 10);
                v_isSharedCheck_914_ = (!lean_is_exclusive(v___x_885_)) as u8;
                if v_isSharedCheck_914_ == 0 {
                    v___x_900_ = v___x_885_;
                    v_isShared_901_ = v_isSharedCheck_914_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_898_);
                    lean_inc(v_traceState_897_);
                    lean_inc(v_infoState_896_);
                    lean_inc(v_auxDeclNGen_895_);
                    lean_inc(v_ngen_894_);
                    lean_inc(v_maxRecDepth_893_);
                    lean_inc(v_nextMacroScope_892_);
                    lean_inc(v_usedQuotCtxts_891_);
                    lean_inc(v_scopes_890_);
                    lean_inc(v_messages_889_);
                    lean_inc(v_env_888_);
                    lean_dec(v___x_885_);
                    v___x_900_ = lean_box(0);
                    v_isShared_901_ = v_isSharedCheck_914_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_902_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_902_, 0, v_currNamespace_886_);
                lean_ctor_set(v___x_902_, 1, v_openDecls_887_);
                v___x_903_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_903_, 0, v___x_902_);
                lean_ctor_set(v___x_903_, 1, v___y_873_);
                lean_inc_ref(v___y_876_);
                lean_inc_ref(v___y_874_);
                v___x_904_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_904_, 0, v___y_874_);
                lean_ctor_set(v___x_904_, 1, v___y_872_);
                lean_ctor_set(v___x_904_, 2, v___y_870_);
                lean_ctor_set(v___x_904_, 3, v___y_876_);
                lean_ctor_set(v___x_904_, 4, v___x_903_);
                lean_ctor_set_uint8(
                    v___x_904_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_875_,
                );
                lean_ctor_set_uint8(
                    v___x_904_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_871_,
                );
                lean_ctor_set_uint8(
                    v___x_904_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_865_,
                );
                v___x_905_ = l_Lean_MessageLog_add(v___x_904_, v_messages_889_);
                if v_isShared_901_ == 0 {
                    lean_ctor_set(v___x_900_, 1, v___x_905_);
                    v___x_907_ = v___x_900_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_913_, 0, v_env_888_);
                    lean_ctor_set(v_reuseFailAlloc_913_, 1, v___x_905_);
                    lean_ctor_set(v_reuseFailAlloc_913_, 2, v_scopes_890_);
                    lean_ctor_set(v_reuseFailAlloc_913_, 3, v_usedQuotCtxts_891_);
                    lean_ctor_set(v_reuseFailAlloc_913_, 4, v_nextMacroScope_892_);
                    lean_ctor_set(v_reuseFailAlloc_913_, 5, v_maxRecDepth_893_);
                    lean_ctor_set(v_reuseFailAlloc_913_, 6, v_ngen_894_);
                    lean_ctor_set(v_reuseFailAlloc_913_, 7, v_auxDeclNGen_895_);
                    lean_ctor_set(v_reuseFailAlloc_913_, 8, v_infoState_896_);
                    lean_ctor_set(v_reuseFailAlloc_913_, 9, v_traceState_897_);
                    lean_ctor_set(v_reuseFailAlloc_913_, 10, v_snapshotTasks_898_);
                    v___x_907_ = v_reuseFailAlloc_913_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_908_ = lean_st_ref_set(v___y_877_, v___x_907_);
                v___x_909_ = lean_box(0);
                if v_isShared_884_ == 0 {
                    lean_ctor_set(v___x_883_, 0, v___x_909_);
                    v___x_911_ = v___x_883_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
                    v___x_911_ = v_reuseFailAlloc_912_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_911_;
            }
            6 => {
                if v_isShared_919_ == 0 {
                    v___x_921_ = v___x_918_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
                    v___x_921_ = v_reuseFailAlloc_922_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_921_;
            }
            8 => {
                if v_isShared_927_ == 0 {
                    v___x_929_ = v___x_926_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
                    v___x_929_ = v_reuseFailAlloc_930_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_929_;
            }
            10 => {
                v_fileName_938_ = lean_ctor_get(v___y_866_, 0);
                v_fileMap_939_ = lean_ctor_get(v___y_866_, 1);
                v_suppressElabErrors_940_ = lean_ctor_get_uint8(
                    v___y_866_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v___x_941_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_863_,
                    );
                v___x_942_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg(v___x_941_, v___y_867_);
                v_a_943_ = lean_ctor_get(v___x_942_, 0);
                v_isSharedCheck_959_ = (!lean_is_exclusive(v___x_942_)) as u8;
                if v_isSharedCheck_959_ == 0 {
                    v___x_945_ = v___x_942_;
                    v_isShared_946_ = v_isSharedCheck_959_;
                    state = 11;
                    continue;
                } else {
                    lean_inc(v_a_943_);
                    lean_dec(v___x_942_);
                    v___x_945_ = lean_box(0);
                    v_isShared_946_ = v_isSharedCheck_959_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                lean_inc_ref_n(v_fileMap_939_, 2);
                v___x_947_ = l_Lean_FileMap_toPosition(v_fileMap_939_, v___y_936_);
                lean_dec(v___y_936_);
                v___x_948_ = l_Lean_FileMap_toPosition(v_fileMap_939_, v___y_937_);
                lean_dec(v___y_937_);
                v___x_949_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_949_, 0, v___x_948_);
                v___x_950_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___closed__0;
                if v_suppressElabErrors_940_ == 0 {
                    lean_del_object(v___x_945_);
                    v___y_870_ = v___x_949_;
                    v___y_871_ = v___y_934_;
                    v___y_872_ = v___x_947_;
                    v___y_873_ = v_a_943_;
                    v___y_874_ = v_fileName_938_;
                    v___y_875_ = v___y_935_;
                    v___y_876_ = v___x_950_;
                    v___y_877_ = v___y_867_;
                    state = 1;
                    continue;
                } else {
                    v___x_951_ = lean_box((v___y_933_) as usize);
                    v___x_952_ = lean_box((v_suppressElabErrors_940_) as usize);
                    v___f_953_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_953_, 0, v___x_951_);
                    lean_closure_set(v___f_953_, 1, v___x_952_);
                    lean_inc(v_a_943_);
                    v___x_954_ = l_Lean_MessageData_hasTag(v___f_953_, v_a_943_);
                    if v___x_954_ == 0 {
                        lean_dec_ref_known(v___x_949_, 1);
                        lean_dec_ref(v___x_947_);
                        lean_dec(v_a_943_);
                        v___x_955_ = lean_box(0);
                        if v_isShared_946_ == 0 {
                            lean_ctor_set(v___x_945_, 0, v___x_955_);
                            v___x_957_ = v___x_945_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_955_);
                            v___x_957_ = v_reuseFailAlloc_958_;
                            state = 12;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_945_);
                        v___y_870_ = v___x_949_;
                        v___y_871_ = v___y_934_;
                        v___y_872_ = v___x_947_;
                        v___y_873_ = v_a_943_;
                        v___y_874_ = v_fileName_938_;
                        v___y_875_ = v___y_935_;
                        v___y_876_ = v___x_950_;
                        v___y_877_ = v___y_867_;
                        state = 1;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_957_;
            }
            13 => {
                v___x_966_ = l_Lean_Syntax_getTailPos_x3f(v___y_963_, v___y_964_);
                lean_dec(v___y_963_);
                if lean_obj_tag(v___x_966_) == 0 {
                    lean_inc(v___y_965_);
                    v___y_933_ = v___y_961_;
                    v___y_934_ = v___y_962_;
                    v___y_935_ = v___y_964_;
                    v___y_936_ = v___y_965_;
                    v___y_937_ = v___y_965_;
                    state = 10;
                    continue;
                } else {
                    v_val_967_ = lean_ctor_get(v___x_966_, 0);
                    lean_inc(v_val_967_);
                    lean_dec_ref_known(v___x_966_, 1);
                    v___y_933_ = v___y_961_;
                    v___y_934_ = v___y_962_;
                    v___y_935_ = v___y_964_;
                    v___y_936_ = v___y_965_;
                    v___y_937_ = v_val_967_;
                    state = 10;
                    continue;
                }
            }
            14 => {
                v___x_972_ = l_Lean_Elab_Command_getRef___redArg(v___y_866_);
                if lean_obj_tag(v___x_972_) == 0 {
                    v_a_973_ = lean_ctor_get(v___x_972_, 0);
                    lean_inc(v_a_973_);
                    lean_dec_ref_known(v___x_972_, 1);
                    v_ref_974_ = l_Lean_replaceRef(v_ref_862_, v_a_973_);
                    lean_dec(v_a_973_);
                    v___x_975_ = l_Lean_Syntax_getPos_x3f(v_ref_974_, v___y_970_);
                    if lean_obj_tag(v___x_975_) == 0 {
                        v___x_976_ = lean_unsigned_to_nat(0);
                        v___y_961_ = v___y_969_;
                        v___y_962_ = v___y_971_;
                        v___y_963_ = v_ref_974_;
                        v___y_964_ = v___y_970_;
                        v___y_965_ = v___x_976_;
                        state = 13;
                        continue;
                    } else {
                        v_val_977_ = lean_ctor_get(v___x_975_, 0);
                        lean_inc(v_val_977_);
                        lean_dec_ref_known(v___x_975_, 1);
                        v___y_961_ = v___y_969_;
                        v___y_962_ = v___y_971_;
                        v___y_963_ = v_ref_974_;
                        v___y_964_ = v___y_970_;
                        v___y_965_ = v_val_977_;
                        state = 13;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_863_);
                    v_a_978_ = lean_ctor_get(v___x_972_, 0);
                    v_isSharedCheck_985_ = (!lean_is_exclusive(v___x_972_)) as u8;
                    if v_isSharedCheck_985_ == 0 {
                        v___x_980_ = v___x_972_;
                        v_isShared_981_ = v_isSharedCheck_985_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_978_);
                        lean_dec(v___x_972_);
                        v___x_980_ = lean_box(0);
                        v_isShared_981_ = v_isSharedCheck_985_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_981_ == 0 {
                    v___x_983_ = v___x_980_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
                    v___x_983_ = v_reuseFailAlloc_984_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_983_;
            }
            17 => {
                if v___y_990_ == 0 {
                    v___y_969_ = v___y_988_;
                    v___y_970_ = v___y_989_;
                    v___y_971_ = v_severity_864_;
                    state = 14;
                    continue;
                } else {
                    v___y_969_ = v___y_988_;
                    v___y_970_ = v___y_989_;
                    v___y_971_ = v___x_986_;
                    state = 14;
                    continue;
                }
            }
            18 => {
                if v___y_992_ == 0 {
                    v___x_993_ = lean_st_ref_get(v___y_867_);
                    v_scopes_994_ = lean_ctor_get(v___x_993_, 2);
                    lean_inc(v_scopes_994_);
                    lean_dec(v___x_993_);
                    v___x_995_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_996_ = l_List_head_x21___redArg(v___x_995_, v_scopes_994_);
                    lean_dec(v_scopes_994_);
                    v_opts_997_ = lean_ctor_get(v___x_996_, 1);
                    lean_inc_ref(v_opts_997_);
                    lean_dec(v___x_996_);
                    v___x_998_ = 1;
                    v___x_999_ = l_Lean_instBEqMessageSeverity_beq(v_severity_864_, v___x_998_);
                    if v___x_999_ == 0 {
                        lean_dec_ref(v_opts_997_);
                        v___y_988_ = v___y_992_;
                        v___y_989_ = v___y_992_;
                        v___y_990_ = v___x_999_;
                        state = 17;
                        continue;
                    } else {
                        v___x_1000_ = l_Lean_warningAsError;
                        v___x_1001_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__3(v_opts_997_, v___x_1000_);
                        lean_dec_ref(v_opts_997_);
                        v___y_988_ = v___y_992_;
                        v___y_989_ = v___y_992_;
                        v___y_990_ = v___x_1001_;
                        state = 17;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_863_);
                    v___x_1002_ = lean_box(0);
                    v___x_1003_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1003_, 0, v___x_1002_);
                    return v___x_1003_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___boxed(
    mut v_ref_1006_: *mut LeanObject,
    mut v_msgData_1007_: *mut LeanObject,
    mut v_severity_1008_: *mut LeanObject,
    mut v_isSilent_1009_: *mut LeanObject,
    mut v___y_1010_: *mut LeanObject,
    mut v___y_1011_: *mut LeanObject,
    mut v___y_1012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_1013_: u8 = 0;
    let mut v_isSilent_boxed_1014_: u8 = 0;
    let mut v_res_1015_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_1013_ = (lean_unbox(v_severity_1008_) as u8);
    v_isSilent_boxed_1014_ = (lean_unbox(v_isSilent_1009_) as u8);
    v_res_1015_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1(v_ref_1006_, v_msgData_1007_, v_severity_boxed_1013_, v_isSilent_boxed_1014_, v___y_1010_, v___y_1011_);
    lean_dec(v___y_1011_);
    lean_dec_ref(v___y_1010_);
    lean_dec(v_ref_1006_);
    return v_res_1015_;
}
pub unsafe fn l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(
    mut v_ref_1016_: *mut LeanObject,
    mut v_msgData_1017_: *mut LeanObject,
    mut v___y_1018_: *mut LeanObject,
    mut v___y_1019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1021_: u8 = 0;
    let mut v___x_1022_: u8 = 0;
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    v___x_1021_ = 0;
    v___x_1022_ = 0;
    v___x_1023_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1(v_ref_1016_, v_msgData_1017_, v___x_1021_, v___x_1022_, v___y_1018_, v___y_1019_);
    return v___x_1023_;
}
pub unsafe fn l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1___boxed(
    mut v_ref_1024_: *mut LeanObject,
    mut v_msgData_1025_: *mut LeanObject,
    mut v___y_1026_: *mut LeanObject,
    mut v___y_1027_: *mut LeanObject,
    mut v___y_1028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1029_: *mut LeanObject = core::ptr::null_mut();
    v_res_1029_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(
        v_ref_1024_,
        v_msgData_1025_,
        v___y_1026_,
        v___y_1027_,
    );
    lean_dec(v___y_1027_);
    lean_dec_ref(v___y_1026_);
    lean_dec(v_ref_1024_);
    return v_res_1029_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9(
    mut v_tk_1033_: *mut LeanObject,
    mut v_as_1034_: *mut LeanObject,
    mut v_sz_1035_: usize,
    mut v_i_1036_: usize,
    mut v_b_1037_: *mut LeanObject,
    mut v___y_1038_: *mut LeanObject,
    mut v___y_1039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1041_: u8 = 0;
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: usize = 0;
    let mut v___x_1051_: usize = 0;
    let mut v_a_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1056_: u8 = 0;
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1060_: u8 = 0;
    let mut v_a_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1064_: u8 = 0;
    let mut v_ref_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1073_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1041_ = lean_usize_dec_lt(v_i_1036_, v_sz_1035_);
                if v___x_1041_ == 0 {
                    v___x_1042_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1042_, 0, v_b_1037_);
                    return v___x_1042_;
                } else {
                    lean_dec_ref(v_b_1037_);
                    v_a_1043_ = lean_array_uget_borrowed(v_as_1034_, v_i_1036_);
                    v___x_1044_ = lean_box(0);
                    lean_inc(v_a_1043_);
                    v___x_1045_ = l_Lean_Elab_InfoTree_format(v_a_1043_, v___x_1044_);
                    if lean_obj_tag(v___x_1045_) == 0 {
                        v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
                        lean_inc(v_a_1046_);
                        lean_dec_ref_known(v___x_1045_, 1);
                        v___x_1047_ = l_Lean_MessageData_ofFormat(v_a_1046_);
                        v___x_1048_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(v_tk_1033_, v___x_1047_, v___y_1038_, v___y_1039_);
                        if lean_obj_tag(v___x_1048_) == 0 {
                            lean_dec_ref_known(v___x_1048_, 1);
                            v___x_1049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9___closed__0;
                            v___x_1050_ = 1usize;
                            v___x_1051_ = lean_usize_add(v_i_1036_, v___x_1050_);
                            v_i_1036_ = v___x_1051_;
                            v_b_1037_ = v___x_1049_;
                            state = 0;
                            continue;
                        } else {
                            v_a_1053_ = lean_ctor_get(v___x_1048_, 0);
                            v_isSharedCheck_1060_ = (!lean_is_exclusive(v___x_1048_)) as u8;
                            if v_isSharedCheck_1060_ == 0 {
                                v___x_1055_ = v___x_1048_;
                                v_isShared_1056_ = v_isSharedCheck_1060_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1053_);
                                lean_dec(v___x_1048_);
                                v___x_1055_ = lean_box(0);
                                v_isShared_1056_ = v_isSharedCheck_1060_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v_a_1061_ = lean_ctor_get(v___x_1045_, 0);
                        v_isSharedCheck_1073_ = (!lean_is_exclusive(v___x_1045_)) as u8;
                        if v_isSharedCheck_1073_ == 0 {
                            v___x_1063_ = v___x_1045_;
                            v_isShared_1064_ = v_isSharedCheck_1073_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1061_);
                            lean_dec(v___x_1045_);
                            v___x_1063_ = lean_box(0);
                            v_isShared_1064_ = v_isSharedCheck_1073_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1056_ == 0 {
                    v___x_1058_ = v___x_1055_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
                    v___x_1058_ = v_reuseFailAlloc_1059_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1058_;
            }
            3 => {
                v_ref_1065_ = lean_ctor_get(v___y_1038_, 7);
                v___x_1066_ = lean_io_error_to_string(v_a_1061_);
                v___x_1067_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1067_, 0, v___x_1066_);
                v___x_1068_ = l_Lean_MessageData_ofFormat(v___x_1067_);
                lean_inc(v_ref_1065_);
                v___x_1069_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1069_, 0, v_ref_1065_);
                lean_ctor_set(v___x_1069_, 1, v___x_1068_);
                if v_isShared_1064_ == 0 {
                    lean_ctor_set(v___x_1063_, 0, v___x_1069_);
                    v___x_1071_ = v___x_1063_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1069_);
                    v___x_1071_ = v_reuseFailAlloc_1072_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1071_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9___boxed(
    mut v_tk_1074_: *mut LeanObject,
    mut v_as_1075_: *mut LeanObject,
    mut v_sz_1076_: *mut LeanObject,
    mut v_i_1077_: *mut LeanObject,
    mut v_b_1078_: *mut LeanObject,
    mut v___y_1079_: *mut LeanObject,
    mut v___y_1080_: *mut LeanObject,
    mut v___y_1081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1082_: usize = 0;
    let mut v_i_boxed_1083_: usize = 0;
    let mut v_res_1084_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1082_ = lean_unbox_usize(v_sz_1076_);
    lean_dec(v_sz_1076_);
    v_i_boxed_1083_ = lean_unbox_usize(v_i_1077_);
    lean_dec(v_i_1077_);
    v_res_1084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9(v_tk_1074_, v_as_1075_, v_sz_boxed_1082_, v_i_boxed_1083_, v_b_1078_, v___y_1079_, v___y_1080_);
    lean_dec(v___y_1080_);
    lean_dec_ref(v___y_1079_);
    lean_dec_ref(v_as_1075_);
    lean_dec(v_tk_1074_);
    return v_res_1084_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4(
    mut v_tk_1085_: *mut LeanObject,
    mut v_as_1086_: *mut LeanObject,
    mut v_sz_1087_: usize,
    mut v_i_1088_: usize,
    mut v_b_1089_: *mut LeanObject,
    mut v___y_1090_: *mut LeanObject,
    mut v___y_1091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1093_: u8 = 0;
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: usize = 0;
    let mut v___x_1103_: usize = 0;
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1108_: u8 = 0;
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1112_: u8 = 0;
    let mut v_a_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1116_: u8 = 0;
    let mut v_ref_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1125_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1093_ = lean_usize_dec_lt(v_i_1088_, v_sz_1087_);
                if v___x_1093_ == 0 {
                    v___x_1094_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1094_, 0, v_b_1089_);
                    return v___x_1094_;
                } else {
                    lean_dec_ref(v_b_1089_);
                    v_a_1095_ = lean_array_uget_borrowed(v_as_1086_, v_i_1088_);
                    v___x_1096_ = lean_box(0);
                    lean_inc(v_a_1095_);
                    v___x_1097_ = l_Lean_Elab_InfoTree_format(v_a_1095_, v___x_1096_);
                    if lean_obj_tag(v___x_1097_) == 0 {
                        v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
                        lean_inc(v_a_1098_);
                        lean_dec_ref_known(v___x_1097_, 1);
                        v___x_1099_ = l_Lean_MessageData_ofFormat(v_a_1098_);
                        v___x_1100_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(v_tk_1085_, v___x_1099_, v___y_1090_, v___y_1091_);
                        if lean_obj_tag(v___x_1100_) == 0 {
                            lean_dec_ref_known(v___x_1100_, 1);
                            v___x_1101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9___closed__0;
                            v___x_1102_ = 1usize;
                            v___x_1103_ = lean_usize_add(v_i_1088_, v___x_1102_);
                            v___x_1104_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9(v_tk_1085_, v_as_1086_, v_sz_1087_, v___x_1103_, v___x_1101_, v___y_1090_, v___y_1091_);
                            return v___x_1104_;
                        } else {
                            v_a_1105_ = lean_ctor_get(v___x_1100_, 0);
                            v_isSharedCheck_1112_ = (!lean_is_exclusive(v___x_1100_)) as u8;
                            if v_isSharedCheck_1112_ == 0 {
                                v___x_1107_ = v___x_1100_;
                                v_isShared_1108_ = v_isSharedCheck_1112_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1105_);
                                lean_dec(v___x_1100_);
                                v___x_1107_ = lean_box(0);
                                v_isShared_1108_ = v_isSharedCheck_1112_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v_a_1113_ = lean_ctor_get(v___x_1097_, 0);
                        v_isSharedCheck_1125_ = (!lean_is_exclusive(v___x_1097_)) as u8;
                        if v_isSharedCheck_1125_ == 0 {
                            v___x_1115_ = v___x_1097_;
                            v_isShared_1116_ = v_isSharedCheck_1125_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1113_);
                            lean_dec(v___x_1097_);
                            v___x_1115_ = lean_box(0);
                            v_isShared_1116_ = v_isSharedCheck_1125_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1108_ == 0 {
                    v___x_1110_ = v___x_1107_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
                    v___x_1110_ = v_reuseFailAlloc_1111_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1110_;
            }
            3 => {
                v_ref_1117_ = lean_ctor_get(v___y_1090_, 7);
                v___x_1118_ = lean_io_error_to_string(v_a_1113_);
                v___x_1119_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1119_, 0, v___x_1118_);
                v___x_1120_ = l_Lean_MessageData_ofFormat(v___x_1119_);
                lean_inc(v_ref_1117_);
                v___x_1121_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1121_, 0, v_ref_1117_);
                lean_ctor_set(v___x_1121_, 1, v___x_1120_);
                if v_isShared_1116_ == 0 {
                    lean_ctor_set(v___x_1115_, 0, v___x_1121_);
                    v___x_1123_ = v___x_1115_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
                    v___x_1123_ = v_reuseFailAlloc_1124_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1123_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4___boxed(
    mut v_tk_1126_: *mut LeanObject,
    mut v_as_1127_: *mut LeanObject,
    mut v_sz_1128_: *mut LeanObject,
    mut v_i_1129_: *mut LeanObject,
    mut v_b_1130_: *mut LeanObject,
    mut v___y_1131_: *mut LeanObject,
    mut v___y_1132_: *mut LeanObject,
    mut v___y_1133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1134_: usize = 0;
    let mut v_i_boxed_1135_: usize = 0;
    let mut v_res_1136_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1134_ = lean_unbox_usize(v_sz_1128_);
    lean_dec(v_sz_1128_);
    v_i_boxed_1135_ = lean_unbox_usize(v_i_1129_);
    lean_dec(v_i_1129_);
    v_res_1136_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4(v_tk_1126_, v_as_1127_, v_sz_boxed_1134_, v_i_boxed_1135_, v_b_1130_, v___y_1131_, v___y_1132_);
    lean_dec(v___y_1132_);
    lean_dec_ref(v___y_1131_);
    lean_dec_ref(v_as_1127_);
    lean_dec(v_tk_1126_);
    return v_res_1136_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9(
    mut v_tk_1140_: *mut LeanObject,
    mut v_as_1141_: *mut LeanObject,
    mut v_sz_1142_: usize,
    mut v_i_1143_: usize,
    mut v_b_1144_: *mut LeanObject,
    mut v___y_1145_: *mut LeanObject,
    mut v___y_1146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1148_: u8 = 0;
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: usize = 0;
    let mut v___x_1158_: usize = 0;
    let mut v_a_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1163_: u8 = 0;
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1167_: u8 = 0;
    let mut v_a_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1171_: u8 = 0;
    let mut v_ref_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1180_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1148_ = lean_usize_dec_lt(v_i_1143_, v_sz_1142_);
                if v___x_1148_ == 0 {
                    v___x_1149_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1149_, 0, v_b_1144_);
                    return v___x_1149_;
                } else {
                    lean_dec_ref(v_b_1144_);
                    v_a_1150_ = lean_array_uget_borrowed(v_as_1141_, v_i_1143_);
                    v___x_1151_ = lean_box(0);
                    lean_inc(v_a_1150_);
                    v___x_1152_ = l_Lean_Elab_InfoTree_format(v_a_1150_, v___x_1151_);
                    if lean_obj_tag(v___x_1152_) == 0 {
                        v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
                        lean_inc(v_a_1153_);
                        lean_dec_ref_known(v___x_1152_, 1);
                        v___x_1154_ = l_Lean_MessageData_ofFormat(v_a_1153_);
                        v___x_1155_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(v_tk_1140_, v___x_1154_, v___y_1145_, v___y_1146_);
                        if lean_obj_tag(v___x_1155_) == 0 {
                            lean_dec_ref_known(v___x_1155_, 1);
                            v___x_1156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9___closed__0;
                            v___x_1157_ = 1usize;
                            v___x_1158_ = lean_usize_add(v_i_1143_, v___x_1157_);
                            v_i_1143_ = v___x_1158_;
                            v_b_1144_ = v___x_1156_;
                            state = 0;
                            continue;
                        } else {
                            v_a_1160_ = lean_ctor_get(v___x_1155_, 0);
                            v_isSharedCheck_1167_ = (!lean_is_exclusive(v___x_1155_)) as u8;
                            if v_isSharedCheck_1167_ == 0 {
                                v___x_1162_ = v___x_1155_;
                                v_isShared_1163_ = v_isSharedCheck_1167_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1160_);
                                lean_dec(v___x_1155_);
                                v___x_1162_ = lean_box(0);
                                v_isShared_1163_ = v_isSharedCheck_1167_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v_a_1168_ = lean_ctor_get(v___x_1152_, 0);
                        v_isSharedCheck_1180_ = (!lean_is_exclusive(v___x_1152_)) as u8;
                        if v_isSharedCheck_1180_ == 0 {
                            v___x_1170_ = v___x_1152_;
                            v_isShared_1171_ = v_isSharedCheck_1180_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1168_);
                            lean_dec(v___x_1152_);
                            v___x_1170_ = lean_box(0);
                            v_isShared_1171_ = v_isSharedCheck_1180_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1163_ == 0 {
                    v___x_1165_ = v___x_1162_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
                    v___x_1165_ = v_reuseFailAlloc_1166_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1165_;
            }
            3 => {
                v_ref_1172_ = lean_ctor_get(v___y_1145_, 7);
                v___x_1173_ = lean_io_error_to_string(v_a_1168_);
                v___x_1174_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1174_, 0, v___x_1173_);
                v___x_1175_ = l_Lean_MessageData_ofFormat(v___x_1174_);
                lean_inc(v_ref_1172_);
                v___x_1176_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1176_, 0, v_ref_1172_);
                lean_ctor_set(v___x_1176_, 1, v___x_1175_);
                if v_isShared_1171_ == 0 {
                    lean_ctor_set(v___x_1170_, 0, v___x_1176_);
                    v___x_1178_ = v___x_1170_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
                    v___x_1178_ = v_reuseFailAlloc_1179_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1178_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9___boxed(
    mut v_tk_1181_: *mut LeanObject,
    mut v_as_1182_: *mut LeanObject,
    mut v_sz_1183_: *mut LeanObject,
    mut v_i_1184_: *mut LeanObject,
    mut v_b_1185_: *mut LeanObject,
    mut v___y_1186_: *mut LeanObject,
    mut v___y_1187_: *mut LeanObject,
    mut v___y_1188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1189_: usize = 0;
    let mut v_i_boxed_1190_: usize = 0;
    let mut v_res_1191_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1189_ = lean_unbox_usize(v_sz_1183_);
    lean_dec(v_sz_1183_);
    v_i_boxed_1190_ = lean_unbox_usize(v_i_1184_);
    lean_dec(v_i_1184_);
    v_res_1191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9(v_tk_1181_, v_as_1182_, v_sz_boxed_1189_, v_i_boxed_1190_, v_b_1185_, v___y_1186_, v___y_1187_);
    lean_dec(v___y_1187_);
    lean_dec_ref(v___y_1186_);
    lean_dec_ref(v_as_1182_);
    lean_dec(v_tk_1181_);
    return v_res_1191_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7(
    mut v_tk_1192_: *mut LeanObject,
    mut v_as_1193_: *mut LeanObject,
    mut v_sz_1194_: usize,
    mut v_i_1195_: usize,
    mut v_b_1196_: *mut LeanObject,
    mut v___y_1197_: *mut LeanObject,
    mut v___y_1198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1200_: u8 = 0;
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: usize = 0;
    let mut v___x_1210_: usize = 0;
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1215_: u8 = 0;
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1219_: u8 = 0;
    let mut v_a_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1223_: u8 = 0;
    let mut v_ref_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1232_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1200_ = lean_usize_dec_lt(v_i_1195_, v_sz_1194_);
                if v___x_1200_ == 0 {
                    v___x_1201_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1201_, 0, v_b_1196_);
                    return v___x_1201_;
                } else {
                    lean_dec_ref(v_b_1196_);
                    v_a_1202_ = lean_array_uget_borrowed(v_as_1193_, v_i_1195_);
                    v___x_1203_ = lean_box(0);
                    lean_inc(v_a_1202_);
                    v___x_1204_ = l_Lean_Elab_InfoTree_format(v_a_1202_, v___x_1203_);
                    if lean_obj_tag(v___x_1204_) == 0 {
                        v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
                        lean_inc(v_a_1205_);
                        lean_dec_ref_known(v___x_1204_, 1);
                        v___x_1206_ = l_Lean_MessageData_ofFormat(v_a_1205_);
                        v___x_1207_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(v_tk_1192_, v___x_1206_, v___y_1197_, v___y_1198_);
                        if lean_obj_tag(v___x_1207_) == 0 {
                            lean_dec_ref_known(v___x_1207_, 1);
                            v___x_1208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9___closed__0;
                            v___x_1209_ = 1usize;
                            v___x_1210_ = lean_usize_add(v_i_1195_, v___x_1209_);
                            v___x_1211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9(v_tk_1192_, v_as_1193_, v_sz_1194_, v___x_1210_, v___x_1208_, v___y_1197_, v___y_1198_);
                            return v___x_1211_;
                        } else {
                            v_a_1212_ = lean_ctor_get(v___x_1207_, 0);
                            v_isSharedCheck_1219_ = (!lean_is_exclusive(v___x_1207_)) as u8;
                            if v_isSharedCheck_1219_ == 0 {
                                v___x_1214_ = v___x_1207_;
                                v_isShared_1215_ = v_isSharedCheck_1219_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1212_);
                                lean_dec(v___x_1207_);
                                v___x_1214_ = lean_box(0);
                                v_isShared_1215_ = v_isSharedCheck_1219_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v_a_1220_ = lean_ctor_get(v___x_1204_, 0);
                        v_isSharedCheck_1232_ = (!lean_is_exclusive(v___x_1204_)) as u8;
                        if v_isSharedCheck_1232_ == 0 {
                            v___x_1222_ = v___x_1204_;
                            v_isShared_1223_ = v_isSharedCheck_1232_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1220_);
                            lean_dec(v___x_1204_);
                            v___x_1222_ = lean_box(0);
                            v_isShared_1223_ = v_isSharedCheck_1232_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1215_ == 0 {
                    v___x_1217_ = v___x_1214_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
                    v___x_1217_ = v_reuseFailAlloc_1218_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1217_;
            }
            3 => {
                v_ref_1224_ = lean_ctor_get(v___y_1197_, 7);
                v___x_1225_ = lean_io_error_to_string(v_a_1220_);
                v___x_1226_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1226_, 0, v___x_1225_);
                v___x_1227_ = l_Lean_MessageData_ofFormat(v___x_1226_);
                lean_inc(v_ref_1224_);
                v___x_1228_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1228_, 0, v_ref_1224_);
                lean_ctor_set(v___x_1228_, 1, v___x_1227_);
                if v_isShared_1223_ == 0 {
                    lean_ctor_set(v___x_1222_, 0, v___x_1228_);
                    v___x_1230_ = v___x_1222_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
                    v___x_1230_ = v_reuseFailAlloc_1231_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1230_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7___boxed(
    mut v_tk_1233_: *mut LeanObject,
    mut v_as_1234_: *mut LeanObject,
    mut v_sz_1235_: *mut LeanObject,
    mut v_i_1236_: *mut LeanObject,
    mut v_b_1237_: *mut LeanObject,
    mut v___y_1238_: *mut LeanObject,
    mut v___y_1239_: *mut LeanObject,
    mut v___y_1240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1241_: usize = 0;
    let mut v_i_boxed_1242_: usize = 0;
    let mut v_res_1243_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1241_ = lean_unbox_usize(v_sz_1235_);
    lean_dec(v_sz_1235_);
    v_i_boxed_1242_ = lean_unbox_usize(v_i_1236_);
    lean_dec(v_i_1236_);
    v_res_1243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7(v_tk_1233_, v_as_1234_, v_sz_boxed_1241_, v_i_boxed_1242_, v_b_1237_, v___y_1238_, v___y_1239_);
    lean_dec(v___y_1239_);
    lean_dec_ref(v___y_1238_);
    lean_dec_ref(v_as_1234_);
    lean_dec(v_tk_1233_);
    return v_res_1243_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(
    mut v_init_1244_: *mut LeanObject,
    mut v_tk_1245_: *mut LeanObject,
    mut v_n_1246_: *mut LeanObject,
    mut v_b_1247_: *mut LeanObject,
    mut v___y_1248_: *mut LeanObject,
    mut v___y_1249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1254_: usize = 0;
    let mut v___x_1255_: usize = 0;
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1260_: u8 = 0;
    let mut v_fst_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1271_: u8 = 0;
    let mut v_a_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1275_: u8 = 0;
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1279_: u8 = 0;
    let mut v_vs_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1283_: usize = 0;
    let mut v___x_1284_: usize = 0;
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1289_: u8 = 0;
    let mut v_fst_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1300_: u8 = 0;
    let mut v_a_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1304_: u8 = 0;
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1308_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_1246_) == 0 {
                    v_cs_1251_ = lean_ctor_get(v_n_1246_, 0);
                    v___x_1252_ = lean_box(0);
                    v___x_1253_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1253_, 0, v___x_1252_);
                    lean_ctor_set(v___x_1253_, 1, v_b_1247_);
                    v_sz_1254_ = lean_array_size(v_cs_1251_);
                    v___x_1255_ = 0usize;
                    v___x_1256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__6(v_init_1244_, v_tk_1245_, v_cs_1251_, v_sz_1254_, v___x_1255_, v___x_1253_, v___y_1248_, v___y_1249_);
                    if lean_obj_tag(v___x_1256_) == 0 {
                        v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
                        v_isSharedCheck_1271_ = (!lean_is_exclusive(v___x_1256_)) as u8;
                        if v_isSharedCheck_1271_ == 0 {
                            v___x_1259_ = v___x_1256_;
                            v_isShared_1260_ = v_isSharedCheck_1271_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1257_);
                            lean_dec(v___x_1256_);
                            v___x_1259_ = lean_box(0);
                            v_isShared_1260_ = v_isSharedCheck_1271_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1272_ = lean_ctor_get(v___x_1256_, 0);
                        v_isSharedCheck_1279_ = (!lean_is_exclusive(v___x_1256_)) as u8;
                        if v_isSharedCheck_1279_ == 0 {
                            v___x_1274_ = v___x_1256_;
                            v_isShared_1275_ = v_isSharedCheck_1279_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_1272_);
                            lean_dec(v___x_1256_);
                            v___x_1274_ = lean_box(0);
                            v_isShared_1275_ = v_isSharedCheck_1279_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_1280_ = lean_ctor_get(v_n_1246_, 0);
                    v___x_1281_ = lean_box(0);
                    v___x_1282_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1282_, 0, v___x_1281_);
                    lean_ctor_set(v___x_1282_, 1, v_b_1247_);
                    v_sz_1283_ = lean_array_size(v_vs_1280_);
                    v___x_1284_ = 0usize;
                    v___x_1285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7(v_tk_1245_, v_vs_1280_, v_sz_1283_, v___x_1284_, v___x_1282_, v___y_1248_, v___y_1249_);
                    if lean_obj_tag(v___x_1285_) == 0 {
                        v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
                        v_isSharedCheck_1300_ = (!lean_is_exclusive(v___x_1285_)) as u8;
                        if v_isSharedCheck_1300_ == 0 {
                            v___x_1288_ = v___x_1285_;
                            v_isShared_1289_ = v_isSharedCheck_1300_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_1286_);
                            lean_dec(v___x_1285_);
                            v___x_1288_ = lean_box(0);
                            v_isShared_1289_ = v_isSharedCheck_1300_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_1301_ = lean_ctor_get(v___x_1285_, 0);
                        v_isSharedCheck_1308_ = (!lean_is_exclusive(v___x_1285_)) as u8;
                        if v_isSharedCheck_1308_ == 0 {
                            v___x_1303_ = v___x_1285_;
                            v_isShared_1304_ = v_isSharedCheck_1308_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_1301_);
                            lean_dec(v___x_1285_);
                            v___x_1303_ = lean_box(0);
                            v_isShared_1304_ = v_isSharedCheck_1308_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_1261_ = lean_ctor_get(v_a_1257_, 0);
                if lean_obj_tag(v_fst_1261_) == 0 {
                    v_snd_1262_ = lean_ctor_get(v_a_1257_, 1);
                    lean_inc(v_snd_1262_);
                    lean_dec(v_a_1257_);
                    v___x_1263_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1263_, 0, v_snd_1262_);
                    if v_isShared_1260_ == 0 {
                        lean_ctor_set(v___x_1259_, 0, v___x_1263_);
                        v___x_1265_ = v___x_1259_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1263_);
                        v___x_1265_ = v_reuseFailAlloc_1266_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_1261_);
                    lean_dec(v_a_1257_);
                    v_val_1267_ = lean_ctor_get(v_fst_1261_, 0);
                    lean_inc(v_val_1267_);
                    lean_dec_ref_known(v_fst_1261_, 1);
                    if v_isShared_1260_ == 0 {
                        lean_ctor_set(v___x_1259_, 0, v_val_1267_);
                        v___x_1269_ = v___x_1259_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_val_1267_);
                        v___x_1269_ = v_reuseFailAlloc_1270_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1265_;
            }
            3 => {
                return v___x_1269_;
            }
            4 => {
                if v_isShared_1275_ == 0 {
                    v___x_1277_ = v___x_1274_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
                    v___x_1277_ = v_reuseFailAlloc_1278_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1277_;
            }
            6 => {
                v_fst_1290_ = lean_ctor_get(v_a_1286_, 0);
                if lean_obj_tag(v_fst_1290_) == 0 {
                    v_snd_1291_ = lean_ctor_get(v_a_1286_, 1);
                    lean_inc(v_snd_1291_);
                    lean_dec(v_a_1286_);
                    v___x_1292_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1292_, 0, v_snd_1291_);
                    if v_isShared_1289_ == 0 {
                        lean_ctor_set(v___x_1288_, 0, v___x_1292_);
                        v___x_1294_ = v___x_1288_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1292_);
                        v___x_1294_ = v_reuseFailAlloc_1295_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_1290_);
                    lean_dec(v_a_1286_);
                    v_val_1296_ = lean_ctor_get(v_fst_1290_, 0);
                    lean_inc(v_val_1296_);
                    lean_dec_ref_known(v_fst_1290_, 1);
                    if v_isShared_1289_ == 0 {
                        lean_ctor_set(v___x_1288_, 0, v_val_1296_);
                        v___x_1298_ = v___x_1288_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_val_1296_);
                        v___x_1298_ = v_reuseFailAlloc_1299_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_1294_;
            }
            8 => {
                return v___x_1298_;
            }
            9 => {
                if v_isShared_1304_ == 0 {
                    v___x_1306_ = v___x_1303_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
                    v___x_1306_ = v_reuseFailAlloc_1307_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1306_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__6(
    mut v_init_1309_: *mut LeanObject,
    mut v_tk_1310_: *mut LeanObject,
    mut v_as_1311_: *mut LeanObject,
    mut v_sz_1312_: usize,
    mut v_i_1313_: usize,
    mut v_b_1314_: *mut LeanObject,
    mut v___y_1315_: *mut LeanObject,
    mut v___y_1316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1318_: u8 = 0;
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1323_: u8 = 0;
    let mut v_a_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1329_: u8 = 0;
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: usize = 0;
    let mut v___x_1342_: usize = 0;
    let mut v_reuseFailAlloc_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1345_: u8 = 0;
    let mut v_a_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1349_: u8 = 0;
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1353_: u8 = 0;
    let mut v_isSharedCheck_1354_: u8 = 0;
    let mut v_unused_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1318_ = lean_usize_dec_lt(v_i_1313_, v_sz_1312_);
                if v___x_1318_ == 0 {
                    v___x_1319_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1319_, 0, v_b_1314_);
                    return v___x_1319_;
                } else {
                    v_snd_1320_ = lean_ctor_get(v_b_1314_, 1);
                    v_isSharedCheck_1354_ = (!lean_is_exclusive(v_b_1314_)) as u8;
                    if v_isSharedCheck_1354_ == 0 {
                        v_unused_1355_ = lean_ctor_get(v_b_1314_, 0);
                        lean_dec(v_unused_1355_);
                        v___x_1322_ = v_b_1314_;
                        v_isShared_1323_ = v_isSharedCheck_1354_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_1320_);
                        lean_dec(v_b_1314_);
                        v___x_1322_ = lean_box(0);
                        v_isShared_1323_ = v_isSharedCheck_1354_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_1324_ = lean_array_uget_borrowed(v_as_1311_, v_i_1313_);
                lean_inc(v_snd_1320_);
                v___x_1325_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(v_init_1309_, v_tk_1310_, v_a_1324_, v_snd_1320_, v___y_1315_, v___y_1316_);
                if lean_obj_tag(v___x_1325_) == 0 {
                    v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
                    v_isSharedCheck_1345_ = (!lean_is_exclusive(v___x_1325_)) as u8;
                    if v_isSharedCheck_1345_ == 0 {
                        v___x_1328_ = v___x_1325_;
                        v_isShared_1329_ = v_isSharedCheck_1345_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1326_);
                        lean_dec(v___x_1325_);
                        v___x_1328_ = lean_box(0);
                        v_isShared_1329_ = v_isSharedCheck_1345_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1322_);
                    lean_dec(v_snd_1320_);
                    v_a_1346_ = lean_ctor_get(v___x_1325_, 0);
                    v_isSharedCheck_1353_ = (!lean_is_exclusive(v___x_1325_)) as u8;
                    if v_isSharedCheck_1353_ == 0 {
                        v___x_1348_ = v___x_1325_;
                        v_isShared_1349_ = v_isSharedCheck_1353_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_1346_);
                        lean_dec(v___x_1325_);
                        v___x_1348_ = lean_box(0);
                        v_isShared_1349_ = v_isSharedCheck_1353_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_1326_) == 0 {
                    v___x_1330_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1330_, 0, v_a_1326_);
                    if v_isShared_1323_ == 0 {
                        lean_ctor_set(v___x_1322_, 0, v___x_1330_);
                        v___x_1332_ = v___x_1322_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1330_);
                        lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_snd_1320_);
                        v___x_1332_ = v_reuseFailAlloc_1336_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1328_);
                    lean_dec(v_snd_1320_);
                    v_a_1337_ = lean_ctor_get(v_a_1326_, 0);
                    lean_inc(v_a_1337_);
                    lean_dec_ref_known(v_a_1326_, 1);
                    v___x_1338_ = lean_box(0);
                    if v_isShared_1323_ == 0 {
                        lean_ctor_set(v___x_1322_, 1, v_a_1337_);
                        lean_ctor_set(v___x_1322_, 0, v___x_1338_);
                        v___x_1340_ = v___x_1322_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1338_);
                        lean_ctor_set(v_reuseFailAlloc_1344_, 1, v_a_1337_);
                        v___x_1340_ = v_reuseFailAlloc_1344_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1329_ == 0 {
                    lean_ctor_set(v___x_1328_, 0, v___x_1332_);
                    v___x_1334_ = v___x_1328_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1332_);
                    v___x_1334_ = v_reuseFailAlloc_1335_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1334_;
            }
            5 => {
                v___x_1341_ = 1usize;
                v___x_1342_ = lean_usize_add(v_i_1313_, v___x_1341_);
                v_i_1313_ = v___x_1342_;
                v_b_1314_ = v___x_1340_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_1349_ == 0 {
                    v___x_1351_ = v___x_1348_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
                    v___x_1351_ = v_reuseFailAlloc_1352_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1351_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__6___boxed(
    mut v_init_1356_: *mut LeanObject,
    mut v_tk_1357_: *mut LeanObject,
    mut v_as_1358_: *mut LeanObject,
    mut v_sz_1359_: *mut LeanObject,
    mut v_i_1360_: *mut LeanObject,
    mut v_b_1361_: *mut LeanObject,
    mut v___y_1362_: *mut LeanObject,
    mut v___y_1363_: *mut LeanObject,
    mut v___y_1364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1365_: usize = 0;
    let mut v_i_boxed_1366_: usize = 0;
    let mut v_res_1367_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1365_ = lean_unbox_usize(v_sz_1359_);
    lean_dec(v_sz_1359_);
    v_i_boxed_1366_ = lean_unbox_usize(v_i_1360_);
    lean_dec(v_i_1360_);
    v_res_1367_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__6(v_init_1356_, v_tk_1357_, v_as_1358_, v_sz_boxed_1365_, v_i_boxed_1366_, v_b_1361_, v___y_1362_, v___y_1363_);
    lean_dec(v___y_1363_);
    lean_dec_ref(v___y_1362_);
    lean_dec_ref(v_as_1358_);
    lean_dec(v_tk_1357_);
    return v_res_1367_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___boxed(
    mut v_init_1368_: *mut LeanObject,
    mut v_tk_1369_: *mut LeanObject,
    mut v_n_1370_: *mut LeanObject,
    mut v_b_1371_: *mut LeanObject,
    mut v___y_1372_: *mut LeanObject,
    mut v___y_1373_: *mut LeanObject,
    mut v___y_1374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1375_: *mut LeanObject = core::ptr::null_mut();
    v_res_1375_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(v_init_1368_, v_tk_1369_, v_n_1370_, v_b_1371_, v___y_1372_, v___y_1373_);
    lean_dec(v___y_1373_);
    lean_dec_ref(v___y_1372_);
    lean_dec_ref(v_n_1370_);
    lean_dec(v_tk_1369_);
    return v_res_1375_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(
    mut v_tk_1376_: *mut LeanObject,
    mut v_t_1377_: *mut LeanObject,
    mut v_init_1378_: *mut LeanObject,
    mut v___y_1379_: *mut LeanObject,
    mut v___y_1380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1388_: u8 = 0;
    let mut v_a_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1396_: usize = 0;
    let mut v___x_1397_: usize = 0;
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1402_: u8 = 0;
    let mut v_fst_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1412_: u8 = 0;
    let mut v_a_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1416_: u8 = 0;
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1420_: u8 = 0;
    let mut v_isSharedCheck_1421_: u8 = 0;
    let mut v_a_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1425_: u8 = 0;
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1429_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_1382_ = lean_ctor_get(v_t_1377_, 0);
                v_tail_1383_ = lean_ctor_get(v_t_1377_, 1);
                v___x_1384_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(v_init_1378_, v_tk_1376_, v_root_1382_, v_init_1378_, v___y_1379_, v___y_1380_);
                if lean_obj_tag(v___x_1384_) == 0 {
                    v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
                    v_isSharedCheck_1421_ = (!lean_is_exclusive(v___x_1384_)) as u8;
                    if v_isSharedCheck_1421_ == 0 {
                        v___x_1387_ = v___x_1384_;
                        v_isShared_1388_ = v_isSharedCheck_1421_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1385_);
                        lean_dec(v___x_1384_);
                        v___x_1387_ = lean_box(0);
                        v_isShared_1388_ = v_isSharedCheck_1421_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1422_ = lean_ctor_get(v___x_1384_, 0);
                    v_isSharedCheck_1429_ = (!lean_is_exclusive(v___x_1384_)) as u8;
                    if v_isSharedCheck_1429_ == 0 {
                        v___x_1424_ = v___x_1384_;
                        v_isShared_1425_ = v_isSharedCheck_1429_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_1422_);
                        lean_dec(v___x_1384_);
                        v___x_1424_ = lean_box(0);
                        v_isShared_1425_ = v_isSharedCheck_1429_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1385_) == 0 {
                    v_a_1389_ = lean_ctor_get(v_a_1385_, 0);
                    lean_inc(v_a_1389_);
                    lean_dec_ref_known(v_a_1385_, 1);
                    if v_isShared_1388_ == 0 {
                        lean_ctor_set(v___x_1387_, 0, v_a_1389_);
                        v___x_1391_ = v___x_1387_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1389_);
                        v___x_1391_ = v_reuseFailAlloc_1392_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1387_);
                    v_a_1393_ = lean_ctor_get(v_a_1385_, 0);
                    lean_inc(v_a_1393_);
                    lean_dec_ref_known(v_a_1385_, 1);
                    v___x_1394_ = lean_box(0);
                    v___x_1395_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1395_, 0, v___x_1394_);
                    lean_ctor_set(v___x_1395_, 1, v_a_1393_);
                    v_sz_1396_ = lean_array_size(v_tail_1383_);
                    v___x_1397_ = 0usize;
                    v___x_1398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4(v_tk_1376_, v_tail_1383_, v_sz_1396_, v___x_1397_, v___x_1395_, v___y_1379_, v___y_1380_);
                    if lean_obj_tag(v___x_1398_) == 0 {
                        v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
                        v_isSharedCheck_1412_ = (!lean_is_exclusive(v___x_1398_)) as u8;
                        if v_isSharedCheck_1412_ == 0 {
                            v___x_1401_ = v___x_1398_;
                            v_isShared_1402_ = v_isSharedCheck_1412_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1399_);
                            lean_dec(v___x_1398_);
                            v___x_1401_ = lean_box(0);
                            v_isShared_1402_ = v_isSharedCheck_1412_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1413_ = lean_ctor_get(v___x_1398_, 0);
                        v_isSharedCheck_1420_ = (!lean_is_exclusive(v___x_1398_)) as u8;
                        if v_isSharedCheck_1420_ == 0 {
                            v___x_1415_ = v___x_1398_;
                            v_isShared_1416_ = v_isSharedCheck_1420_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_1413_);
                            lean_dec(v___x_1398_);
                            v___x_1415_ = lean_box(0);
                            v_isShared_1416_ = v_isSharedCheck_1420_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1391_;
            }
            3 => {
                v_fst_1403_ = lean_ctor_get(v_a_1399_, 0);
                if lean_obj_tag(v_fst_1403_) == 0 {
                    v_snd_1404_ = lean_ctor_get(v_a_1399_, 1);
                    lean_inc(v_snd_1404_);
                    lean_dec(v_a_1399_);
                    if v_isShared_1402_ == 0 {
                        lean_ctor_set(v___x_1401_, 0, v_snd_1404_);
                        v___x_1406_ = v___x_1401_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_snd_1404_);
                        v___x_1406_ = v_reuseFailAlloc_1407_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_1403_);
                    lean_dec(v_a_1399_);
                    v_val_1408_ = lean_ctor_get(v_fst_1403_, 0);
                    lean_inc(v_val_1408_);
                    lean_dec_ref_known(v_fst_1403_, 1);
                    if v_isShared_1402_ == 0 {
                        lean_ctor_set(v___x_1401_, 0, v_val_1408_);
                        v___x_1410_ = v___x_1401_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_val_1408_);
                        v___x_1410_ = v_reuseFailAlloc_1411_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1406_;
            }
            5 => {
                return v___x_1410_;
            }
            6 => {
                if v_isShared_1416_ == 0 {
                    v___x_1418_ = v___x_1415_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
                    v___x_1418_ = v_reuseFailAlloc_1419_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1418_;
            }
            8 => {
                if v_isShared_1425_ == 0 {
                    v___x_1427_ = v___x_1424_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
                    v___x_1427_ = v_reuseFailAlloc_1428_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1427_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2___boxed(
    mut v_tk_1430_: *mut LeanObject,
    mut v_t_1431_: *mut LeanObject,
    mut v_init_1432_: *mut LeanObject,
    mut v___y_1433_: *mut LeanObject,
    mut v___y_1434_: *mut LeanObject,
    mut v___y_1435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1436_: *mut LeanObject = core::ptr::null_mut();
    v_res_1436_ =
        l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(
            v_tk_1430_,
            v_t_1431_,
            v_init_1432_,
            v___y_1433_,
            v___y_1434_,
        );
    lean_dec(v___y_1434_);
    lean_dec_ref(v___y_1433_);
    lean_dec_ref(v_t_1431_);
    lean_dec(v_tk_1430_);
    return v_res_1436_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6(
    mut v_msgData_1437_: *mut LeanObject,
    mut v_severity_1438_: u8,
    mut v_isSilent_1439_: u8,
    mut v___y_1440_: *mut LeanObject,
    mut v___y_1441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1449_: u8 = 0;
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1453_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1443_ = l_Lean_Elab_Command_getRef___redArg(v___y_1440_);
                if lean_obj_tag(v___x_1443_) == 0 {
                    v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
                    lean_inc(v_a_1444_);
                    lean_dec_ref_known(v___x_1443_, 1);
                    v___x_1445_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1(v_a_1444_, v_msgData_1437_, v_severity_1438_, v_isSilent_1439_, v___y_1440_, v___y_1441_);
                    lean_dec(v_a_1444_);
                    return v___x_1445_;
                } else {
                    lean_dec_ref(v_msgData_1437_);
                    v_a_1446_ = lean_ctor_get(v___x_1443_, 0);
                    v_isSharedCheck_1453_ = (!lean_is_exclusive(v___x_1443_)) as u8;
                    if v_isSharedCheck_1453_ == 0 {
                        v___x_1448_ = v___x_1443_;
                        v_isShared_1449_ = v_isSharedCheck_1453_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1446_);
                        lean_dec(v___x_1443_);
                        v___x_1448_ = lean_box(0);
                        v_isShared_1449_ = v_isSharedCheck_1453_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1449_ == 0 {
                    v___x_1451_ = v___x_1448_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
                    v___x_1451_ = v_reuseFailAlloc_1452_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1451_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6___boxed(
    mut v_msgData_1454_: *mut LeanObject,
    mut v_severity_1455_: *mut LeanObject,
    mut v_isSilent_1456_: *mut LeanObject,
    mut v___y_1457_: *mut LeanObject,
    mut v___y_1458_: *mut LeanObject,
    mut v___y_1459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_1460_: u8 = 0;
    let mut v_isSilent_boxed_1461_: u8 = 0;
    let mut v_res_1462_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_1460_ = (lean_unbox(v_severity_1455_) as u8);
    v_isSilent_boxed_1461_ = (lean_unbox(v_isSilent_1456_) as u8);
    v_res_1462_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6(v_msgData_1454_, v_severity_boxed_1460_, v_isSilent_boxed_1461_, v___y_1457_, v___y_1458_);
    lean_dec(v___y_1458_);
    lean_dec_ref(v___y_1457_);
    return v_res_1462_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(
    mut v_msgData_1463_: *mut LeanObject,
    mut v___y_1464_: *mut LeanObject,
    mut v___y_1465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1467_: u8 = 0;
    let mut v___x_1468_: u8 = 0;
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    v___x_1467_ = 2;
    v___x_1468_ = 0;
    v___x_1469_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6(v_msgData_1463_, v___x_1467_, v___x_1468_, v___y_1464_, v___y_1465_);
    return v___x_1469_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3___boxed(
    mut v_msgData_1470_: *mut LeanObject,
    mut v___y_1471_: *mut LeanObject,
    mut v___y_1472_: *mut LeanObject,
    mut v___y_1473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1474_: *mut LeanObject = core::ptr::null_mut();
    v_res_1474_ = l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(
        v_msgData_1470_,
        v___y_1471_,
        v___y_1472_,
    );
    lean_dec(v___y_1472_);
    lean_dec_ref(v___y_1471_);
    return v_res_1474_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5() -> *mut LeanObject {
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    v___x_1483_ = l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__4;
    v___x_1484_ = l_Lean_MessageData_ofFormat(v___x_1483_);
    return v___x_1484_;
}
pub unsafe fn l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees(
    mut v_x_1485_: *mut LeanObject,
    mut v_a_1486_: *mut LeanObject,
    mut v_a_1487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: u8 = 0;
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_1494_: u8 = 0;
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1510_: u8 = 0;
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1514_: u8 = 0;
    let mut v_unused_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1489_ = l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__2;
                lean_inc(v_x_1485_);
                v___x_1490_ = l_Lean_Syntax_isOfKind(v_x_1485_, v___x_1489_);
                if v___x_1490_ == 0 {
                    lean_dec(v_x_1485_);
                    v___x_1491_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg();
                    return v___x_1491_;
                } else {
                    v___x_1492_ = lean_st_ref_get(v_a_1487_);
                    v_infoState_1493_ = lean_ctor_get(v___x_1492_, 8);
                    lean_inc_ref(v_infoState_1493_);
                    lean_dec(v___x_1492_);
                    v_enabled_1494_ = lean_ctor_get_uint8(
                        v_infoState_1493_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    lean_dec_ref(v_infoState_1493_);
                    v___x_1495_ = lean_unsigned_to_nat(0);
                    v_tk_1496_ = l_Lean_Syntax_getArg(v_x_1485_, v___x_1495_);
                    v___x_1497_ = lean_unsigned_to_nat(2);
                    v___x_1498_ = l_Lean_Syntax_getArg(v_x_1485_, v___x_1497_);
                    lean_dec(v_x_1485_);
                    if v_enabled_1494_ == 0 {
                        if v___x_1490_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_1498_);
                            lean_dec(v_tk_1496_);
                            v___x_1516_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5_once
                                ),
                                _init_l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5,
                            );
                            v___x_1517_ = l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(v___x_1516_, v_a_1486_, v_a_1487_);
                            return v___x_1517_;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1500_ = l_Lean_Elab_Command_elabCommand(v___x_1498_, v_a_1486_, v_a_1487_);
                if lean_obj_tag(v___x_1500_) == 0 {
                    lean_dec_ref_known(v___x_1500_, 1);
                    v___x_1501_ = lean_st_ref_get(v_a_1487_);
                    v_infoState_1502_ = lean_ctor_get(v___x_1501_, 8);
                    lean_inc_ref(v_infoState_1502_);
                    lean_dec(v___x_1501_);
                    v___x_1503_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_1502_);
                    v___x_1504_ = lean_task_get_own(v___x_1503_);
                    v_trees_1505_ = lean_ctor_get(v___x_1504_, 2);
                    lean_inc_ref(v_trees_1505_);
                    lean_dec(v___x_1504_);
                    v___x_1506_ = lean_box(0);
                    v___x_1507_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(v_tk_1496_, v_trees_1505_, v___x_1506_, v_a_1486_, v_a_1487_);
                    lean_dec_ref(v_trees_1505_);
                    lean_dec(v_tk_1496_);
                    if lean_obj_tag(v___x_1507_) == 0 {
                        v_isSharedCheck_1514_ = (!lean_is_exclusive(v___x_1507_)) as u8;
                        if v_isSharedCheck_1514_ == 0 {
                            v_unused_1515_ = lean_ctor_get(v___x_1507_, 0);
                            lean_dec(v_unused_1515_);
                            v___x_1509_ = v___x_1507_;
                            v_isShared_1510_ = v_isSharedCheck_1514_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_1507_);
                            v___x_1509_ = lean_box(0);
                            v_isShared_1510_ = v_isSharedCheck_1514_;
                            state = 2;
                            continue;
                        }
                    } else {
                        return v___x_1507_;
                    }
                } else {
                    lean_dec(v_tk_1496_);
                    return v___x_1500_;
                }
            }
            2 => {
                if v_isShared_1510_ == 0 {
                    lean_ctor_set(v___x_1509_, 0, v___x_1506_);
                    v___x_1512_ = v___x_1509_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1506_);
                    v___x_1512_ = v_reuseFailAlloc_1513_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1512_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___boxed(
    mut v_x_1518_: *mut LeanObject,
    mut v_a_1519_: *mut LeanObject,
    mut v_a_1520_: *mut LeanObject,
    mut v_a_1521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1522_: *mut LeanObject = core::ptr::null_mut();
    v_res_1522_ = l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees(v_x_1518_, v_a_1519_, v_a_1520_);
    lean_dec(v_a_1520_);
    lean_dec_ref(v_a_1519_);
    return v_res_1522_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2(
    mut v_msgData_1523_: *mut LeanObject,
    mut v___y_1524_: *mut LeanObject,
    mut v___y_1525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    v___x_1527_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg(v_msgData_1523_, v___y_1525_);
    return v___x_1527_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___boxed(
    mut v_msgData_1528_: *mut LeanObject,
    mut v___y_1529_: *mut LeanObject,
    mut v___y_1530_: *mut LeanObject,
    mut v___y_1531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1532_: *mut LeanObject = core::ptr::null_mut();
    v_res_1532_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2(v_msgData_1528_, v___y_1529_, v___y_1530_);
    lean_dec(v___y_1530_);
    lean_dec_ref(v___y_1529_);
    return v_res_1532_;
}
pub unsafe fn l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1()
-> *mut LeanObject {
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    v___x_1544_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_1545_ = l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__2;
    v___x_1546_ = l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4;
    v___x_1547_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_1548_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1544_,
        v___x_1545_,
        v___x_1546_,
        v___x_1547_,
    );
    return v___x_1548_;
}
pub unsafe fn l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___boxed(
    mut v_a_1549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1550_: *mut LeanObject = core::ptr::null_mut();
    v_res_1550_ = l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1();
    return v_res_1550_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_InfoTrees(builtin: u8) -> *mut LeanObject {
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
    res = l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_InfoTrees(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_InfoTrees(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Lean_Elab_InfoTrees(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_InfoTrees(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_InfoTrees(builtin);
}

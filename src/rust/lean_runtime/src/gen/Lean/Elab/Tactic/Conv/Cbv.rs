// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Cbv
// Imports: Lean.Meta.Tactic.Cbv Lean.Elab.Tactic.Conv.Basic
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr5, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::Conv::Basic::{
    initialize_Lean_Elab_Tactic_Conv_Basic, l_Lean_Elab_Tactic_Conv_getLhs___redArg,
    l_Lean_Elab_Tactic_Conv_updateLhs, runtime_initialize_Lean_Elab_Tactic_Conv_Basic,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_ofFormat,
    l_Lean_MessageLog_add, l_Lean_instBEqMessageSeverity_beq,
};
use crate::r#gen::Lean::Meta::Tactic::Cbv::Main::{
    l_Lean_Meta_Tactic_Cbv_cbv_warning, l_Lean_Meta_Tactic_Cbv_cbvEntry,
};
use crate::r#gen::Lean::Meta::Tactic::Cbv::{
    initialize_Lean_Meta_Tactic_Cbv, runtime_initialize_Lean_Meta_Tactic_Cbv,
};
use crate::lean_imports_rs::Init::Prelude::lean_string_dec_eq;
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__3_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__5_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__6_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__7_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__7_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__0_value: LeanStringObject<97> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 97,
        m_capacity: 97,
        m_length: 96,
        m_data: [
            84, 104, 101, 32, 96, 99, 98, 118, 96, 32, 117, 115, 97, 103, 101, 32, 119, 97, 114,
            110, 105, 110, 103, 32, 111, 112, 116, 105, 111, 110, 32, 105, 115, 32, 101, 110, 97,
            98, 108, 101, 100, 46, 32, 68, 105, 115, 97, 98, 108, 101, 32, 105, 116, 32, 98, 121,
            32, 115, 101, 116, 116, 105, 110, 103, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105,
            111, 110, 32, 99, 98, 118, 46, 119, 97, 114, 110, 105, 110, 103, 32, 102, 97, 108, 115,
            101, 96, 46, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [67, 111, 110, 118, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__3_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [99, 98, 118, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__3_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__2_value) as *mut LeanObject,2622230176999461939 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__3_value) as *mut LeanObject,12057338954073742905 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__5_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [101, 118, 97, 108, 67, 98, 118, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__5_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__2_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__5_value) as *mut LeanObject,13629570598098759553 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6_value) as *mut LeanObject;
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0(
    mut v_opts_388_: *mut LeanObject,
    mut v_opt_389_: *mut LeanObject,
) -> u8 {
    let mut v_name_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
    v_name_390_ = lean_ctor_get(v_opt_389_, 0);
    v_defValue_391_ = lean_ctor_get(v_opt_389_, 1);
    v_map_392_ = lean_ctor_get(v_opts_388_, 0);
    v___x_393_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_392_,
            v_name_390_,
        );
    if lean_obj_tag(v___x_393_) == 0 {
        let mut v___x_394_: u8 = 0;
        v___x_394_ = (lean_unbox(v_defValue_391_) as u8);
        return v___x_394_;
    } else {
        let mut v_val_395_: *mut LeanObject = core::ptr::null_mut();
        v_val_395_ = lean_ctor_get(v___x_393_, 0);
        lean_inc(v_val_395_);
        lean_dec_ref_known(v___x_393_, 1);
        if lean_obj_tag(v_val_395_) == 1 {
            let mut v_v_396_: u8 = 0;
            v_v_396_ = lean_ctor_get_uint8(v_val_395_, 0 as u32);
            lean_dec_ref_known(v_val_395_, 0);
            return v_v_396_;
        } else {
            let mut v___x_397_: u8 = 0;
            lean_dec(v_val_395_);
            v___x_397_ = (lean_unbox(v_defValue_391_) as u8);
            return v___x_397_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0___boxed(
    mut v_opts_398_: *mut LeanObject,
    mut v_opt_399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_400_: u8 = 0;
    let mut v_r_401_: *mut LeanObject = core::ptr::null_mut();
    v_res_400_ =
        l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0(v_opts_398_, v_opt_399_);
    lean_dec_ref(v_opt_399_);
    lean_dec_ref(v_opts_398_);
    v_r_401_ = lean_box((v_res_400_) as usize);
    return v_r_401_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1_spec__2(
    mut v_msgData_402_: *mut LeanObject,
    mut v___y_403_: *mut LeanObject,
    mut v___y_404_: *mut LeanObject,
    mut v___y_405_: *mut LeanObject,
    mut v___y_406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
    v___x_408_ = lean_st_ref_get(v___y_406_);
    v_env_409_ = lean_ctor_get(v___x_408_, 0);
    lean_inc_ref(v_env_409_);
    lean_dec(v___x_408_);
    v___x_410_ = lean_st_ref_get(v___y_404_);
    v_mctx_411_ = lean_ctor_get(v___x_410_, 0);
    lean_inc_ref(v_mctx_411_);
    lean_dec(v___x_410_);
    v_lctx_412_ = lean_ctor_get(v___y_403_, 2);
    v_options_413_ = lean_ctor_get(v___y_405_, 2);
    lean_inc_ref(v_options_413_);
    lean_inc_ref(v_lctx_412_);
    v___x_414_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_414_, 0, v_env_409_);
    lean_ctor_set(v___x_414_, 1, v_mctx_411_);
    lean_ctor_set(v___x_414_, 2, v_lctx_412_);
    lean_ctor_set(v___x_414_, 3, v_options_413_);
    v___x_415_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_415_, 0, v___x_414_);
    lean_ctor_set(v___x_415_, 1, v_msgData_402_);
    v___x_416_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_416_, 0, v___x_415_);
    return v___x_416_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1_spec__2___boxed(
    mut v_msgData_417_: *mut LeanObject,
    mut v___y_418_: *mut LeanObject,
    mut v___y_419_: *mut LeanObject,
    mut v___y_420_: *mut LeanObject,
    mut v___y_421_: *mut LeanObject,
    mut v___y_422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_423_: *mut LeanObject = core::ptr::null_mut();
    v_res_423_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1_spec__2(v_msgData_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
    lean_dec(v___y_421_);
    lean_dec_ref(v___y_420_);
    lean_dec(v___y_419_);
    lean_dec_ref(v___y_418_);
    return v_res_423_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0(
    mut v___y_432_: u8,
    mut v_suppressElabErrors_433_: u8,
    mut v_x_434_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_434_) == 1 {
        let mut v_pre_435_: *mut LeanObject = core::ptr::null_mut();
        v_pre_435_ = lean_ctor_get(v_x_434_, 0);
        match lean_obj_tag(v_pre_435_) {
            1 => {
                let mut v_pre_436_: *mut LeanObject = core::ptr::null_mut();
                v_pre_436_ = lean_ctor_get(v_pre_435_, 0);
                match lean_obj_tag(v_pre_436_) {
                    0 => {
                        let mut v_str_437_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_str_438_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_440_: u8 = 0;
                        v_str_437_ = lean_ctor_get(v_x_434_, 1);
                        v_str_438_ = lean_ctor_get(v_pre_435_, 1);
                        v___x_439_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__0;
                        v___x_440_ = lean_string_dec_eq(v_str_438_, v___x_439_);
                        if v___x_440_ == 0 {
                            let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_442_: u8 = 0;
                            v___x_441_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__1;
                            v___x_442_ = lean_string_dec_eq(v_str_438_, v___x_441_);
                            if v___x_442_ == 0 {
                                return v___y_432_;
                            } else {
                                let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_444_: u8 = 0;
                                v___x_443_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__2;
                                v___x_444_ = lean_string_dec_eq(v_str_437_, v___x_443_);
                                if v___x_444_ == 0 {
                                    return v___y_432_;
                                } else {
                                    return v_suppressElabErrors_433_;
                                }
                            }
                        } else {
                            let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_446_: u8 = 0;
                            v___x_445_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__3;
                            v___x_446_ = lean_string_dec_eq(v_str_437_, v___x_445_);
                            if v___x_446_ == 0 {
                                return v___y_432_;
                            } else {
                                return v_suppressElabErrors_433_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_447_: *mut LeanObject = core::ptr::null_mut();
                        v_pre_447_ = lean_ctor_get(v_pre_436_, 0);
                        if lean_obj_tag(v_pre_447_) == 0 {
                            let mut v_str_448_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_449_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_450_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_452_: u8 = 0;
                            v_str_448_ = lean_ctor_get(v_x_434_, 1);
                            v_str_449_ = lean_ctor_get(v_pre_435_, 1);
                            v_str_450_ = lean_ctor_get(v_pre_436_, 1);
                            v___x_451_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__4;
                            v___x_452_ = lean_string_dec_eq(v_str_450_, v___x_451_);
                            if v___x_452_ == 0 {
                                return v___y_432_;
                            } else {
                                let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_454_: u8 = 0;
                                v___x_453_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__5;
                                v___x_454_ = lean_string_dec_eq(v_str_449_, v___x_453_);
                                if v___x_454_ == 0 {
                                    return v___y_432_;
                                } else {
                                    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_456_: u8 = 0;
                                    v___x_455_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__6;
                                    v___x_456_ = lean_string_dec_eq(v_str_448_, v___x_455_);
                                    if v___x_456_ == 0 {
                                        return v___y_432_;
                                    } else {
                                        return v_suppressElabErrors_433_;
                                    }
                                }
                            }
                        } else {
                            return v___y_432_;
                        }
                    }
                    _ => {
                        return v___y_432_;
                    }
                }
            }
            0 => {
                let mut v_str_457_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_459_: u8 = 0;
                v_str_457_ = lean_ctor_get(v_x_434_, 1);
                v___x_458_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___closed__7;
                v___x_459_ = lean_string_dec_eq(v_str_457_, v___x_458_);
                if v___x_459_ == 0 {
                    return v___y_432_;
                } else {
                    return v_suppressElabErrors_433_;
                }
            }
            _ => {
                return v___y_432_;
            }
        }
    } else {
        return v___y_432_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___boxed(
    mut v___y_460_: *mut LeanObject,
    mut v_suppressElabErrors_461_: *mut LeanObject,
    mut v_x_462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4772__boxed_463_: u8 = 0;
    let mut v_suppressElabErrors_boxed_464_: u8 = 0;
    let mut v_res_465_: u8 = 0;
    let mut v_r_466_: *mut LeanObject = core::ptr::null_mut();
    v___y_4772__boxed_463_ = (lean_unbox(v___y_460_) as u8);
    v_suppressElabErrors_boxed_464_ = (lean_unbox(v_suppressElabErrors_461_) as u8);
    v_res_465_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0(v___y_4772__boxed_463_, v_suppressElabErrors_boxed_464_, v_x_462_);
    lean_dec(v_x_462_);
    v_r_466_ = lean_box((v_res_465_) as usize);
    return v_r_466_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg(
    mut v_ref_468_: *mut LeanObject,
    mut v_msgData_469_: *mut LeanObject,
    mut v_severity_470_: u8,
    mut v_isSilent_471_: u8,
    mut v___y_472_: *mut LeanObject,
    mut v___y_473_: *mut LeanObject,
    mut v___y_474_: *mut LeanObject,
    mut v___y_475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_481_: u8 = 0;
    let mut v___y_482_: u8 = 0;
    let mut v___y_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_501_: u8 = 0;
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_512_: u8 = 0;
    let mut v___y_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_518_: u8 = 0;
    let mut v___y_519_: u8 = 0;
    let mut v___y_520_: u8 = 0;
    let mut v___y_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_527_: u8 = 0;
    let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_532_: u8 = 0;
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_537_: u8 = 0;
    let mut v___y_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_543_: u8 = 0;
    let mut v___y_544_: u8 = 0;
    let mut v___y_545_: u8 = 0;
    let mut v___y_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_554_: u8 = 0;
    let mut v___y_555_: u8 = 0;
    let mut v___y_556_: u8 = 0;
    let mut v_ref_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_561_: u8 = 0;
    let mut v___y_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_567_: u8 = 0;
    let mut v___y_568_: u8 = 0;
    let mut v___y_569_: u8 = 0;
    let mut v___y_571_: u8 = 0;
    let mut v_fileName_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_576_: u8 = 0;
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_580_: u8 = 0;
    let mut v___x_581_: u8 = 0;
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_583_: u8 = 0;
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: u8 = 0;
    let mut v___x_587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_561_ = 2;
                v___x_586_ = l_Lean_instBEqMessageSeverity_beq(v_severity_470_, v___x_561_);
                if v___x_586_ == 0 {
                    v___y_571_ = v___x_586_;
                    state = 10;
                    continue;
                } else {
                    lean_inc_ref(v_msgData_469_);
                    v___x_587_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_469_);
                    v___y_571_ = v___x_587_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_487_ = lean_st_ref_take(v___y_486_);
                v_currNamespace_488_ = lean_ctor_get(v___y_485_, 6);
                v_openDecls_489_ = lean_ctor_get(v___y_485_, 7);
                v_env_490_ = lean_ctor_get(v___x_487_, 0);
                v_nextMacroScope_491_ = lean_ctor_get(v___x_487_, 1);
                v_ngen_492_ = lean_ctor_get(v___x_487_, 2);
                v_auxDeclNGen_493_ = lean_ctor_get(v___x_487_, 3);
                v_traceState_494_ = lean_ctor_get(v___x_487_, 4);
                v_cache_495_ = lean_ctor_get(v___x_487_, 5);
                v_messages_496_ = lean_ctor_get(v___x_487_, 6);
                v_infoState_497_ = lean_ctor_get(v___x_487_, 7);
                v_snapshotTasks_498_ = lean_ctor_get(v___x_487_, 8);
                v_isSharedCheck_512_ = (!lean_is_exclusive(v___x_487_)) as u8;
                if v_isSharedCheck_512_ == 0 {
                    v___x_500_ = v___x_487_;
                    v_isShared_501_ = v_isSharedCheck_512_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_498_);
                    lean_inc(v_infoState_497_);
                    lean_inc(v_messages_496_);
                    lean_inc(v_cache_495_);
                    lean_inc(v_traceState_494_);
                    lean_inc(v_auxDeclNGen_493_);
                    lean_inc(v_ngen_492_);
                    lean_inc(v_nextMacroScope_491_);
                    lean_inc(v_env_490_);
                    lean_dec(v___x_487_);
                    v___x_500_ = lean_box(0);
                    v_isShared_501_ = v_isSharedCheck_512_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_openDecls_489_);
                lean_inc(v_currNamespace_488_);
                v___x_502_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_502_, 0, v_currNamespace_488_);
                lean_ctor_set(v___x_502_, 1, v_openDecls_489_);
                v___x_503_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_503_, 0, v___x_502_);
                lean_ctor_set(v___x_503_, 1, v___y_480_);
                lean_inc_ref(v___y_479_);
                lean_inc_ref(v___y_478_);
                v___x_504_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_504_, 0, v___y_478_);
                lean_ctor_set(v___x_504_, 1, v___y_484_);
                lean_ctor_set(v___x_504_, 2, v___y_483_);
                lean_ctor_set(v___x_504_, 3, v___y_479_);
                lean_ctor_set(v___x_504_, 4, v___x_503_);
                lean_ctor_set_uint8(
                    v___x_504_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_482_,
                );
                lean_ctor_set_uint8(
                    v___x_504_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_481_,
                );
                lean_ctor_set_uint8(
                    v___x_504_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_471_,
                );
                v___x_505_ = l_Lean_MessageLog_add(v___x_504_, v_messages_496_);
                if v_isShared_501_ == 0 {
                    lean_ctor_set(v___x_500_, 6, v___x_505_);
                    v___x_507_ = v___x_500_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_511_, 0, v_env_490_);
                    lean_ctor_set(v_reuseFailAlloc_511_, 1, v_nextMacroScope_491_);
                    lean_ctor_set(v_reuseFailAlloc_511_, 2, v_ngen_492_);
                    lean_ctor_set(v_reuseFailAlloc_511_, 3, v_auxDeclNGen_493_);
                    lean_ctor_set(v_reuseFailAlloc_511_, 4, v_traceState_494_);
                    lean_ctor_set(v_reuseFailAlloc_511_, 5, v_cache_495_);
                    lean_ctor_set(v_reuseFailAlloc_511_, 6, v___x_505_);
                    lean_ctor_set(v_reuseFailAlloc_511_, 7, v_infoState_497_);
                    lean_ctor_set(v_reuseFailAlloc_511_, 8, v_snapshotTasks_498_);
                    v___x_507_ = v_reuseFailAlloc_511_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_508_ = lean_st_ref_set(v___y_486_, v___x_507_);
                v___x_509_ = lean_box(0);
                v___x_510_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_510_, 0, v___x_509_);
                return v___x_510_;
            }
            4 => {
                v___x_522_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_469_,
                    );
                v___x_523_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1_spec__2(v___x_522_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
                v_a_524_ = lean_ctor_get(v___x_523_, 0);
                v_isSharedCheck_537_ = (!lean_is_exclusive(v___x_523_)) as u8;
                if v_isSharedCheck_537_ == 0 {
                    v___x_526_ = v___x_523_;
                    v_isShared_527_ = v_isSharedCheck_537_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_a_524_);
                    lean_dec(v___x_523_);
                    v___x_526_ = lean_box(0);
                    v_isShared_527_ = v_isSharedCheck_537_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref_n(v___y_516_, 2);
                v___x_528_ = l_Lean_FileMap_toPosition(v___y_516_, v___y_517_);
                lean_dec(v___y_517_);
                v___x_529_ = l_Lean_FileMap_toPosition(v___y_516_, v___y_521_);
                lean_dec(v___y_521_);
                v___x_530_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_530_, 0, v___x_529_);
                v___x_531_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___closed__0;
                if v___y_520_ == 0 {
                    lean_del_object(v___x_526_);
                    lean_dec_ref(v___y_514_);
                    v___y_478_ = v___y_515_;
                    v___y_479_ = v___x_531_;
                    v___y_480_ = v_a_524_;
                    v___y_481_ = v___y_519_;
                    v___y_482_ = v___y_518_;
                    v___y_483_ = v___x_530_;
                    v___y_484_ = v___x_528_;
                    v___y_485_ = v___y_474_;
                    v___y_486_ = v___y_475_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_524_);
                    v___x_532_ = l_Lean_MessageData_hasTag(v___y_514_, v_a_524_);
                    if v___x_532_ == 0 {
                        lean_dec_ref_known(v___x_530_, 1);
                        lean_dec_ref(v___x_528_);
                        lean_dec(v_a_524_);
                        v___x_533_ = lean_box(0);
                        if v_isShared_527_ == 0 {
                            lean_ctor_set(v___x_526_, 0, v___x_533_);
                            v___x_535_ = v___x_526_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
                            v___x_535_ = v_reuseFailAlloc_536_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_526_);
                        v___y_478_ = v___y_515_;
                        v___y_479_ = v___x_531_;
                        v___y_480_ = v_a_524_;
                        v___y_481_ = v___y_519_;
                        v___y_482_ = v___y_518_;
                        v___y_483_ = v___x_530_;
                        v___y_484_ = v___x_528_;
                        v___y_485_ = v___y_474_;
                        v___y_486_ = v___y_475_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_535_;
            }
            7 => {
                v___x_547_ = l_Lean_Syntax_getTailPos_x3f(v___y_542_, v___y_544_);
                lean_dec(v___y_542_);
                if lean_obj_tag(v___x_547_) == 0 {
                    lean_inc(v___y_546_);
                    v___y_514_ = v___y_539_;
                    v___y_515_ = v___y_540_;
                    v___y_516_ = v___y_541_;
                    v___y_517_ = v___y_546_;
                    v___y_518_ = v___y_544_;
                    v___y_519_ = v___y_543_;
                    v___y_520_ = v___y_545_;
                    v___y_521_ = v___y_546_;
                    state = 4;
                    continue;
                } else {
                    v_val_548_ = lean_ctor_get(v___x_547_, 0);
                    lean_inc(v_val_548_);
                    lean_dec_ref_known(v___x_547_, 1);
                    v___y_514_ = v___y_539_;
                    v___y_515_ = v___y_540_;
                    v___y_516_ = v___y_541_;
                    v___y_517_ = v___y_546_;
                    v___y_518_ = v___y_544_;
                    v___y_519_ = v___y_543_;
                    v___y_520_ = v___y_545_;
                    v___y_521_ = v_val_548_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_557_ = l_Lean_replaceRef(v_ref_468_, v___y_552_);
                v___x_558_ = l_Lean_Syntax_getPos_x3f(v_ref_557_, v___y_554_);
                if lean_obj_tag(v___x_558_) == 0 {
                    v___x_559_ = lean_unsigned_to_nat(0);
                    v___y_539_ = v___y_550_;
                    v___y_540_ = v___y_551_;
                    v___y_541_ = v___y_553_;
                    v___y_542_ = v_ref_557_;
                    v___y_543_ = v___y_556_;
                    v___y_544_ = v___y_554_;
                    v___y_545_ = v___y_555_;
                    v___y_546_ = v___x_559_;
                    state = 7;
                    continue;
                } else {
                    v_val_560_ = lean_ctor_get(v___x_558_, 0);
                    lean_inc(v_val_560_);
                    lean_dec_ref_known(v___x_558_, 1);
                    v___y_539_ = v___y_550_;
                    v___y_540_ = v___y_551_;
                    v___y_541_ = v___y_553_;
                    v___y_542_ = v_ref_557_;
                    v___y_543_ = v___y_556_;
                    v___y_544_ = v___y_554_;
                    v___y_545_ = v___y_555_;
                    v___y_546_ = v_val_560_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_569_ == 0 {
                    v___y_550_ = v___y_566_;
                    v___y_551_ = v___y_563_;
                    v___y_552_ = v___y_564_;
                    v___y_553_ = v___y_565_;
                    v___y_554_ = v___y_568_;
                    v___y_555_ = v___y_567_;
                    v___y_556_ = v_severity_470_;
                    state = 8;
                    continue;
                } else {
                    v___y_550_ = v___y_566_;
                    v___y_551_ = v___y_563_;
                    v___y_552_ = v___y_564_;
                    v___y_553_ = v___y_565_;
                    v___y_554_ = v___y_568_;
                    v___y_555_ = v___y_567_;
                    v___y_556_ = v___x_561_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_571_ == 0 {
                    v_fileName_572_ = lean_ctor_get(v___y_474_, 0);
                    v_fileMap_573_ = lean_ctor_get(v___y_474_, 1);
                    v_options_574_ = lean_ctor_get(v___y_474_, 2);
                    v_ref_575_ = lean_ctor_get(v___y_474_, 5);
                    v_suppressElabErrors_576_ = lean_ctor_get_uint8(
                        v___y_474_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_577_ = lean_box((v___y_571_) as usize);
                    v___x_578_ = lean_box((v_suppressElabErrors_576_) as usize);
                    v___f_579_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_579_, 0, v___x_577_);
                    lean_closure_set(v___f_579_, 1, v___x_578_);
                    v___x_580_ = 1;
                    v___x_581_ = l_Lean_instBEqMessageSeverity_beq(v_severity_470_, v___x_580_);
                    if v___x_581_ == 0 {
                        v___y_563_ = v_fileName_572_;
                        v___y_564_ = v_ref_575_;
                        v___y_565_ = v_fileMap_573_;
                        v___y_566_ = v___f_579_;
                        v___y_567_ = v_suppressElabErrors_576_;
                        v___y_568_ = v___y_571_;
                        v___y_569_ = v___x_581_;
                        state = 9;
                        continue;
                    } else {
                        v___x_582_ = l_Lean_warningAsError;
                        v___x_583_ =
                            l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0(
                                v_options_574_,
                                v___x_582_,
                            );
                        v___y_563_ = v_fileName_572_;
                        v___y_564_ = v_ref_575_;
                        v___y_565_ = v_fileMap_573_;
                        v___y_566_ = v___f_579_;
                        v___y_567_ = v_suppressElabErrors_576_;
                        v___y_568_ = v___y_571_;
                        v___y_569_ = v___x_583_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_469_);
                    v___x_584_ = lean_box(0);
                    v___x_585_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_585_, 0, v___x_584_);
                    return v___x_585_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg___boxed(
    mut v_ref_588_: *mut LeanObject,
    mut v_msgData_589_: *mut LeanObject,
    mut v_severity_590_: *mut LeanObject,
    mut v_isSilent_591_: *mut LeanObject,
    mut v___y_592_: *mut LeanObject,
    mut v___y_593_: *mut LeanObject,
    mut v___y_594_: *mut LeanObject,
    mut v___y_595_: *mut LeanObject,
    mut v___y_596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_597_: u8 = 0;
    let mut v_isSilent_boxed_598_: u8 = 0;
    let mut v_res_599_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_597_ = (lean_unbox(v_severity_590_) as u8);
    v_isSilent_boxed_598_ = (lean_unbox(v_isSilent_591_) as u8);
    v_res_599_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg(v_ref_588_, v_msgData_589_, v_severity_boxed_597_, v_isSilent_boxed_598_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
    lean_dec(v___y_595_);
    lean_dec_ref(v___y_594_);
    lean_dec(v___y_593_);
    lean_dec_ref(v___y_592_);
    lean_dec(v_ref_588_);
    return v_res_599_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1(
    mut v_ref_600_: *mut LeanObject,
    mut v_msgData_601_: *mut LeanObject,
    mut v___y_602_: *mut LeanObject,
    mut v___y_603_: *mut LeanObject,
    mut v___y_604_: *mut LeanObject,
    mut v___y_605_: *mut LeanObject,
    mut v___y_606_: *mut LeanObject,
    mut v___y_607_: *mut LeanObject,
    mut v___y_608_: *mut LeanObject,
    mut v___y_609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_611_: u8 = 0;
    let mut v___x_612_: u8 = 0;
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    v___x_611_ = 1;
    v___x_612_ = 0;
    v___x_613_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg(v_ref_600_, v_msgData_601_, v___x_611_, v___x_612_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
    return v___x_613_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1___boxed(
    mut v_ref_614_: *mut LeanObject,
    mut v_msgData_615_: *mut LeanObject,
    mut v___y_616_: *mut LeanObject,
    mut v___y_617_: *mut LeanObject,
    mut v___y_618_: *mut LeanObject,
    mut v___y_619_: *mut LeanObject,
    mut v___y_620_: *mut LeanObject,
    mut v___y_621_: *mut LeanObject,
    mut v___y_622_: *mut LeanObject,
    mut v___y_623_: *mut LeanObject,
    mut v___y_624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_625_: *mut LeanObject = core::ptr::null_mut();
    v_res_625_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1(
        v_ref_614_,
        v_msgData_615_,
        v___y_616_,
        v___y_617_,
        v___y_618_,
        v___y_619_,
        v___y_620_,
        v___y_621_,
        v___y_622_,
        v___y_623_,
    );
    lean_dec(v___y_623_);
    lean_dec_ref(v___y_622_);
    lean_dec(v___y_621_);
    lean_dec_ref(v___y_620_);
    lean_dec(v___y_619_);
    lean_dec_ref(v___y_618_);
    lean_dec(v___y_617_);
    lean_dec_ref(v___y_616_);
    lean_dec(v_ref_614_);
    return v_res_625_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__2() -> *mut LeanObject {
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    v___x_629_ = l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__1;
    v___x_630_ = l_Lean_MessageData_ofFormat(v___x_629_);
    return v___x_630_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalCbv___lam__0(
    mut v_stx_631_: *mut LeanObject,
    mut v___y_632_: *mut LeanObject,
    mut v___y_633_: *mut LeanObject,
    mut v___y_634_: *mut LeanObject,
    mut v___y_635_: *mut LeanObject,
    mut v___y_636_: *mut LeanObject,
    mut v___y_637_: *mut LeanObject,
    mut v___y_638_: *mut LeanObject,
    mut v___y_639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_656_: u8 = 0;
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x27_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_664_: u8 = 0;
    let mut v_a_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_668_: u8 = 0;
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_672_: u8 = 0;
    let mut v_a_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_676_: u8 = 0;
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_680_: u8 = 0;
    let mut v_options_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: u8 = 0;
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_681_ = lean_ctor_get(v___y_638_, 2);
                v___x_682_ = l_Lean_Meta_Tactic_Cbv_cbv_warning;
                v___x_683_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__0(
                    v_options_681_,
                    v___x_682_,
                );
                if v___x_683_ == 0 {
                    v___y_642_ = v___y_632_;
                    v___y_643_ = v___y_633_;
                    v___y_644_ = v___y_634_;
                    v___y_645_ = v___y_635_;
                    v___y_646_ = v___y_636_;
                    v___y_647_ = v___y_637_;
                    v___y_648_ = v___y_638_;
                    v___y_649_ = v___y_639_;
                    state = 1;
                    continue;
                } else {
                    v___x_684_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__2_once
                        ),
                        _init_l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___closed__2,
                    );
                    v___x_685_ = l_Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1(
                        v_stx_631_, v___x_684_, v___y_632_, v___y_633_, v___y_634_, v___y_635_,
                        v___y_636_, v___y_637_, v___y_638_, v___y_639_,
                    );
                    if lean_obj_tag(v___x_685_) == 0 {
                        lean_dec_ref_known(v___x_685_, 1);
                        v___y_642_ = v___y_632_;
                        v___y_643_ = v___y_633_;
                        v___y_644_ = v___y_634_;
                        v___y_645_ = v___y_635_;
                        v___y_646_ = v___y_636_;
                        v___y_647_ = v___y_637_;
                        v___y_648_ = v___y_638_;
                        v___y_649_ = v___y_639_;
                        state = 1;
                        continue;
                    } else {
                        return v___x_685_;
                    }
                }
            }
            1 => {
                v___x_650_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                    v___y_643_, v___y_646_, v___y_647_, v___y_648_, v___y_649_,
                );
                if lean_obj_tag(v___x_650_) == 0 {
                    v_a_651_ = lean_ctor_get(v___x_650_, 0);
                    lean_inc(v_a_651_);
                    lean_dec_ref_known(v___x_650_, 1);
                    v___x_652_ = l_Lean_Meta_Tactic_Cbv_cbvEntry(
                        v_a_651_, v___y_646_, v___y_647_, v___y_648_, v___y_649_,
                    );
                    if lean_obj_tag(v___x_652_) == 0 {
                        v_a_653_ = lean_ctor_get(v___x_652_, 0);
                        v_isSharedCheck_664_ = (!lean_is_exclusive(v___x_652_)) as u8;
                        if v_isSharedCheck_664_ == 0 {
                            v___x_655_ = v___x_652_;
                            v_isShared_656_ = v_isSharedCheck_664_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_653_);
                            lean_dec(v___x_652_);
                            v___x_655_ = lean_box(0);
                            v_isShared_656_ = v_isSharedCheck_664_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_665_ = lean_ctor_get(v___x_652_, 0);
                        v_isSharedCheck_672_ = (!lean_is_exclusive(v___x_652_)) as u8;
                        if v_isSharedCheck_672_ == 0 {
                            v___x_667_ = v___x_652_;
                            v_isShared_668_ = v_isSharedCheck_672_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_665_);
                            lean_dec(v___x_652_);
                            v___x_667_ = lean_box(0);
                            v_isShared_668_ = v_isSharedCheck_672_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_673_ = lean_ctor_get(v___x_650_, 0);
                    v_isSharedCheck_680_ = (!lean_is_exclusive(v___x_650_)) as u8;
                    if v_isSharedCheck_680_ == 0 {
                        v___x_675_ = v___x_650_;
                        v_isShared_676_ = v_isSharedCheck_680_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_673_);
                        lean_dec(v___x_650_);
                        v___x_675_ = lean_box(0);
                        v_isShared_676_ = v_isSharedCheck_680_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_653_) == 0 {
                    lean_dec_ref_known(v_a_653_, 0);
                    v___x_657_ = lean_box(0);
                    if v_isShared_656_ == 0 {
                        lean_ctor_set(v___x_655_, 0, v___x_657_);
                        v___x_659_ = v___x_655_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_657_);
                        v___x_659_ = v_reuseFailAlloc_660_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_655_);
                    v_e_x27_661_ = lean_ctor_get(v_a_653_, 0);
                    lean_inc_ref(v_e_x27_661_);
                    v_proof_662_ = lean_ctor_get(v_a_653_, 1);
                    lean_inc_ref(v_proof_662_);
                    lean_dec_ref_known(v_a_653_, 2);
                    v___x_663_ = l_Lean_Elab_Tactic_Conv_updateLhs(
                        v_e_x27_661_,
                        v_proof_662_,
                        v___y_642_,
                        v___y_643_,
                        v___y_644_,
                        v___y_645_,
                        v___y_646_,
                        v___y_647_,
                        v___y_648_,
                        v___y_649_,
                    );
                    return v___x_663_;
                }
            }
            3 => {
                return v___x_659_;
            }
            4 => {
                if v_isShared_668_ == 0 {
                    v___x_670_ = v___x_667_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
                    v___x_670_ = v_reuseFailAlloc_671_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_670_;
            }
            6 => {
                if v_isShared_676_ == 0 {
                    v___x_678_ = v___x_675_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
                    v___x_678_ = v_reuseFailAlloc_679_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_678_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___boxed(
    mut v_stx_686_: *mut LeanObject,
    mut v___y_687_: *mut LeanObject,
    mut v___y_688_: *mut LeanObject,
    mut v___y_689_: *mut LeanObject,
    mut v___y_690_: *mut LeanObject,
    mut v___y_691_: *mut LeanObject,
    mut v___y_692_: *mut LeanObject,
    mut v___y_693_: *mut LeanObject,
    mut v___y_694_: *mut LeanObject,
    mut v___y_695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_696_: *mut LeanObject = core::ptr::null_mut();
    v_res_696_ = l_Lean_Elab_Tactic_Conv_evalCbv___lam__0(
        v_stx_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_,
        v___y_693_, v___y_694_,
    );
    lean_dec(v___y_694_);
    lean_dec_ref(v___y_693_);
    lean_dec(v___y_692_);
    lean_dec_ref(v___y_691_);
    lean_dec(v___y_690_);
    lean_dec_ref(v___y_689_);
    lean_dec(v___y_688_);
    lean_dec_ref(v___y_687_);
    lean_dec(v_stx_686_);
    return v_res_696_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalCbv(
    mut v_stx_697_: *mut LeanObject,
    mut v_a_698_: *mut LeanObject,
    mut v_a_699_: *mut LeanObject,
    mut v_a_700_: *mut LeanObject,
    mut v_a_701_: *mut LeanObject,
    mut v_a_702_: *mut LeanObject,
    mut v_a_703_: *mut LeanObject,
    mut v_a_704_: *mut LeanObject,
    mut v_a_705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    v___f_707_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalCbv___lam__0___boxed as *mut core::ffi::c_void,
        10,
        1,
    );
    lean_closure_set(v___f_707_, 0, v_stx_697_);
    v___x_708_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_707_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_,
    );
    return v___x_708_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalCbv___boxed(
    mut v_stx_709_: *mut LeanObject,
    mut v_a_710_: *mut LeanObject,
    mut v_a_711_: *mut LeanObject,
    mut v_a_712_: *mut LeanObject,
    mut v_a_713_: *mut LeanObject,
    mut v_a_714_: *mut LeanObject,
    mut v_a_715_: *mut LeanObject,
    mut v_a_716_: *mut LeanObject,
    mut v_a_717_: *mut LeanObject,
    mut v_a_718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_719_: *mut LeanObject = core::ptr::null_mut();
    v_res_719_ = l_Lean_Elab_Tactic_Conv_evalCbv(
        v_stx_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_,
    );
    lean_dec(v_a_717_);
    lean_dec_ref(v_a_716_);
    lean_dec(v_a_715_);
    lean_dec_ref(v_a_714_);
    lean_dec(v_a_713_);
    lean_dec_ref(v_a_712_);
    lean_dec(v_a_711_);
    lean_dec_ref(v_a_710_);
    return v_res_719_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1(
    mut v_ref_720_: *mut LeanObject,
    mut v_msgData_721_: *mut LeanObject,
    mut v_severity_722_: u8,
    mut v_isSilent_723_: u8,
    mut v___y_724_: *mut LeanObject,
    mut v___y_725_: *mut LeanObject,
    mut v___y_726_: *mut LeanObject,
    mut v___y_727_: *mut LeanObject,
    mut v___y_728_: *mut LeanObject,
    mut v___y_729_: *mut LeanObject,
    mut v___y_730_: *mut LeanObject,
    mut v___y_731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    v___x_733_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___redArg(v_ref_720_, v_msgData_721_, v_severity_722_, v_isSilent_723_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
    return v___x_733_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1___boxed(
    mut v_ref_734_: *mut LeanObject,
    mut v_msgData_735_: *mut LeanObject,
    mut v_severity_736_: *mut LeanObject,
    mut v_isSilent_737_: *mut LeanObject,
    mut v___y_738_: *mut LeanObject,
    mut v___y_739_: *mut LeanObject,
    mut v___y_740_: *mut LeanObject,
    mut v___y_741_: *mut LeanObject,
    mut v___y_742_: *mut LeanObject,
    mut v___y_743_: *mut LeanObject,
    mut v___y_744_: *mut LeanObject,
    mut v___y_745_: *mut LeanObject,
    mut v___y_746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_747_: u8 = 0;
    let mut v_isSilent_boxed_748_: u8 = 0;
    let mut v_res_749_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_747_ = (lean_unbox(v_severity_736_) as u8);
    v_isSilent_boxed_748_ = (lean_unbox(v_isSilent_737_) as u8);
    v_res_749_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Tactic_Conv_evalCbv_spec__1_spec__1(v_ref_734_, v_msgData_735_, v_severity_boxed_747_, v_isSilent_boxed_748_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
    lean_dec(v___y_745_);
    lean_dec_ref(v___y_744_);
    lean_dec(v___y_743_);
    lean_dec_ref(v___y_742_);
    lean_dec(v___y_741_);
    lean_dec_ref(v___y_740_);
    lean_dec(v___y_739_);
    lean_dec_ref(v___y_738_);
    lean_dec(v_ref_734_);
    return v_res_749_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1()
-> *mut LeanObject {
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    v___x_768_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_769_ = l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__4;
    v___x_770_ = l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___closed__6;
    v___x_771_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalCbv___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_772_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_768_, v___x_769_, v___x_770_, v___x_771_,
    );
    return v___x_772_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1___boxed(
    mut v_a_773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_774_: *mut LeanObject = core::ptr::null_mut();
    v_res_774_ = l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1();
    return v_res_774_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Conv_Cbv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Cbv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Cbv_0__Lean_Elab_Tactic_Conv_evalCbv___regBuiltin_Lean_Elab_Tactic_Conv_evalCbv__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Conv_Cbv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Conv_Cbv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Cbv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Cbv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Conv_Cbv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Conv_Cbv(builtin);
}

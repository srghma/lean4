// Lean compiler output
// Module: Lean.Elab.Tactic.Injection
// Imports: Lean.Meta.Tactic.Injection Lean.Meta.Tactic.Assumption Lean.Elab.Tactic.ElabTerm
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_getNameOfIdent_x27,
    l_Lean_Elab_Tactic_replaceMainGoal___redArg, l_Lean_Elab_Tactic_tacticElabAttribute,
    l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::{
    initialize_Lean_Elab_Tactic_ElabTerm, l_Lean_Elab_Tactic_elabAsFVar,
    runtime_initialize_Lean_Elab_Tactic_ElabTerm,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofList, l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Tactic::Assumption::{
    initialize_Lean_Meta_Tactic_Assumption, l_Lean_MVarId_assumptionCore,
    runtime_initialize_Lean_Meta_Tactic_Assumption,
};
use crate::r#gen::Lean::Meta::Tactic::Injection::{
    initialize_Lean_Meta_Tactic_Injection, l_Lean_Meta_injection, l_Lean_Meta_injections,
    runtime_initialize_Lean_Meta_Tactic_Injection,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_Meta_throwTacticEx___redArg;
use crate::lean_imports_rs::Init::Prelude::lean_array_to_list;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_inc, lean_inc_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__0_value: LeanStringObject<40> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [116, 111, 111, 32, 109, 97, 110, 121, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 115, 32, 112, 114, 111, 118, 105, 100, 101, 100, 44, 32, 117, 110, 117, 115, 101, 100, 58, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalInjection___lam__0___closed__0_value: LeanStringObject<10> =
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
        m_data: [105, 110, 106, 101, 99, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Elab_Tactic_evalInjection___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalInjection___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalInjection___lam__0___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalInjection___lam__0___closed__0_value)
                as *mut LeanObject,
            12874249535713742015 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalInjection___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalInjection___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalInjection___lam__0___closed__0_value) as *mut LeanObject,8171666429901634422 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__5_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 118, 97, 108, 73, 110, 106, 101, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__5_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__4_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__5_value) as *mut LeanObject,6549291366557724274 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 30 as usize) << 1) | 1) as *mut LeanObject,((( 30 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 37 as usize) << 1) | 1) as *mut LeanObject,((( 103 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__0_value) as *mut LeanObject,((( 30 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__1_value) as *mut LeanObject,((( 103 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 30 as usize) << 1) | 1) as *mut LeanObject,((( 34 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 30 as usize) << 1) | 1) as *mut LeanObject,((( 47 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__3_value) as *mut LeanObject,((( 34 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__4_value) as *mut LeanObject,((( 47 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalInjections___lam__0___closed__0_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [105, 110, 106, 101, 99, 116, 105, 111, 110, 115, 0],
    };
static mut l_Lean_Elab_Tactic_evalInjections___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalInjections___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalInjections___lam__0___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalInjections___lam__0___closed__0_value)
                as *mut LeanObject,
            5163565424560827901 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalInjections___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalInjections___lam__0___closed__1_value)
        as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalInjections___lam__0___closed__0_value) as *mut LeanObject,12924360897913574244 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__1_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 118, 97, 108, 73, 110, 106, 101, 99, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__1_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__4_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__1_value) as *mut LeanObject,15701361205147766637 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 39 as usize) << 1) | 1) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 44 as usize) << 1) | 1) as *mut LeanObject,((( 102 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__0_value) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__1_value) as *mut LeanObject,((( 102 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 39 as usize) << 1) | 1) as *mut LeanObject,((( 35 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 39 as usize) << 1) | 1) as *mut LeanObject,((( 49 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__3_value) as *mut LeanObject,((( 35 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__4_value) as *mut LeanObject,((( 49 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__6_value) as *mut LeanObject;
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds_spec__0(
    mut v_a_430_: *mut LeanObject,
    mut v_a_431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_437_: u8 = 0;
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_443_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_430_) == 0 {
                    v___x_432_ = l_List_reverse___redArg(v_a_431_);
                    return v___x_432_;
                } else {
                    v_head_433_ = lean_ctor_get(v_a_430_, 0);
                    v_tail_434_ = lean_ctor_get(v_a_430_, 1);
                    v_isSharedCheck_443_ = (!lean_is_exclusive(v_a_430_)) as u8;
                    if v_isSharedCheck_443_ == 0 {
                        v___x_436_ = v_a_430_;
                        v_isShared_437_ = v_isSharedCheck_443_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_434_);
                        lean_inc(v_head_433_);
                        lean_dec(v_a_430_);
                        v___x_436_ = lean_box(0);
                        v_isShared_437_ = v_isSharedCheck_443_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_438_ = l_Lean_Elab_Tactic_getNameOfIdent_x27(v_head_433_);
                lean_dec(v_head_433_);
                if v_isShared_437_ == 0 {
                    lean_ctor_set(v___x_436_, 1, v_a_431_);
                    lean_ctor_set(v___x_436_, 0, v___x_438_);
                    v___x_440_ = v___x_436_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_438_);
                    lean_ctor_set(v_reuseFailAlloc_442_, 1, v_a_431_);
                    v___x_440_ = v_reuseFailAlloc_442_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_430_ = v_tail_434_;
                v_a_431_ = v___x_440_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds(
    mut v_stx_444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_445_: u8 = 0;
    v___x_445_ = l_Lean_Syntax_isNone(v_stx_444_);
    if v___x_445_ == 0 {
        let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_447_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
        v___x_446_ = lean_unsigned_to_nat(1);
        v___x_447_ = l_Lean_Syntax_getArg(v_stx_444_, v___x_446_);
        v___x_448_ = l_Lean_Syntax_getArgs(v___x_447_);
        lean_dec(v___x_447_);
        v___x_449_ = lean_array_to_list(v___x_448_);
        v___x_450_ = lean_box(0);
        v___x_451_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds_spec__0(v___x_449_, v___x_450_);
        return v___x_451_;
    } else {
        let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
        v___x_452_ = lean_box(0);
        return v___x_452_;
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds___boxed(
    mut v_stx_453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_454_: *mut LeanObject = core::ptr::null_mut();
    v_res_454_ =
        l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds(v_stx_453_);
    lean_dec(v_stx_453_);
    return v_res_454_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds_spec__0(
    mut v_a_455_: *mut LeanObject,
    mut v_a_456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_462_: u8 = 0;
    let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_455_) == 0 {
                    v___x_457_ = l_List_reverse___redArg(v_a_456_);
                    return v___x_457_;
                } else {
                    v_head_458_ = lean_ctor_get(v_a_455_, 0);
                    v_tail_459_ = lean_ctor_get(v_a_455_, 1);
                    v_isSharedCheck_468_ = (!lean_is_exclusive(v_a_455_)) as u8;
                    if v_isSharedCheck_468_ == 0 {
                        v___x_461_ = v_a_455_;
                        v_isShared_462_ = v_isSharedCheck_468_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_459_);
                        lean_inc(v_head_458_);
                        lean_dec(v_a_455_);
                        v___x_461_ = lean_box(0);
                        v_isShared_462_ = v_isSharedCheck_468_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_463_ = l_Lean_MessageData_ofName(v_head_458_);
                if v_isShared_462_ == 0 {
                    lean_ctor_set(v___x_461_, 1, v_a_456_);
                    lean_ctor_set(v___x_461_, 0, v___x_463_);
                    v___x_465_ = v___x_461_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_463_);
                    lean_ctor_set(v_reuseFailAlloc_467_, 1, v_a_456_);
                    v___x_465_ = v_reuseFailAlloc_467_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_455_ = v_tail_459_;
                v_a_456_ = v___x_465_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__1()
-> *mut LeanObject {
    let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
    v___x_470_ =
        l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__0;
    v___x_471_ = l_Lean_stringToMessageData(v___x_470_);
    return v___x_471_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(
    mut v_tacticName_472_: *mut LeanObject,
    mut v_mvarId_473_: *mut LeanObject,
    mut v_unusedIds_474_: *mut LeanObject,
    mut v_a_475_: *mut LeanObject,
    mut v_a_476_: *mut LeanObject,
    mut v_a_477_: *mut LeanObject,
    mut v_a_478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_480_: u8 = 0;
    v___x_480_ = l_List_isEmpty___redArg(v_unusedIds_474_);
    if v___x_480_ == 0 {
        let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
        v___x_481_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__1_once), _init_l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___closed__1);
        v___x_482_ = lean_box(0);
        v___x_483_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds_spec__0(v_unusedIds_474_, v___x_482_);
        v___x_484_ = l_Lean_MessageData_ofList(v___x_483_);
        v___x_485_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_485_, 0, v___x_481_);
        lean_ctor_set(v___x_485_, 1, v___x_484_);
        v___x_486_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_486_, 0, v___x_485_);
        v___x_487_ = l_Lean_Meta_throwTacticEx___redArg(
            v_tacticName_472_,
            v_mvarId_473_,
            v___x_486_,
            v_a_475_,
            v_a_476_,
            v_a_477_,
            v_a_478_,
        );
        return v___x_487_;
    } else {
        let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_unusedIds_474_);
        lean_dec(v_mvarId_473_);
        lean_dec(v_tacticName_472_);
        v___x_488_ = lean_box(0);
        v___x_489_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_489_, 0, v___x_488_);
        return v___x_489_;
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds___boxed(
    mut v_tacticName_490_: *mut LeanObject,
    mut v_mvarId_491_: *mut LeanObject,
    mut v_unusedIds_492_: *mut LeanObject,
    mut v_a_493_: *mut LeanObject,
    mut v_a_494_: *mut LeanObject,
    mut v_a_495_: *mut LeanObject,
    mut v_a_496_: *mut LeanObject,
    mut v_a_497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_498_: *mut LeanObject = core::ptr::null_mut();
    v_res_498_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(
        v_tacticName_490_,
        v_mvarId_491_,
        v_unusedIds_492_,
        v_a_493_,
        v_a_494_,
        v_a_495_,
        v_a_496_,
    );
    lean_dec(v_a_496_);
    lean_dec_ref(v_a_495_);
    lean_dec(v_a_494_);
    lean_dec_ref(v_a_493_);
    return v_res_498_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption(
    mut v_mvarId_499_: *mut LeanObject,
    mut v_a_500_: *mut LeanObject,
    mut v_a_501_: *mut LeanObject,
    mut v_a_502_: *mut LeanObject,
    mut v_a_503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_509_: u8 = 0;
    let mut v___x_510_: u8 = 0;
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_520_: u8 = 0;
    let mut v_a_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_524_: u8 = 0;
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_528_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_499_);
                v___x_505_ = l_Lean_MVarId_assumptionCore(
                    v_mvarId_499_,
                    v_a_500_,
                    v_a_501_,
                    v_a_502_,
                    v_a_503_,
                );
                if lean_obj_tag(v___x_505_) == 0 {
                    v_a_506_ = lean_ctor_get(v___x_505_, 0);
                    v_isSharedCheck_520_ = (!lean_is_exclusive(v___x_505_)) as u8;
                    if v_isSharedCheck_520_ == 0 {
                        v___x_508_ = v___x_505_;
                        v_isShared_509_ = v_isSharedCheck_520_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_506_);
                        lean_dec(v___x_505_);
                        v___x_508_ = lean_box(0);
                        v_isShared_509_ = v_isSharedCheck_520_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_mvarId_499_);
                    v_a_521_ = lean_ctor_get(v___x_505_, 0);
                    v_isSharedCheck_528_ = (!lean_is_exclusive(v___x_505_)) as u8;
                    if v_isSharedCheck_528_ == 0 {
                        v___x_523_ = v___x_505_;
                        v_isShared_524_ = v_isSharedCheck_528_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_521_);
                        lean_dec(v___x_505_);
                        v___x_523_ = lean_box(0);
                        v_isShared_524_ = v_isSharedCheck_528_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_510_ = (lean_unbox(v_a_506_) as u8);
                lean_dec(v_a_506_);
                if v___x_510_ == 0 {
                    v___x_511_ = lean_box(0);
                    v___x_512_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_512_, 0, v_mvarId_499_);
                    lean_ctor_set(v___x_512_, 1, v___x_511_);
                    if v_isShared_509_ == 0 {
                        lean_ctor_set(v___x_508_, 0, v___x_512_);
                        v___x_514_ = v___x_508_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
                        v___x_514_ = v_reuseFailAlloc_515_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_mvarId_499_);
                    v___x_516_ = lean_box(0);
                    if v_isShared_509_ == 0 {
                        lean_ctor_set(v___x_508_, 0, v___x_516_);
                        v___x_518_ = v___x_508_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_516_);
                        v___x_518_ = v_reuseFailAlloc_519_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_514_;
            }
            3 => {
                return v___x_518_;
            }
            4 => {
                if v_isShared_524_ == 0 {
                    v___x_526_ = v___x_523_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_521_);
                    v___x_526_ = v_reuseFailAlloc_527_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_526_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption___boxed(
    mut v_mvarId_529_: *mut LeanObject,
    mut v_a_530_: *mut LeanObject,
    mut v_a_531_: *mut LeanObject,
    mut v_a_532_: *mut LeanObject,
    mut v_a_533_: *mut LeanObject,
    mut v_a_534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_535_: *mut LeanObject = core::ptr::null_mut();
    v_res_535_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption(
        v_mvarId_529_,
        v_a_530_,
        v_a_531_,
        v_a_532_,
        v_a_533_,
    );
    lean_dec(v_a_533_);
    lean_dec_ref(v_a_532_);
    lean_dec(v_a_531_);
    lean_dec_ref(v_a_530_);
    return v_res_535_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalInjection___lam__0(
    mut v_a_539_: *mut LeanObject,
    mut v___x_540_: *mut LeanObject,
    mut v___y_541_: *mut LeanObject,
    mut v___y_542_: *mut LeanObject,
    mut v___y_543_: *mut LeanObject,
    mut v___y_544_: *mut LeanObject,
    mut v___y_545_: *mut LeanObject,
    mut v___y_546_: *mut LeanObject,
    mut v___y_547_: *mut LeanObject,
    mut v___y_548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_555_: u8 = 0;
    let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_560_: u8 = 0;
    let mut v_unused_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_remainingNames_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_578_: u8 = 0;
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_582_: u8 = 0;
    let mut v_a_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_586_: u8 = 0;
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_590_: u8 = 0;
    let mut v_a_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_594_: u8 = 0;
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_598_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_562_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_542_, v___y_545_, v___y_546_, v___y_547_, v___y_548_,
                );
                if lean_obj_tag(v___x_562_) == 0 {
                    v_a_563_ = lean_ctor_get(v___x_562_, 0);
                    lean_inc_n(v_a_563_, 2);
                    lean_dec_ref_known(v___x_562_, 1);
                    lean_inc(v___x_540_);
                    v___x_564_ = l_Lean_Meta_injection(
                        v_a_563_, v_a_539_, v___x_540_, v___y_545_, v___y_546_, v___y_547_,
                        v___y_548_,
                    );
                    if lean_obj_tag(v___x_564_) == 0 {
                        v_a_565_ = lean_ctor_get(v___x_564_, 0);
                        lean_inc(v_a_565_);
                        lean_dec_ref_known(v___x_564_, 1);
                        if lean_obj_tag(v_a_565_) == 0 {
                            v___x_566_ = l_Lean_Elab_Tactic_evalInjection___lam__0___closed__1;
                            v___x_567_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(v___x_566_, v_a_563_, v___x_540_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
                            if lean_obj_tag(v___x_567_) == 0 {
                                lean_dec_ref_known(v___x_567_, 1);
                                v___x_568_ = lean_box(0);
                                v_a_551_ = v___x_568_;
                                state = 1;
                                continue;
                            } else {
                                return v___x_567_;
                            }
                        } else {
                            lean_dec(v___x_540_);
                            v_mvarId_569_ = lean_ctor_get(v_a_565_, 0);
                            lean_inc(v_mvarId_569_);
                            v_remainingNames_570_ = lean_ctor_get(v_a_565_, 2);
                            lean_inc(v_remainingNames_570_);
                            lean_dec_ref_known(v_a_565_, 3);
                            v___x_571_ = l_Lean_Elab_Tactic_evalInjection___lam__0___closed__1;
                            v___x_572_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(v___x_571_, v_a_563_, v_remainingNames_570_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
                            if lean_obj_tag(v___x_572_) == 0 {
                                lean_dec_ref_known(v___x_572_, 1);
                                v___x_573_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption(v_mvarId_569_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
                                if lean_obj_tag(v___x_573_) == 0 {
                                    v_a_574_ = lean_ctor_get(v___x_573_, 0);
                                    lean_inc(v_a_574_);
                                    lean_dec_ref_known(v___x_573_, 1);
                                    v_a_551_ = v_a_574_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_575_ = lean_ctor_get(v___x_573_, 0);
                                    v_isSharedCheck_582_ = (!lean_is_exclusive(v___x_573_)) as u8;
                                    if v_isSharedCheck_582_ == 0 {
                                        v___x_577_ = v___x_573_;
                                        v_isShared_578_ = v_isSharedCheck_582_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_a_575_);
                                        lean_dec(v___x_573_);
                                        v___x_577_ = lean_box(0);
                                        v_isShared_578_ = v_isSharedCheck_582_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_mvarId_569_);
                                return v___x_572_;
                            }
                        }
                    } else {
                        lean_dec(v_a_563_);
                        lean_dec(v___x_540_);
                        v_a_583_ = lean_ctor_get(v___x_564_, 0);
                        v_isSharedCheck_590_ = (!lean_is_exclusive(v___x_564_)) as u8;
                        if v_isSharedCheck_590_ == 0 {
                            v___x_585_ = v___x_564_;
                            v_isShared_586_ = v_isSharedCheck_590_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_583_);
                            lean_dec(v___x_564_);
                            v___x_585_ = lean_box(0);
                            v_isShared_586_ = v_isSharedCheck_590_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_540_);
                    lean_dec(v_a_539_);
                    v_a_591_ = lean_ctor_get(v___x_562_, 0);
                    v_isSharedCheck_598_ = (!lean_is_exclusive(v___x_562_)) as u8;
                    if v_isSharedCheck_598_ == 0 {
                        v___x_593_ = v___x_562_;
                        v_isShared_594_ = v_isSharedCheck_598_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_591_);
                        lean_dec(v___x_562_);
                        v___x_593_ = lean_box(0);
                        v_isShared_594_ = v_isSharedCheck_598_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_552_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v_a_551_, v___y_542_, v___y_545_, v___y_546_, v___y_547_, v___y_548_,
                );
                if lean_obj_tag(v___x_552_) == 0 {
                    v_isSharedCheck_560_ = (!lean_is_exclusive(v___x_552_)) as u8;
                    if v_isSharedCheck_560_ == 0 {
                        v_unused_561_ = lean_ctor_get(v___x_552_, 0);
                        lean_dec(v_unused_561_);
                        v___x_554_ = v___x_552_;
                        v_isShared_555_ = v_isSharedCheck_560_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_552_);
                        v___x_554_ = lean_box(0);
                        v_isShared_555_ = v_isSharedCheck_560_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_552_;
                }
            }
            2 => {
                v___x_556_ = lean_box(0);
                if v_isShared_555_ == 0 {
                    lean_ctor_set(v___x_554_, 0, v___x_556_);
                    v___x_558_ = v___x_554_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_556_);
                    v___x_558_ = v_reuseFailAlloc_559_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_558_;
            }
            4 => {
                if v_isShared_578_ == 0 {
                    v___x_580_ = v___x_577_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_575_);
                    v___x_580_ = v_reuseFailAlloc_581_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_580_;
            }
            6 => {
                if v_isShared_586_ == 0 {
                    v___x_588_ = v___x_585_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
                    v___x_588_ = v_reuseFailAlloc_589_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_588_;
            }
            8 => {
                if v_isShared_594_ == 0 {
                    v___x_596_ = v___x_593_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
                    v___x_596_ = v_reuseFailAlloc_597_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_596_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalInjection___lam__0___boxed(
    mut v_a_599_: *mut LeanObject,
    mut v___x_600_: *mut LeanObject,
    mut v___y_601_: *mut LeanObject,
    mut v___y_602_: *mut LeanObject,
    mut v___y_603_: *mut LeanObject,
    mut v___y_604_: *mut LeanObject,
    mut v___y_605_: *mut LeanObject,
    mut v___y_606_: *mut LeanObject,
    mut v___y_607_: *mut LeanObject,
    mut v___y_608_: *mut LeanObject,
    mut v___y_609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_610_: *mut LeanObject = core::ptr::null_mut();
    v_res_610_ = l_Lean_Elab_Tactic_evalInjection___lam__0(
        v_a_599_, v___x_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_,
        v___y_606_, v___y_607_, v___y_608_,
    );
    lean_dec(v___y_608_);
    lean_dec_ref(v___y_607_);
    lean_dec(v___y_606_);
    lean_dec_ref(v___y_605_);
    lean_dec(v___y_604_);
    lean_dec_ref(v___y_603_);
    lean_dec(v___y_602_);
    lean_dec_ref(v___y_601_);
    return v_res_610_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalInjection(
    mut v_stx_611_: *mut LeanObject,
    mut v_a_612_: *mut LeanObject,
    mut v_a_613_: *mut LeanObject,
    mut v_a_614_: *mut LeanObject,
    mut v_a_615_: *mut LeanObject,
    mut v_a_616_: *mut LeanObject,
    mut v_a_617_: *mut LeanObject,
    mut v_a_618_: *mut LeanObject,
    mut v_a_619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_634_: u8 = 0;
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_638_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_621_ = lean_unsigned_to_nat(1);
                v___x_622_ = l_Lean_Syntax_getArg(v_stx_611_, v___x_621_);
                v___x_623_ = lean_box(0);
                v___x_624_ = l_Lean_Elab_Tactic_elabAsFVar(
                    v___x_622_, v___x_623_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_,
                    v_a_617_, v_a_618_, v_a_619_,
                );
                if lean_obj_tag(v___x_624_) == 0 {
                    v_a_625_ = lean_ctor_get(v___x_624_, 0);
                    lean_inc(v_a_625_);
                    lean_dec_ref_known(v___x_624_, 1);
                    v___x_626_ = lean_unsigned_to_nat(2);
                    v___x_627_ = l_Lean_Syntax_getArg(v_stx_611_, v___x_626_);
                    v___x_628_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds(v___x_627_);
                    lean_dec(v___x_627_);
                    v___f_629_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalInjection___lam__0___boxed as *mut core::ffi::c_void,
                        11,
                        2,
                    );
                    lean_closure_set(v___f_629_, 0, v_a_625_);
                    lean_closure_set(v___f_629_, 1, v___x_628_);
                    v___x_630_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                        v___f_629_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_,
                        v_a_618_, v_a_619_,
                    );
                    return v___x_630_;
                } else {
                    v_a_631_ = lean_ctor_get(v___x_624_, 0);
                    v_isSharedCheck_638_ = (!lean_is_exclusive(v___x_624_)) as u8;
                    if v_isSharedCheck_638_ == 0 {
                        v___x_633_ = v___x_624_;
                        v_isShared_634_ = v_isSharedCheck_638_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_631_);
                        lean_dec(v___x_624_);
                        v___x_633_ = lean_box(0);
                        v_isShared_634_ = v_isSharedCheck_638_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_634_ == 0 {
                    v___x_636_ = v___x_633_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
                    v___x_636_ = v_reuseFailAlloc_637_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_636_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalInjection___boxed(
    mut v_stx_639_: *mut LeanObject,
    mut v_a_640_: *mut LeanObject,
    mut v_a_641_: *mut LeanObject,
    mut v_a_642_: *mut LeanObject,
    mut v_a_643_: *mut LeanObject,
    mut v_a_644_: *mut LeanObject,
    mut v_a_645_: *mut LeanObject,
    mut v_a_646_: *mut LeanObject,
    mut v_a_647_: *mut LeanObject,
    mut v_a_648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_649_: *mut LeanObject = core::ptr::null_mut();
    v_res_649_ = l_Lean_Elab_Tactic_evalInjection(
        v_stx_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_,
    );
    lean_dec(v_a_647_);
    lean_dec_ref(v_a_646_);
    lean_dec(v_a_645_);
    lean_dec_ref(v_a_644_);
    lean_dec(v_a_643_);
    lean_dec_ref(v_a_642_);
    lean_dec(v_a_641_);
    lean_dec_ref(v_a_640_);
    lean_dec(v_stx_639_);
    return v_res_649_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1()
-> *mut LeanObject {
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    v___x_666_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_667_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__3;
    v___x_668_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6;
    v___x_669_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalInjection___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_670_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_666_, v___x_667_, v___x_668_, v___x_669_,
    );
    return v___x_670_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___boxed(
    mut v_a_671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_672_: *mut LeanObject = core::ptr::null_mut();
    v_res_672_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1();
    return v_res_672_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3()
-> *mut LeanObject {
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    v___x_698_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1___closed__6;
    v___x_699_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___closed__6;
    v___x_700_ = l_Lean_addBuiltinDeclarationRanges(v___x_698_, v___x_699_);
    return v___x_700_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3___boxed(
    mut v_a_701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_702_: *mut LeanObject = core::ptr::null_mut();
    v_res_702_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3();
    return v_res_702_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalInjections___lam__0(
    mut v_ids_706_: *mut LeanObject,
    mut v___x_707_: *mut LeanObject,
    mut v___y_708_: *mut LeanObject,
    mut v___y_709_: *mut LeanObject,
    mut v___y_710_: *mut LeanObject,
    mut v___y_711_: *mut LeanObject,
    mut v___y_712_: *mut LeanObject,
    mut v___y_713_: *mut LeanObject,
    mut v___y_714_: *mut LeanObject,
    mut v___y_715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_722_: u8 = 0;
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_727_: u8 = 0;
    let mut v_unused_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_remainingNames_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_746_: u8 = 0;
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_750_: u8 = 0;
    let mut v_a_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_754_: u8 = 0;
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_758_: u8 = 0;
    let mut v_a_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_762_: u8 = 0;
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_766_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_729_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_709_, v___y_712_, v___y_713_, v___y_714_, v___y_715_,
                );
                if lean_obj_tag(v___x_729_) == 0 {
                    v_a_730_ = lean_ctor_get(v___x_729_, 0);
                    lean_inc_n(v_a_730_, 2);
                    lean_dec_ref_known(v___x_729_, 1);
                    v___x_731_ = lean_unsigned_to_nat(5);
                    lean_inc(v_ids_706_);
                    v___x_732_ = l_Lean_Meta_injections(
                        v_a_730_, v_ids_706_, v___x_731_, v___x_707_, v___y_712_, v___y_713_,
                        v___y_714_, v___y_715_,
                    );
                    if lean_obj_tag(v___x_732_) == 0 {
                        v_a_733_ = lean_ctor_get(v___x_732_, 0);
                        lean_inc(v_a_733_);
                        lean_dec_ref_known(v___x_732_, 1);
                        if lean_obj_tag(v_a_733_) == 0 {
                            v___x_734_ = l_Lean_Elab_Tactic_evalInjections___lam__0___closed__1;
                            v___x_735_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(v___x_734_, v_a_730_, v_ids_706_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
                            if lean_obj_tag(v___x_735_) == 0 {
                                lean_dec_ref_known(v___x_735_, 1);
                                v___x_736_ = lean_box(0);
                                v_a_718_ = v___x_736_;
                                state = 1;
                                continue;
                            } else {
                                return v___x_735_;
                            }
                        } else {
                            lean_dec(v_ids_706_);
                            v_mvarId_737_ = lean_ctor_get(v_a_733_, 0);
                            lean_inc(v_mvarId_737_);
                            v_remainingNames_738_ = lean_ctor_get(v_a_733_, 1);
                            lean_inc(v_remainingNames_738_);
                            lean_dec_ref_known(v_a_733_, 3);
                            v___x_739_ = l_Lean_Elab_Tactic_evalInjections___lam__0___closed__1;
                            v___x_740_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_checkUnusedIds(v___x_739_, v_a_730_, v_remainingNames_738_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
                            if lean_obj_tag(v___x_740_) == 0 {
                                lean_dec_ref_known(v___x_740_, 1);
                                v___x_741_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_tryAssumption(v_mvarId_737_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
                                if lean_obj_tag(v___x_741_) == 0 {
                                    v_a_742_ = lean_ctor_get(v___x_741_, 0);
                                    lean_inc(v_a_742_);
                                    lean_dec_ref_known(v___x_741_, 1);
                                    v_a_718_ = v_a_742_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_743_ = lean_ctor_get(v___x_741_, 0);
                                    v_isSharedCheck_750_ = (!lean_is_exclusive(v___x_741_)) as u8;
                                    if v_isSharedCheck_750_ == 0 {
                                        v___x_745_ = v___x_741_;
                                        v_isShared_746_ = v_isSharedCheck_750_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_a_743_);
                                        lean_dec(v___x_741_);
                                        v___x_745_ = lean_box(0);
                                        v_isShared_746_ = v_isSharedCheck_750_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_mvarId_737_);
                                return v___x_740_;
                            }
                        }
                    } else {
                        lean_dec(v_a_730_);
                        lean_dec(v_ids_706_);
                        v_a_751_ = lean_ctor_get(v___x_732_, 0);
                        v_isSharedCheck_758_ = (!lean_is_exclusive(v___x_732_)) as u8;
                        if v_isSharedCheck_758_ == 0 {
                            v___x_753_ = v___x_732_;
                            v_isShared_754_ = v_isSharedCheck_758_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_751_);
                            lean_dec(v___x_732_);
                            v___x_753_ = lean_box(0);
                            v_isShared_754_ = v_isSharedCheck_758_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_707_);
                    lean_dec(v_ids_706_);
                    v_a_759_ = lean_ctor_get(v___x_729_, 0);
                    v_isSharedCheck_766_ = (!lean_is_exclusive(v___x_729_)) as u8;
                    if v_isSharedCheck_766_ == 0 {
                        v___x_761_ = v___x_729_;
                        v_isShared_762_ = v_isSharedCheck_766_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_759_);
                        lean_dec(v___x_729_);
                        v___x_761_ = lean_box(0);
                        v_isShared_762_ = v_isSharedCheck_766_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_719_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v_a_718_, v___y_709_, v___y_712_, v___y_713_, v___y_714_, v___y_715_,
                );
                if lean_obj_tag(v___x_719_) == 0 {
                    v_isSharedCheck_727_ = (!lean_is_exclusive(v___x_719_)) as u8;
                    if v_isSharedCheck_727_ == 0 {
                        v_unused_728_ = lean_ctor_get(v___x_719_, 0);
                        lean_dec(v_unused_728_);
                        v___x_721_ = v___x_719_;
                        v_isShared_722_ = v_isSharedCheck_727_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_719_);
                        v___x_721_ = lean_box(0);
                        v_isShared_722_ = v_isSharedCheck_727_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_719_;
                }
            }
            2 => {
                v___x_723_ = lean_box(0);
                if v_isShared_722_ == 0 {
                    lean_ctor_set(v___x_721_, 0, v___x_723_);
                    v___x_725_ = v___x_721_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
                    v___x_725_ = v_reuseFailAlloc_726_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_725_;
            }
            4 => {
                if v_isShared_746_ == 0 {
                    v___x_748_ = v___x_745_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
                    v___x_748_ = v_reuseFailAlloc_749_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_748_;
            }
            6 => {
                if v_isShared_754_ == 0 {
                    v___x_756_ = v___x_753_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
                    v___x_756_ = v_reuseFailAlloc_757_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_756_;
            }
            8 => {
                if v_isShared_762_ == 0 {
                    v___x_764_ = v___x_761_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
                    v___x_764_ = v_reuseFailAlloc_765_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_764_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalInjections___lam__0___boxed(
    mut v_ids_767_: *mut LeanObject,
    mut v___x_768_: *mut LeanObject,
    mut v___y_769_: *mut LeanObject,
    mut v___y_770_: *mut LeanObject,
    mut v___y_771_: *mut LeanObject,
    mut v___y_772_: *mut LeanObject,
    mut v___y_773_: *mut LeanObject,
    mut v___y_774_: *mut LeanObject,
    mut v___y_775_: *mut LeanObject,
    mut v___y_776_: *mut LeanObject,
    mut v___y_777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_778_: *mut LeanObject = core::ptr::null_mut();
    v_res_778_ = l_Lean_Elab_Tactic_evalInjections___lam__0(
        v_ids_767_, v___x_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_,
        v___y_774_, v___y_775_, v___y_776_,
    );
    lean_dec(v___y_776_);
    lean_dec_ref(v___y_775_);
    lean_dec(v___y_774_);
    lean_dec_ref(v___y_773_);
    lean_dec(v___y_772_);
    lean_dec_ref(v___y_771_);
    lean_dec(v___y_770_);
    lean_dec_ref(v___y_769_);
    return v_res_778_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalInjections(
    mut v_stx_779_: *mut LeanObject,
    mut v_a_780_: *mut LeanObject,
    mut v_a_781_: *mut LeanObject,
    mut v_a_782_: *mut LeanObject,
    mut v_a_783_: *mut LeanObject,
    mut v_a_784_: *mut LeanObject,
    mut v_a_785_: *mut LeanObject,
    mut v_a_786_: *mut LeanObject,
    mut v_a_787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ids_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    v___x_789_ = lean_box(1);
    v___x_790_ = lean_unsigned_to_nat(1);
    v___x_791_ = l_Lean_Syntax_getArg(v_stx_779_, v___x_790_);
    v___x_792_ = l_Lean_Syntax_getArgs(v___x_791_);
    lean_dec(v___x_791_);
    v___x_793_ = lean_array_to_list(v___x_792_);
    v___x_794_ = lean_box(0);
    v_ids_795_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_getInjectionNewIds_spec__0(v___x_793_, v___x_794_);
    v___f_796_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalInjections___lam__0___boxed as *mut core::ffi::c_void,
        11,
        2,
    );
    lean_closure_set(v___f_796_, 0, v_ids_795_);
    lean_closure_set(v___f_796_, 1, v___x_789_);
    v___x_797_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_796_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_,
    );
    return v___x_797_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalInjections___boxed(
    mut v_stx_798_: *mut LeanObject,
    mut v_a_799_: *mut LeanObject,
    mut v_a_800_: *mut LeanObject,
    mut v_a_801_: *mut LeanObject,
    mut v_a_802_: *mut LeanObject,
    mut v_a_803_: *mut LeanObject,
    mut v_a_804_: *mut LeanObject,
    mut v_a_805_: *mut LeanObject,
    mut v_a_806_: *mut LeanObject,
    mut v_a_807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_808_: *mut LeanObject = core::ptr::null_mut();
    v_res_808_ = l_Lean_Elab_Tactic_evalInjections(
        v_stx_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_,
    );
    lean_dec(v_a_806_);
    lean_dec_ref(v_a_805_);
    lean_dec(v_a_804_);
    lean_dec_ref(v_a_803_);
    lean_dec(v_a_802_);
    lean_dec_ref(v_a_801_);
    lean_dec(v_a_800_);
    lean_dec_ref(v_a_799_);
    lean_dec(v_stx_798_);
    return v_res_808_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1()
-> *mut LeanObject {
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    v___x_821_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_822_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__0;
    v___x_823_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2;
    v___x_824_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalInjections___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_825_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_821_, v___x_822_, v___x_823_, v___x_824_,
    );
    return v___x_825_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___boxed(
    mut v_a_826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_827_: *mut LeanObject = core::ptr::null_mut();
    v_res_827_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1();
    return v_res_827_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3()
-> *mut LeanObject {
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    v___x_854_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1___closed__2;
    v___x_855_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___closed__6;
    v___x_856_ = l_Lean_addBuiltinDeclarationRanges(v___x_854_, v___x_855_);
    return v___x_856_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3___boxed(
    mut v_a_857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_858_: *mut LeanObject = core::ptr::null_mut();
    v_res_858_ = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3();
    return v_res_858_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Injection(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Injection(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Assumption(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjection___regBuiltin_Lean_Elab_Tactic_evalInjection_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Injection_0__Lean_Elab_Tactic_evalInjections___regBuiltin_Lean_Elab_Tactic_evalInjections_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Injection(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Injection(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Injection(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Assumption(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Injection(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Injection(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Injection(builtin);
}

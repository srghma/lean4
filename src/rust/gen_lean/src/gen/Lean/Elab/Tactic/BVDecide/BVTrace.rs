// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.BVTrace
// Imports: Lean.Elab.Tactic.BVDecide.BVCheck Lean.Meta.Tactic.BVDecide.LRAT.Trim
use crate::ffi::{lean_st_ref_get, lean_string_append};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_mkStrLit;
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
};
use crate::r#gen::Init::System::FilePath::{l_System_FilePath_fileName, l_System_FilePath_join};
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::BVDecide::BVCheck::{
    initialize_Lean_Elab_Tactic_BVDecide_BVCheck, l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir,
    l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext,
    runtime_initialize_Lean_Elab_Tactic_BVDecide_BVCheck,
};
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_tacticElabAttribute,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::l_Lean_Elab_Term_getDeclName_x3f___redArg;
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_nil, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofSyntax,
    l_Lean_indentD, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp;
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Attr::l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg;
use crate::r#gen::Lean::Meta::Tactic::BVDecide::LRAT::Trim::{
    initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim, l_Lean_Meta_Tactic_BVDecide_LRAT_trim,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Main::l_Lean_Meta_Tactic_BVDecide_bvDecide;
use crate::r#gen::Lean::Meta::Tactic::TryThis::l_Lean_Meta_Tactic_TryThis_addSuggestion;
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Parser::{
    l_Std_Tactic_BVDecide_LRAT_dumpLRATProof, l_Std_Tactic_BVDecide_LRAT_loadLRATProof,
};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__0_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [45, 0],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__1_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [46, 108, 114, 97, 116, 0],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__2_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 102, 105, 110, 100, 32, 100, 101, 99, 108,
        97, 114, 97, 116, 105, 111, 110, 32, 110, 97, 109, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__4_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 102, 105, 110, 100, 32, 102, 105, 108, 101,
        32, 110, 97, 109, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__0_value:
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
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__1_value:
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
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__2_value:
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
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__3_value:
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
    m_data: [98, 118, 84, 114, 97, 99, 101, 0],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__3_value)
            as *mut crate::leanh::LeanObject,
        10563082290425751099 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__5_value:
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
    m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__6_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__6_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__6_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__6_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__6_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__5_value)
            as *mut crate::leanh::LeanObject,
        3488656302031949961 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__7_value:
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
    m_data: [116, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__7_value)
            as *mut crate::leanh::LeanObject,
        16145843736367156323 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__9_value:
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
    m_data: [98, 118, 67, 104, 101, 99, 107, 0],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__9_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__10_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__10_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__10_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__10_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__10_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__10_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__10_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__9_value)
            as *mut crate::leanh::LeanObject,
        6595225419433550061 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__11_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [98, 118, 95, 99, 104, 101, 99, 107, 0],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__12_value:
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
    m_data: [84, 114, 121, 32, 116, 104, 105, 115, 58, 0],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__13_value:
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
    m_data: [98, 118, 78, 111, 114, 109, 97, 108, 105, 122, 101, 0],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__13_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__14_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__14_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__14_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__14_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__14_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__14_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__14_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__13_value)
            as *mut crate::leanh::LeanObject,
        9992359010160305136 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__15_value:
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
    m_data: [98, 118, 95, 110, 111, 114, 109, 97, 108, 105, 122, 101, 0],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__16_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__17_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__16_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__17_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__1_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [66, 86, 68, 101, 99, 105, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [66, 86, 84, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__3_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 118, 97, 108, 66, 118, 84, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__2_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__1_value) as *mut crate::leanh::LeanObject,11988787035136614332 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__2_value) as *mut crate::leanh::LeanObject,13916995592177097600 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__3_value) as *mut crate::leanh::LeanObject,4136661934514806382 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(
    mut v___y_715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: u8 = 0;
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_725_: u8 = 0;
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_729_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_717_ = crate::leanh::lean_ctor_get(v___y_715_, 5);
                v___x_718_ = 0;
                v___x_719_ = l_Lean_Syntax_getPos_x3f(v_ref_717_, v___x_718_);
                if crate::leanh::lean_obj_tag(v___x_719_) == 0 {
                    v___x_720_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_721_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_721_, 0, v___x_720_);
                    return v___x_721_;
                } else {
                    v_val_722_ = crate::leanh::lean_ctor_get(v___x_719_, 0);
                    v_isSharedCheck_729_ = (!crate::leanh::lean_is_exclusive(v___x_719_)) as u8;
                    if v_isSharedCheck_729_ == 0 {
                        v___x_724_ = v___x_719_;
                        v_isShared_725_ = v_isSharedCheck_729_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_722_);
                        crate::leanh::lean_dec(v___x_719_);
                        v___x_724_ = crate::leanh::lean_box(0);
                        v_isShared_725_ = v_isSharedCheck_729_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_725_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_724_, 0);
                    v___x_727_ = v___x_724_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_728_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_728_, 0, v_val_722_);
                    v___x_727_ = v_reuseFailAlloc_728_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_727_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg___boxed(
    mut v___y_730_: *mut crate::leanh::LeanObject,
    mut v___y_731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_732_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v___y_730_);
    crate::leanh::lean_dec_ref(v___y_730_);
    return v_res_732_;
}
pub unsafe fn l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0(
    mut v___y_733_: *mut crate::leanh::LeanObject,
    mut v___y_734_: *mut crate::leanh::LeanObject,
    mut v___y_735_: *mut crate::leanh::LeanObject,
    mut v___y_736_: *mut crate::leanh::LeanObject,
    mut v___y_737_: *mut crate::leanh::LeanObject,
    mut v___y_738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_740_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v___y_737_);
    return v___x_740_;
}
pub unsafe fn l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___boxed(
    mut v___y_741_: *mut crate::leanh::LeanObject,
    mut v___y_742_: *mut crate::leanh::LeanObject,
    mut v___y_743_: *mut crate::leanh::LeanObject,
    mut v___y_744_: *mut crate::leanh::LeanObject,
    mut v___y_745_: *mut crate::leanh::LeanObject,
    mut v___y_746_: *mut crate::leanh::LeanObject,
    mut v___y_747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_748_ =
        l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0(
            v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_,
        );
    crate::leanh::lean_dec(v___y_746_);
    crate::leanh::lean_dec_ref(v___y_745_);
    crate::leanh::lean_dec(v___y_744_);
    crate::leanh::lean_dec_ref(v___y_743_);
    crate::leanh::lean_dec(v___y_742_);
    crate::leanh::lean_dec_ref(v___y_741_);
    return v_res_748_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__1(
    mut v_msgData_749_: *mut crate::leanh::LeanObject,
    mut v___y_750_: *mut crate::leanh::LeanObject,
    mut v___y_751_: *mut crate::leanh::LeanObject,
    mut v___y_752_: *mut crate::leanh::LeanObject,
    mut v___y_753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_755_ = lean_st_ref_get(v___y_753_);
    v_env_756_ = crate::leanh::lean_ctor_get(v___x_755_, 0);
    crate::leanh::lean_inc_ref(v_env_756_);
    crate::leanh::lean_dec(v___x_755_);
    v___x_757_ = lean_st_ref_get(v___y_751_);
    v_mctx_758_ = crate::leanh::lean_ctor_get(v___x_757_, 0);
    crate::leanh::lean_inc_ref(v_mctx_758_);
    crate::leanh::lean_dec(v___x_757_);
    v_lctx_759_ = crate::leanh::lean_ctor_get(v___y_750_, 2);
    v_options_760_ = crate::leanh::lean_ctor_get(v___y_752_, 2);
    crate::leanh::lean_inc_ref(v_options_760_);
    crate::leanh::lean_inc_ref(v_lctx_759_);
    v___x_761_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_761_, 0, v_env_756_);
    crate::leanh::lean_ctor_set(v___x_761_, 1, v_mctx_758_);
    crate::leanh::lean_ctor_set(v___x_761_, 2, v_lctx_759_);
    crate::leanh::lean_ctor_set(v___x_761_, 3, v_options_760_);
    v___x_762_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_762_, 0, v___x_761_);
    crate::leanh::lean_ctor_set(v___x_762_, 1, v_msgData_749_);
    v___x_763_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_763_, 0, v___x_762_);
    return v___x_763_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__1___boxed(
    mut v_msgData_764_: *mut crate::leanh::LeanObject,
    mut v___y_765_: *mut crate::leanh::LeanObject,
    mut v___y_766_: *mut crate::leanh::LeanObject,
    mut v___y_767_: *mut crate::leanh::LeanObject,
    mut v___y_768_: *mut crate::leanh::LeanObject,
    mut v___y_769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_770_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__1(v_msgData_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
    crate::leanh::lean_dec(v___y_768_);
    crate::leanh::lean_dec_ref(v___y_767_);
    crate::leanh::lean_dec(v___y_766_);
    crate::leanh::lean_dec_ref(v___y_765_);
    return v_res_770_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__3(
    mut v_opts_771_: *mut crate::leanh::LeanObject,
    mut v_opt_772_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_773_ = crate::leanh::lean_ctor_get(v_opt_772_, 0);
    v_defValue_774_ = crate::leanh::lean_ctor_get(v_opt_772_, 1);
    v_map_775_ = crate::leanh::lean_ctor_get(v_opts_771_, 0);
    v___x_776_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_775_,
            v_name_773_,
        );
    if crate::leanh::lean_obj_tag(v___x_776_) == 0 {
        let mut v___x_777_: u8 = 0;
        v___x_777_ = (crate::leanh::lean_unbox(v_defValue_774_) as u8);
        return v___x_777_;
    } else {
        let mut v_val_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_778_ = crate::leanh::lean_ctor_get(v___x_776_, 0);
        crate::leanh::lean_inc(v_val_778_);
        crate::leanh::lean_dec_ref_known(v___x_776_, 1);
        if crate::leanh::lean_obj_tag(v_val_778_) == 1 {
            let mut v_v_779_: u8 = 0;
            v_v_779_ = crate::leanh::lean_ctor_get_uint8(v_val_778_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_778_, 0);
            return v_v_779_;
        } else {
            let mut v___x_780_: u8 = 0;
            crate::leanh::lean_dec(v_val_778_);
            v___x_780_ = (crate::leanh::lean_unbox(v_defValue_774_) as u8);
            return v___x_780_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__3___boxed(
    mut v_opts_781_: *mut crate::leanh::LeanObject,
    mut v_opt_782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_783_: u8 = 0;
    let mut v_r_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_783_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__3(v_opts_781_, v_opt_782_);
    crate::leanh::lean_dec_ref(v_opt_782_);
    crate::leanh::lean_dec_ref(v_opts_781_);
    v_r_784_ = crate::leanh::lean_box((v_res_783_) as usize);
    return v_r_784_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_785_ = crate::leanh::lean_box(1);
    v___x_786_ = l_Lean_MessageData_ofFormat(v___x_785_);
    return v___x_786_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_790_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__2;
    v___x_791_ = l_Lean_MessageData_ofFormat(v___x_790_);
    return v___x_791_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4(
    mut v_x_792_: *mut crate::leanh::LeanObject,
    mut v_x_793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_798_: u8 = 0;
    let mut v_before_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_802_: u8 = 0;
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_815_: u8 = 0;
    let mut v_unused_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_817_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_793_) == 0 {
                    return v_x_792_;
                } else {
                    v_head_794_ = crate::leanh::lean_ctor_get(v_x_793_, 0);
                    v_tail_795_ = crate::leanh::lean_ctor_get(v_x_793_, 1);
                    v_isSharedCheck_817_ = (!crate::leanh::lean_is_exclusive(v_x_793_)) as u8;
                    if v_isSharedCheck_817_ == 0 {
                        v___x_797_ = v_x_793_;
                        v_isShared_798_ = v_isSharedCheck_817_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_795_);
                        crate::leanh::lean_inc(v_head_794_);
                        crate::leanh::lean_dec(v_x_793_);
                        v___x_797_ = crate::leanh::lean_box(0);
                        v_isShared_798_ = v_isSharedCheck_817_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_799_ = crate::leanh::lean_ctor_get(v_head_794_, 0);
                v_isSharedCheck_815_ = (!crate::leanh::lean_is_exclusive(v_head_794_)) as u8;
                if v_isSharedCheck_815_ == 0 {
                    v_unused_816_ = crate::leanh::lean_ctor_get(v_head_794_, 1);
                    crate::leanh::lean_dec(v_unused_816_);
                    v___x_801_ = v_head_794_;
                    v_isShared_802_ = v_isSharedCheck_815_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_799_);
                    crate::leanh::lean_dec(v_head_794_);
                    v___x_801_ = crate::leanh::lean_box(0);
                    v_isShared_802_ = v_isSharedCheck_815_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_803_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0);
                if v_isShared_802_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_801_, 7);
                    crate::leanh::lean_ctor_set(v___x_801_, 1, v___x_803_);
                    crate::leanh::lean_ctor_set(v___x_801_, 0, v_x_792_);
                    v___x_805_ = v___x_801_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_814_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_814_, 0, v_x_792_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_814_, 1, v___x_803_);
                    v___x_805_ = v_reuseFailAlloc_814_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_806_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__3);
                if v_isShared_798_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_797_, 7);
                    crate::leanh::lean_ctor_set(v___x_797_, 1, v___x_806_);
                    crate::leanh::lean_ctor_set(v___x_797_, 0, v___x_805_);
                    v___x_808_ = v___x_797_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_813_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_805_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_813_, 1, v___x_806_);
                    v___x_808_ = v_reuseFailAlloc_813_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_809_ = l_Lean_MessageData_ofSyntax(v_before_799_);
                v___x_810_ = l_Lean_indentD(v___x_809_);
                v___x_811_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_811_, 0, v___x_808_);
                crate::leanh::lean_ctor_set(v___x_811_, 1, v___x_810_);
                v_x_792_ = v___x_811_;
                v_x_793_ = v_tail_795_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_821_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__1;
    v___x_822_ = l_Lean_MessageData_ofFormat(v___x_821_);
    return v___x_822_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg(
    mut v_msgData_823_: *mut crate::leanh::LeanObject,
    mut v_macroStack_824_: *mut crate::leanh::LeanObject,
    mut v___y_825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: u8 = 0;
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_836_: u8 = 0;
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_848_: u8 = 0;
    let mut v_unused_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_827_ = crate::leanh::lean_ctor_get(v___y_825_, 2);
                v___x_828_ = l_Lean_Elab_pp_macroStack;
                v___x_829_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__3(v_options_827_, v___x_828_);
                if v___x_829_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_824_);
                    v___x_830_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_830_, 0, v_msgData_823_);
                    return v___x_830_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_824_) == 0 {
                        v___x_831_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_831_, 0, v_msgData_823_);
                        return v___x_831_;
                    } else {
                        v_head_832_ = crate::leanh::lean_ctor_get(v_macroStack_824_, 0);
                        crate::leanh::lean_inc(v_head_832_);
                        v_after_833_ = crate::leanh::lean_ctor_get(v_head_832_, 1);
                        v_isSharedCheck_848_ =
                            (!crate::leanh::lean_is_exclusive(v_head_832_)) as u8;
                        if v_isSharedCheck_848_ == 0 {
                            v_unused_849_ = crate::leanh::lean_ctor_get(v_head_832_, 0);
                            crate::leanh::lean_dec(v_unused_849_);
                            v___x_835_ = v_head_832_;
                            v_isShared_836_ = v_isSharedCheck_848_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_833_);
                            crate::leanh::lean_dec(v_head_832_);
                            v___x_835_ = crate::leanh::lean_box(0);
                            v_isShared_836_ = v_isSharedCheck_848_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_837_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4___closed__0);
                if v_isShared_836_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_835_, 7);
                    crate::leanh::lean_ctor_set(v___x_835_, 1, v___x_837_);
                    crate::leanh::lean_ctor_set(v___x_835_, 0, v_msgData_823_);
                    v___x_839_ = v___x_835_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_847_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_847_, 0, v_msgData_823_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_847_, 1, v___x_837_);
                    v___x_839_ = v_reuseFailAlloc_847_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_840_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___closed__2);
                v___x_841_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_841_, 0, v___x_839_);
                crate::leanh::lean_ctor_set(v___x_841_, 1, v___x_840_);
                v___x_842_ = l_Lean_MessageData_ofSyntax(v_after_833_);
                v___x_843_ = l_Lean_indentD(v___x_842_);
                v_msgData_844_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_844_, 0, v___x_841_);
                crate::leanh::lean_ctor_set(v_msgData_844_, 1, v___x_843_);
                v___x_845_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2_spec__4(v_msgData_844_, v_macroStack_824_);
                v___x_846_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_846_, 0, v___x_845_);
                return v___x_846_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg___boxed(
    mut v_msgData_850_: *mut crate::leanh::LeanObject,
    mut v_macroStack_851_: *mut crate::leanh::LeanObject,
    mut v___y_852_: *mut crate::leanh::LeanObject,
    mut v___y_853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_854_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg(v_msgData_850_, v_macroStack_851_, v___y_852_);
    crate::leanh::lean_dec_ref(v___y_852_);
    return v_res_854_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1___redArg(
    mut v_msg_855_: *mut crate::leanh::LeanObject,
    mut v___y_856_: *mut crate::leanh::LeanObject,
    mut v___y_857_: *mut crate::leanh::LeanObject,
    mut v___y_858_: *mut crate::leanh::LeanObject,
    mut v___y_859_: *mut crate::leanh::LeanObject,
    mut v___y_860_: *mut crate::leanh::LeanObject,
    mut v___y_861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_872_: u8 = 0;
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_877_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_863_ = crate::leanh::lean_ctor_get(v___y_860_, 5);
                v___x_864_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__1(v_msg_855_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
                v_a_865_ = crate::leanh::lean_ctor_get(v___x_864_, 0);
                crate::leanh::lean_inc(v_a_865_);
                crate::leanh::lean_dec_ref(v___x_864_);
                v_macroStack_866_ = crate::leanh::lean_ctor_get(v___y_856_, 1);
                v___x_867_ = l_Lean_Elab_getBetterRef(v_ref_863_, v_macroStack_866_);
                crate::leanh::lean_inc(v_macroStack_866_);
                v___x_868_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg(v_a_865_, v_macroStack_866_, v___y_860_);
                v_a_869_ = crate::leanh::lean_ctor_get(v___x_868_, 0);
                v_isSharedCheck_877_ = (!crate::leanh::lean_is_exclusive(v___x_868_)) as u8;
                if v_isSharedCheck_877_ == 0 {
                    v___x_871_ = v___x_868_;
                    v_isShared_872_ = v_isSharedCheck_877_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_869_);
                    crate::leanh::lean_dec(v___x_868_);
                    v___x_871_ = crate::leanh::lean_box(0);
                    v_isShared_872_ = v_isSharedCheck_877_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_873_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_873_, 0, v___x_867_);
                crate::leanh::lean_ctor_set(v___x_873_, 1, v_a_869_);
                if v_isShared_872_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_871_, 1);
                    crate::leanh::lean_ctor_set(v___x_871_, 0, v___x_873_);
                    v___x_875_ = v___x_871_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_876_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
                    v___x_875_ = v_reuseFailAlloc_876_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_875_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1___redArg___boxed(
    mut v_msg_878_: *mut crate::leanh::LeanObject,
    mut v___y_879_: *mut crate::leanh::LeanObject,
    mut v___y_880_: *mut crate::leanh::LeanObject,
    mut v___y_881_: *mut crate::leanh::LeanObject,
    mut v___y_882_: *mut crate::leanh::LeanObject,
    mut v___y_883_: *mut crate::leanh::LeanObject,
    mut v___y_884_: *mut crate::leanh::LeanObject,
    mut v___y_885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_886_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1___redArg(v_msg_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
    crate::leanh::lean_dec(v___y_884_);
    crate::leanh::lean_dec_ref(v___y_883_);
    crate::leanh::lean_dec(v___y_882_);
    crate::leanh::lean_dec_ref(v___y_881_);
    crate::leanh::lean_dec(v___y_880_);
    crate::leanh::lean_dec_ref(v___y_879_);
    return v_res_886_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_890_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__2;
    v___x_891_ = l_Lean_stringToMessageData(v___x_890_);
    return v___x_891_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_893_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__4;
    v___x_894_ = l_Lean_stringToMessageData(v___x_893_);
    return v___x_894_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(
    mut v_a_895_: *mut crate::leanh::LeanObject,
    mut v_a_896_: *mut crate::leanh::LeanObject,
    mut v_a_897_: *mut crate::leanh::LeanObject,
    mut v_a_898_: *mut crate::leanh::LeanObject,
    mut v_a_899_: *mut crate::leanh::LeanObject,
    mut v_a_900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_913_: u8 = 0;
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: u8 = 0;
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_933_: u8 = 0;
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_939_: u8 = 0;
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_943_: u8 = 0;
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_902_ = crate::leanh::lean_ctor_get(v_a_899_, 0);
                v_fileMap_903_ = crate::leanh::lean_ctor_get(v_a_899_, 1);
                crate::leanh::lean_inc_ref(v_fileName_902_);
                v___x_904_ = l_System_FilePath_fileName(v_fileName_902_);
                if crate::leanh::lean_obj_tag(v___x_904_) == 1 {
                    v_val_905_ = crate::leanh::lean_ctor_get(v___x_904_, 0);
                    crate::leanh::lean_inc(v_val_905_);
                    crate::leanh::lean_dec_ref_known(v___x_904_, 1);
                    v___x_906_ = l_Lean_Elab_Term_getDeclName_x3f___redArg(v_a_895_);
                    if crate::leanh::lean_obj_tag(v___x_906_) == 0 {
                        v_a_907_ = crate::leanh::lean_ctor_get(v___x_906_, 0);
                        crate::leanh::lean_inc(v_a_907_);
                        crate::leanh::lean_dec_ref_known(v___x_906_, 1);
                        if crate::leanh::lean_obj_tag(v_a_907_) == 1 {
                            v_val_908_ = crate::leanh::lean_ctor_get(v_a_907_, 0);
                            crate::leanh::lean_inc(v_val_908_);
                            crate::leanh::lean_dec_ref_known(v_a_907_, 1);
                            v___x_909_ = l_Lean_getRefPos___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__0___redArg(v_a_899_);
                            v_a_910_ = crate::leanh::lean_ctor_get(v___x_909_, 0);
                            v_isSharedCheck_933_ =
                                (!crate::leanh::lean_is_exclusive(v___x_909_)) as u8;
                            if v_isSharedCheck_933_ == 0 {
                                v___x_912_ = v___x_909_;
                                v_isShared_913_ = v_isSharedCheck_933_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_910_);
                                crate::leanh::lean_dec(v___x_909_);
                                v___x_912_ = crate::leanh::lean_box(0);
                                v_isShared_913_ = v_isSharedCheck_933_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_907_);
                            crate::leanh::lean_dec(v_val_905_);
                            v___x_934_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3_once), _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__3);
                            v___x_935_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1___redArg(v___x_934_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
                            return v___x_935_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_905_);
                        v_a_936_ = crate::leanh::lean_ctor_get(v___x_906_, 0);
                        v_isSharedCheck_943_ = (!crate::leanh::lean_is_exclusive(v___x_906_)) as u8;
                        if v_isSharedCheck_943_ == 0 {
                            v___x_938_ = v___x_906_;
                            v_isShared_939_ = v_isSharedCheck_943_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_936_);
                            crate::leanh::lean_dec(v___x_906_);
                            v___x_938_ = crate::leanh::lean_box(0);
                            v_isShared_939_ = v_isSharedCheck_943_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_904_);
                    v___x_944_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5_once
                        ),
                        _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__5,
                    );
                    v___x_945_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1___redArg(v___x_944_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_);
                    return v___x_945_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_fileMap_903_);
                v___x_914_ = l_Lean_FileMap_toPosition(v_fileMap_903_, v_a_910_);
                crate::leanh::lean_dec(v_a_910_);
                v_line_915_ = crate::leanh::lean_ctor_get(v___x_914_, 0);
                crate::leanh::lean_inc(v_line_915_);
                v_column_916_ = crate::leanh::lean_ctor_get(v___x_914_, 1);
                crate::leanh::lean_inc(v_column_916_);
                crate::leanh::lean_dec_ref(v___x_914_);
                v___x_917_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__0;
                v___x_918_ = lean_string_append(v_val_905_, v___x_917_);
                v___x_919_ = 1;
                v___x_920_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_val_908_, v___x_919_,
                );
                v___x_921_ = lean_string_append(v___x_918_, v___x_920_);
                crate::leanh::lean_dec_ref(v___x_920_);
                v___x_922_ = lean_string_append(v___x_921_, v___x_917_);
                v___x_923_ = l_Nat_reprFast(v_line_915_);
                v___x_924_ = lean_string_append(v___x_922_, v___x_923_);
                crate::leanh::lean_dec_ref(v___x_923_);
                v___x_925_ = lean_string_append(v___x_924_, v___x_917_);
                v___x_926_ = l_Nat_reprFast(v_column_916_);
                v___x_927_ = lean_string_append(v___x_925_, v___x_926_);
                crate::leanh::lean_dec_ref(v___x_926_);
                v___x_928_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___closed__1;
                v___x_929_ = lean_string_append(v___x_927_, v___x_928_);
                if v_isShared_913_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_912_, 0, v___x_929_);
                    v___x_931_ = v___x_912_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_932_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
                    v___x_931_ = v_reuseFailAlloc_932_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_931_;
            }
            3 => {
                if v_isShared_939_ == 0 {
                    v___x_941_ = v___x_938_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_942_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
                    v___x_941_ = v_reuseFailAlloc_942_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_941_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName___boxed(
    mut v_a_946_: *mut crate::leanh::LeanObject,
    mut v_a_947_: *mut crate::leanh::LeanObject,
    mut v_a_948_: *mut crate::leanh::LeanObject,
    mut v_a_949_: *mut crate::leanh::LeanObject,
    mut v_a_950_: *mut crate::leanh::LeanObject,
    mut v_a_951_: *mut crate::leanh::LeanObject,
    mut v_a_952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_953_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(
        v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_,
    );
    crate::leanh::lean_dec(v_a_951_);
    crate::leanh::lean_dec_ref(v_a_950_);
    crate::leanh::lean_dec(v_a_949_);
    crate::leanh::lean_dec_ref(v_a_948_);
    crate::leanh::lean_dec(v_a_947_);
    crate::leanh::lean_dec_ref(v_a_946_);
    return v_res_953_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1(
    mut v_00_u03b1_954_: *mut crate::leanh::LeanObject,
    mut v_msg_955_: *mut crate::leanh::LeanObject,
    mut v___y_956_: *mut crate::leanh::LeanObject,
    mut v___y_957_: *mut crate::leanh::LeanObject,
    mut v___y_958_: *mut crate::leanh::LeanObject,
    mut v___y_959_: *mut crate::leanh::LeanObject,
    mut v___y_960_: *mut crate::leanh::LeanObject,
    mut v___y_961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_963_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1___redArg(v_msg_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
    return v___x_963_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1___boxed(
    mut v_00_u03b1_964_: *mut crate::leanh::LeanObject,
    mut v_msg_965_: *mut crate::leanh::LeanObject,
    mut v___y_966_: *mut crate::leanh::LeanObject,
    mut v___y_967_: *mut crate::leanh::LeanObject,
    mut v___y_968_: *mut crate::leanh::LeanObject,
    mut v___y_969_: *mut crate::leanh::LeanObject,
    mut v___y_970_: *mut crate::leanh::LeanObject,
    mut v___y_971_: *mut crate::leanh::LeanObject,
    mut v___y_972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_973_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1(
            v_00_u03b1_964_,
            v_msg_965_,
            v___y_966_,
            v___y_967_,
            v___y_968_,
            v___y_969_,
            v___y_970_,
            v___y_971_,
        );
    crate::leanh::lean_dec(v___y_971_);
    crate::leanh::lean_dec_ref(v___y_970_);
    crate::leanh::lean_dec(v___y_969_);
    crate::leanh::lean_dec_ref(v___y_968_);
    crate::leanh::lean_dec(v___y_967_);
    crate::leanh::lean_dec_ref(v___y_966_);
    return v_res_973_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2(
    mut v_msgData_974_: *mut crate::leanh::LeanObject,
    mut v_macroStack_975_: *mut crate::leanh::LeanObject,
    mut v___y_976_: *mut crate::leanh::LeanObject,
    mut v___y_977_: *mut crate::leanh::LeanObject,
    mut v___y_978_: *mut crate::leanh::LeanObject,
    mut v___y_979_: *mut crate::leanh::LeanObject,
    mut v___y_980_: *mut crate::leanh::LeanObject,
    mut v___y_981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_983_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___redArg(v_msgData_974_, v_macroStack_975_, v___y_980_);
    return v___x_983_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2___boxed(
    mut v_msgData_984_: *mut crate::leanh::LeanObject,
    mut v_macroStack_985_: *mut crate::leanh::LeanObject,
    mut v___y_986_: *mut crate::leanh::LeanObject,
    mut v___y_987_: *mut crate::leanh::LeanObject,
    mut v___y_988_: *mut crate::leanh::LeanObject,
    mut v___y_989_: *mut crate::leanh::LeanObject,
    mut v___y_990_: *mut crate::leanh::LeanObject,
    mut v___y_991_: *mut crate::leanh::LeanObject,
    mut v___y_992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_993_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName_spec__1_spec__2(v_msgData_984_, v_macroStack_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
    crate::leanh::lean_dec(v___y_991_);
    crate::leanh::lean_dec_ref(v___y_990_);
    crate::leanh::lean_dec(v___y_989_);
    crate::leanh::lean_dec_ref(v___y_988_);
    crate::leanh::lean_dec(v___y_987_);
    crate::leanh::lean_dec_ref(v___y_986_);
    return v_res_993_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_994_ = crate::leanh::lean_box(0);
    v___x_995_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_996_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_996_, 0, v___x_995_);
    crate::leanh::lean_ctor_set(v___x_996_, 1, v___x_994_);
    return v___x_996_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_998_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg___closed__0);
    v___x_999_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_999_, 0, v___x_998_);
    return v___x_999_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg___boxed(
    mut v___y_1000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1001_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg();
    return v_res_1001_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0(
    mut v_00_u03b1_1002_: *mut crate::leanh::LeanObject,
    mut v___y_1003_: *mut crate::leanh::LeanObject,
    mut v___y_1004_: *mut crate::leanh::LeanObject,
    mut v___y_1005_: *mut crate::leanh::LeanObject,
    mut v___y_1006_: *mut crate::leanh::LeanObject,
    mut v___y_1007_: *mut crate::leanh::LeanObject,
    mut v___y_1008_: *mut crate::leanh::LeanObject,
    mut v___y_1009_: *mut crate::leanh::LeanObject,
    mut v___y_1010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1012_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg();
    return v___x_1012_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___boxed(
    mut v_00_u03b1_1013_: *mut crate::leanh::LeanObject,
    mut v___y_1014_: *mut crate::leanh::LeanObject,
    mut v___y_1015_: *mut crate::leanh::LeanObject,
    mut v___y_1016_: *mut crate::leanh::LeanObject,
    mut v___y_1017_: *mut crate::leanh::LeanObject,
    mut v___y_1018_: *mut crate::leanh::LeanObject,
    mut v___y_1019_: *mut crate::leanh::LeanObject,
    mut v___y_1020_: *mut crate::leanh::LeanObject,
    mut v___y_1021_: *mut crate::leanh::LeanObject,
    mut v___y_1022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1023_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0(v_00_u03b1_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
    crate::leanh::lean_dec(v___y_1021_);
    crate::leanh::lean_dec_ref(v___y_1020_);
    crate::leanh::lean_dec(v___y_1019_);
    crate::leanh::lean_dec_ref(v___y_1018_);
    crate::leanh::lean_dec(v___y_1017_);
    crate::leanh::lean_dec_ref(v___y_1016_);
    crate::leanh::lean_dec(v___y_1015_);
    crate::leanh::lean_dec_ref(v___y_1014_);
    return v_res_1023_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0(
    mut v_x_1024_: *mut crate::leanh::LeanObject,
    mut v___y_1025_: *mut crate::leanh::LeanObject,
    mut v___y_1026_: *mut crate::leanh::LeanObject,
    mut v___y_1027_: *mut crate::leanh::LeanObject,
    mut v___y_1028_: *mut crate::leanh::LeanObject,
    mut v___y_1029_: *mut crate::leanh::LeanObject,
    mut v___y_1030_: *mut crate::leanh::LeanObject,
    mut v___y_1031_: *mut crate::leanh::LeanObject,
    mut v___y_1032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1028_);
    crate::leanh::lean_inc_ref(v___y_1027_);
    crate::leanh::lean_inc(v___y_1026_);
    crate::leanh::lean_inc_ref(v___y_1025_);
    v___x_1034_ = crate::leanh::lean_apply_9(
        v_x_1024_,
        v___y_1025_,
        v___y_1026_,
        v___y_1027_,
        v___y_1028_,
        v___y_1029_,
        v___y_1030_,
        v___y_1031_,
        v___y_1032_,
        crate::leanh::lean_box(0),
    );
    return v___x_1034_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0___boxed(
    mut v_x_1035_: *mut crate::leanh::LeanObject,
    mut v___y_1036_: *mut crate::leanh::LeanObject,
    mut v___y_1037_: *mut crate::leanh::LeanObject,
    mut v___y_1038_: *mut crate::leanh::LeanObject,
    mut v___y_1039_: *mut crate::leanh::LeanObject,
    mut v___y_1040_: *mut crate::leanh::LeanObject,
    mut v___y_1041_: *mut crate::leanh::LeanObject,
    mut v___y_1042_: *mut crate::leanh::LeanObject,
    mut v___y_1043_: *mut crate::leanh::LeanObject,
    mut v___y_1044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1045_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0(v_x_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
    crate::leanh::lean_dec(v___y_1039_);
    crate::leanh::lean_dec_ref(v___y_1038_);
    crate::leanh::lean_dec(v___y_1037_);
    crate::leanh::lean_dec_ref(v___y_1036_);
    return v_res_1045_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(
    mut v_mvarId_1046_: *mut crate::leanh::LeanObject,
    mut v_x_1047_: *mut crate::leanh::LeanObject,
    mut v___y_1048_: *mut crate::leanh::LeanObject,
    mut v___y_1049_: *mut crate::leanh::LeanObject,
    mut v___y_1050_: *mut crate::leanh::LeanObject,
    mut v___y_1051_: *mut crate::leanh::LeanObject,
    mut v___y_1052_: *mut crate::leanh::LeanObject,
    mut v___y_1053_: *mut crate::leanh::LeanObject,
    mut v___y_1054_: *mut crate::leanh::LeanObject,
    mut v___y_1055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1062_: u8 = 0;
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1066_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_1051_);
                crate::leanh::lean_inc_ref(v___y_1050_);
                crate::leanh::lean_inc(v___y_1049_);
                crate::leanh::lean_inc_ref(v___y_1048_);
                v___f_1057_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                crate::leanh::lean_closure_set(v___f_1057_, 0, v_x_1047_);
                crate::leanh::lean_closure_set(v___f_1057_, 1, v___y_1048_);
                crate::leanh::lean_closure_set(v___f_1057_, 2, v___y_1049_);
                crate::leanh::lean_closure_set(v___f_1057_, 3, v___y_1050_);
                crate::leanh::lean_closure_set(v___f_1057_, 4, v___y_1051_);
                v___x_1058_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_1046_,
                    v___f_1057_,
                    v___y_1052_,
                    v___y_1053_,
                    v___y_1054_,
                    v___y_1055_,
                );
                if crate::leanh::lean_obj_tag(v___x_1058_) == 0 {
                    return v___x_1058_;
                } else {
                    v_a_1059_ = crate::leanh::lean_ctor_get(v___x_1058_, 0);
                    v_isSharedCheck_1066_ = (!crate::leanh::lean_is_exclusive(v___x_1058_)) as u8;
                    if v_isSharedCheck_1066_ == 0 {
                        v___x_1061_ = v___x_1058_;
                        v_isShared_1062_ = v_isSharedCheck_1066_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1059_);
                        crate::leanh::lean_dec(v___x_1058_);
                        v___x_1061_ = crate::leanh::lean_box(0);
                        v_isShared_1062_ = v_isSharedCheck_1066_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1062_ == 0 {
                    v___x_1064_ = v___x_1061_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1065_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
                    v___x_1064_ = v_reuseFailAlloc_1065_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1064_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg___boxed(
    mut v_mvarId_1067_: *mut crate::leanh::LeanObject,
    mut v_x_1068_: *mut crate::leanh::LeanObject,
    mut v___y_1069_: *mut crate::leanh::LeanObject,
    mut v___y_1070_: *mut crate::leanh::LeanObject,
    mut v___y_1071_: *mut crate::leanh::LeanObject,
    mut v___y_1072_: *mut crate::leanh::LeanObject,
    mut v___y_1073_: *mut crate::leanh::LeanObject,
    mut v___y_1074_: *mut crate::leanh::LeanObject,
    mut v___y_1075_: *mut crate::leanh::LeanObject,
    mut v___y_1076_: *mut crate::leanh::LeanObject,
    mut v___y_1077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1078_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v_mvarId_1067_, v_x_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
    crate::leanh::lean_dec(v___y_1076_);
    crate::leanh::lean_dec_ref(v___y_1075_);
    crate::leanh::lean_dec(v___y_1074_);
    crate::leanh::lean_dec_ref(v___y_1073_);
    crate::leanh::lean_dec(v___y_1072_);
    crate::leanh::lean_dec_ref(v___y_1071_);
    crate::leanh::lean_dec(v___y_1070_);
    crate::leanh::lean_dec_ref(v___y_1069_);
    return v_res_1078_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1(
    mut v_00_u03b1_1079_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1080_: *mut crate::leanh::LeanObject,
    mut v_x_1081_: *mut crate::leanh::LeanObject,
    mut v___y_1082_: *mut crate::leanh::LeanObject,
    mut v___y_1083_: *mut crate::leanh::LeanObject,
    mut v___y_1084_: *mut crate::leanh::LeanObject,
    mut v___y_1085_: *mut crate::leanh::LeanObject,
    mut v___y_1086_: *mut crate::leanh::LeanObject,
    mut v___y_1087_: *mut crate::leanh::LeanObject,
    mut v___y_1088_: *mut crate::leanh::LeanObject,
    mut v___y_1089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1091_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v_mvarId_1080_, v_x_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
    return v___x_1091_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___boxed(
    mut v_00_u03b1_1092_: *mut crate::leanh::LeanObject,
    mut v_mvarId_1093_: *mut crate::leanh::LeanObject,
    mut v_x_1094_: *mut crate::leanh::LeanObject,
    mut v___y_1095_: *mut crate::leanh::LeanObject,
    mut v___y_1096_: *mut crate::leanh::LeanObject,
    mut v___y_1097_: *mut crate::leanh::LeanObject,
    mut v___y_1098_: *mut crate::leanh::LeanObject,
    mut v___y_1099_: *mut crate::leanh::LeanObject,
    mut v___y_1100_: *mut crate::leanh::LeanObject,
    mut v___y_1101_: *mut crate::leanh::LeanObject,
    mut v___y_1102_: *mut crate::leanh::LeanObject,
    mut v___y_1103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1104_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1(
            v_00_u03b1_1092_,
            v_mvarId_1093_,
            v_x_1094_,
            v___y_1095_,
            v___y_1096_,
            v___y_1097_,
            v___y_1098_,
            v___y_1099_,
            v___y_1100_,
            v___y_1101_,
            v___y_1102_,
        );
    crate::leanh::lean_dec(v___y_1102_);
    crate::leanh::lean_dec_ref(v___y_1101_);
    crate::leanh::lean_dec(v___y_1100_);
    crate::leanh::lean_dec_ref(v___y_1099_);
    crate::leanh::lean_dec(v___y_1098_);
    crate::leanh::lean_dec_ref(v___y_1097_);
    crate::leanh::lean_dec(v___y_1096_);
    crate::leanh::lean_dec_ref(v___y_1095_);
    return v_res_1104_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(
    mut v_e_1105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1110_: u8 = 0;
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1115_: u8 = 0;
    let mut v_a_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1119_: u8 = 0;
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1123_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_1105_) == 0 {
                    v_a_1107_ = crate::leanh::lean_ctor_get(v_e_1105_, 0);
                    v_isSharedCheck_1115_ = (!crate::leanh::lean_is_exclusive(v_e_1105_)) as u8;
                    if v_isSharedCheck_1115_ == 0 {
                        v___x_1109_ = v_e_1105_;
                        v_isShared_1110_ = v_isSharedCheck_1115_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1107_);
                        crate::leanh::lean_dec(v_e_1105_);
                        v___x_1109_ = crate::leanh::lean_box(0);
                        v_isShared_1110_ = v_isSharedCheck_1115_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1116_ = crate::leanh::lean_ctor_get(v_e_1105_, 0);
                    v_isSharedCheck_1123_ = (!crate::leanh::lean_is_exclusive(v_e_1105_)) as u8;
                    if v_isSharedCheck_1123_ == 0 {
                        v___x_1118_ = v_e_1105_;
                        v_isShared_1119_ = v_isSharedCheck_1123_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1116_);
                        crate::leanh::lean_dec(v_e_1105_);
                        v___x_1118_ = crate::leanh::lean_box(0);
                        v_isShared_1119_ = v_isSharedCheck_1123_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1111_ = lean_mk_io_user_error(v_a_1107_);
                if v_isShared_1110_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1109_, 1);
                    crate::leanh::lean_ctor_set(v___x_1109_, 0, v___x_1111_);
                    v___x_1113_ = v___x_1109_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1114_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1111_);
                    v___x_1113_ = v_reuseFailAlloc_1114_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1113_;
            }
            3 => {
                if v_isShared_1119_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1118_, 0);
                    v___x_1121_ = v___x_1118_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1122_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
                    v___x_1121_ = v_reuseFailAlloc_1122_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1121_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg___boxed(
    mut v_e_1124_: *mut crate::leanh::LeanObject,
    mut v_a_1125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1126_ =
        l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(
            v_e_1124_,
        );
    return v_res_1126_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2(
    mut v_00_u03b1_1127_: *mut crate::leanh::LeanObject,
    mut v_e_1128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1130_ =
        l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(
            v_e_1128_,
        );
    return v___x_1130_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___boxed(
    mut v_00_u03b1_1131_: *mut crate::leanh::LeanObject,
    mut v_e_1132_: *mut crate::leanh::LeanObject,
    mut v_a_1133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1134_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2(
        v_00_u03b1_1131_,
        v_e_1132_,
    );
    return v_res_1134_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___lam__0(
    mut v_a_1135_: *mut crate::leanh::LeanObject,
    mut v_a_1136_: *mut crate::leanh::LeanObject,
    mut v___y_1137_: *mut crate::leanh::LeanObject,
    mut v___y_1138_: *mut crate::leanh::LeanObject,
    mut v___y_1139_: *mut crate::leanh::LeanObject,
    mut v___y_1140_: *mut crate::leanh::LeanObject,
    mut v___y_1141_: *mut crate::leanh::LeanObject,
    mut v___y_1142_: *mut crate::leanh::LeanObject,
    mut v___y_1143_: *mut crate::leanh::LeanObject,
    mut v___y_1144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1146_ = l_Lean_Meta_Tactic_BVDecide_bvDecide(
        v_a_1135_,
        v_a_1136_,
        v___y_1141_,
        v___y_1142_,
        v___y_1143_,
        v___y_1144_,
    );
    return v___x_1146_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___lam__0___boxed(
    mut v_a_1147_: *mut crate::leanh::LeanObject,
    mut v_a_1148_: *mut crate::leanh::LeanObject,
    mut v___y_1149_: *mut crate::leanh::LeanObject,
    mut v___y_1150_: *mut crate::leanh::LeanObject,
    mut v___y_1151_: *mut crate::leanh::LeanObject,
    mut v___y_1152_: *mut crate::leanh::LeanObject,
    mut v___y_1153_: *mut crate::leanh::LeanObject,
    mut v___y_1154_: *mut crate::leanh::LeanObject,
    mut v___y_1155_: *mut crate::leanh::LeanObject,
    mut v___y_1156_: *mut crate::leanh::LeanObject,
    mut v___y_1157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1158_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___lam__0(
        v_a_1147_,
        v_a_1148_,
        v___y_1149_,
        v___y_1150_,
        v___y_1151_,
        v___y_1152_,
        v___y_1153_,
        v___y_1154_,
        v___y_1155_,
        v___y_1156_,
    );
    crate::leanh::lean_dec(v___y_1156_);
    crate::leanh::lean_dec_ref(v___y_1155_);
    crate::leanh::lean_dec(v___y_1154_);
    crate::leanh::lean_dec_ref(v___y_1153_);
    crate::leanh::lean_dec(v___y_1152_);
    crate::leanh::lean_dec_ref(v___y_1151_);
    crate::leanh::lean_dec(v___y_1150_);
    crate::leanh::lean_dec_ref(v___y_1149_);
    return v_res_1158_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1195_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_1195_;
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(
    mut v_x_1196_: *mut crate::leanh::LeanObject,
    mut v_a_1197_: *mut crate::leanh::LeanObject,
    mut v_a_1198_: *mut crate::leanh::LeanObject,
    mut v_a_1199_: *mut crate::leanh::LeanObject,
    mut v_a_1200_: *mut crate::leanh::LeanObject,
    mut v_a_1201_: *mut crate::leanh::LeanObject,
    mut v_a_1202_: *mut crate::leanh::LeanObject,
    mut v_a_1203_: *mut crate::leanh::LeanObject,
    mut v_a_1204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: u8 = 0;
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: u8 = 0;
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: u8 = 0;
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: u8 = 0;
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_timeout_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binaryProofs_1224_: u8 = 0;
    let mut v_acNf_1225_: u8 = 0;
    let mut v_andFlattening_1226_: u8 = 0;
    let mut v_embeddedConstraintSubst_1227_: u8 = 0;
    let mut v_structures_1228_: u8 = 0;
    let mut v_fixedInt_1229_: u8 = 0;
    let mut v_enums_1230_: u8 = 0;
    let mut v_graphviz_1231_: u8 = 0;
    let mut v_maxSteps_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_shortCircuit_1233_: u8 = 0;
    let mut v_solverMode_1234_: u8 = 0;
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1237_: u8 = 0;
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: u8 = 0;
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: u8 = 0;
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1290_: u8 = 0;
    let mut v_config_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trimProofs_1292_: u8 = 0;
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1305_: u8 = 0;
    let mut v_ref_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1316_: u8 = 0;
    let mut v_a_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1320_: u8 = 0;
    let mut v_ref_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1331_: u8 = 0;
    let mut v_a_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1335_: u8 = 0;
    let mut v_ref_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1346_: u8 = 0;
    let mut v_a_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1350_: u8 = 0;
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1354_: u8 = 0;
    let mut v_isSharedCheck_1355_: u8 = 0;
    let mut v_unused_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1360_: u8 = 0;
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1364_: u8 = 0;
    let mut v_a_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1368_: u8 = 0;
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1372_: u8 = 0;
    let mut v_a_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1376_: u8 = 0;
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1380_: u8 = 0;
    let mut v_reuseFailAlloc_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1382_: u8 = 0;
    let mut v_a_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1386_: u8 = 0;
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1390_: u8 = 0;
    let mut v_a_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1394_: u8 = 0;
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1398_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1206_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__4;
                crate::leanh::lean_inc(v_x_1196_);
                v___x_1207_ = l_Lean_Syntax_isOfKind(v_x_1196_, v___x_1206_);
                if v___x_1207_ == 0 {
                    crate::leanh::lean_dec(v_x_1196_);
                    v___x_1208_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg();
                    return v___x_1208_;
                } else {
                    v___x_1209_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1210_ = l_Lean_Syntax_getArg(v_x_1196_, v___x_1209_);
                    v___x_1211_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__6;
                    crate::leanh::lean_inc(v___x_1210_);
                    v___x_1212_ = l_Lean_Syntax_isOfKind(v___x_1210_, v___x_1211_);
                    if v___x_1212_ == 0 {
                        crate::leanh::lean_dec(v___x_1210_);
                        crate::leanh::lean_dec(v_x_1196_);
                        v___x_1213_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__0___redArg();
                        return v___x_1213_;
                    } else {
                        v___x_1214_ = crate::leanh::lean_unsigned_to_nat(10);
                        v___x_1215_ = 0;
                        v___x_1216_ = crate::leanh::lean_unsigned_to_nat(100000);
                        v___x_1217_ = 0;
                        v___x_1218_ = crate::leanh::lean_alloc_ctor(0, 2, (11) as u32);
                        crate::leanh::lean_ctor_set(v___x_1218_, 0, v___x_1214_);
                        crate::leanh::lean_ctor_set(v___x_1218_, 1, v___x_1216_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1218_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                            v___x_1212_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1218_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                            v___x_1212_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1218_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 2) as u32,
                            v___x_1215_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1218_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 3) as u32,
                            v___x_1212_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1218_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 4) as u32,
                            v___x_1212_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1218_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 5) as u32,
                            v___x_1212_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1218_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 6) as u32,
                            v___x_1212_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1218_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 7) as u32,
                            v___x_1212_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1218_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 8) as u32,
                            v___x_1215_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1218_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 9) as u32,
                            v___x_1215_,
                        );
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1218_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 10) as u32,
                            v___x_1217_,
                        );
                        crate::leanh::lean_inc(v___x_1210_);
                        v___x_1219_ = l_Lean_Meta_Tactic_BVDecide_elabBVDecideConfig___redArg(
                            v___x_1210_,
                            v___x_1218_,
                            v___x_1212_,
                            v_a_1197_,
                            v_a_1203_,
                            v_a_1204_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1219_) == 0 {
                            v_a_1220_ = crate::leanh::lean_ctor_get(v___x_1219_, 0);
                            crate::leanh::lean_inc(v_a_1220_);
                            crate::leanh::lean_dec_ref_known(v___x_1219_, 1);
                            v___x_1221_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_getLratFileName(
                                v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1221_) == 0 {
                                v_a_1222_ = crate::leanh::lean_ctor_get(v___x_1221_, 0);
                                crate::leanh::lean_inc(v_a_1222_);
                                crate::leanh::lean_dec_ref_known(v___x_1221_, 1);
                                v_timeout_1223_ = crate::leanh::lean_ctor_get(v_a_1220_, 0);
                                v_binaryProofs_1224_ = crate::leanh::lean_ctor_get_uint8(
                                    v_a_1220_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1)
                                        as u32,
                                );
                                v_acNf_1225_ = crate::leanh::lean_ctor_get_uint8(
                                    v_a_1220_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 2)
                                        as u32,
                                );
                                v_andFlattening_1226_ = crate::leanh::lean_ctor_get_uint8(
                                    v_a_1220_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 3)
                                        as u32,
                                );
                                v_embeddedConstraintSubst_1227_ = crate::leanh::lean_ctor_get_uint8(
                                    v_a_1220_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 4)
                                        as u32,
                                );
                                v_structures_1228_ = crate::leanh::lean_ctor_get_uint8(
                                    v_a_1220_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 5)
                                        as u32,
                                );
                                v_fixedInt_1229_ = crate::leanh::lean_ctor_get_uint8(
                                    v_a_1220_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 6)
                                        as u32,
                                );
                                v_enums_1230_ = crate::leanh::lean_ctor_get_uint8(
                                    v_a_1220_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 7)
                                        as u32,
                                );
                                v_graphviz_1231_ = crate::leanh::lean_ctor_get_uint8(
                                    v_a_1220_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 8)
                                        as u32,
                                );
                                v_maxSteps_1232_ = crate::leanh::lean_ctor_get(v_a_1220_, 1);
                                v_shortCircuit_1233_ = crate::leanh::lean_ctor_get_uint8(
                                    v_a_1220_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 9)
                                        as u32,
                                );
                                v_solverMode_1234_ = crate::leanh::lean_ctor_get_uint8(
                                    v_a_1220_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 10)
                                        as u32,
                                );
                                v_isSharedCheck_1382_ =
                                    (!crate::leanh::lean_is_exclusive(v_a_1220_)) as u8;
                                if v_isSharedCheck_1382_ == 0 {
                                    v___x_1236_ = v_a_1220_;
                                    v_isShared_1237_ = v_isSharedCheck_1382_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_maxSteps_1232_);
                                    crate::leanh::lean_inc(v_timeout_1223_);
                                    crate::leanh::lean_dec(v_a_1220_);
                                    v___x_1236_ = crate::leanh::lean_box(0);
                                    v_isShared_1237_ = v_isSharedCheck_1382_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1220_);
                                crate::leanh::lean_dec(v___x_1210_);
                                crate::leanh::lean_dec(v_x_1196_);
                                v_a_1383_ = crate::leanh::lean_ctor_get(v___x_1221_, 0);
                                v_isSharedCheck_1390_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1221_)) as u8;
                                if v_isSharedCheck_1390_ == 0 {
                                    v___x_1385_ = v___x_1221_;
                                    v_isShared_1386_ = v_isSharedCheck_1390_;
                                    state = 22;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1383_);
                                    crate::leanh::lean_dec(v___x_1221_);
                                    v___x_1385_ = crate::leanh::lean_box(0);
                                    v_isShared_1386_ = v_isSharedCheck_1390_;
                                    state = 22;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_1210_);
                            crate::leanh::lean_dec(v_x_1196_);
                            v_a_1391_ = crate::leanh::lean_ctor_get(v___x_1219_, 0);
                            v_isSharedCheck_1398_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1219_)) as u8;
                            if v_isSharedCheck_1398_ == 0 {
                                v___x_1393_ = v___x_1219_;
                                v_isShared_1394_ = v_isSharedCheck_1398_;
                                state = 24;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1391_);
                                crate::leanh::lean_dec(v___x_1219_);
                                v___x_1393_ = crate::leanh::lean_box(0);
                                v_isShared_1394_ = v_isSharedCheck_1398_;
                                state = 24;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1237_ == 0 {
                    v___x_1239_ = v___x_1236_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1381_ = crate::leanh::lean_alloc_ctor(0, 2, (11) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_timeout_1223_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_maxSteps_1232_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1381_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 1) as u32,
                        v_binaryProofs_1224_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1381_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 2) as u32,
                        v_acNf_1225_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1381_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 3) as u32,
                        v_andFlattening_1226_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1381_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 4) as u32,
                        v_embeddedConstraintSubst_1227_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1381_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 5) as u32,
                        v_structures_1228_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1381_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 6) as u32,
                        v_fixedInt_1229_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1381_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 7) as u32,
                        v_enums_1230_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1381_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 8) as u32,
                        v_graphviz_1231_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1381_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 9) as u32,
                        v_shortCircuit_1233_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1381_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 10) as u32,
                        v_solverMode_1234_,
                    );
                    v___x_1239_ = v_reuseFailAlloc_1381_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1239_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_1215_,
                );
                crate::leanh::lean_inc(v_a_1222_);
                v___x_1240_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_mkContext(
                    v_a_1222_,
                    v___x_1239_,
                    v_a_1199_,
                    v_a_1200_,
                    v_a_1201_,
                    v_a_1202_,
                    v_a_1203_,
                    v_a_1204_,
                );
                if crate::leanh::lean_obj_tag(v___x_1240_) == 0 {
                    v_a_1241_ = crate::leanh::lean_ctor_get(v___x_1240_, 0);
                    crate::leanh::lean_inc(v_a_1241_);
                    crate::leanh::lean_dec_ref_known(v___x_1240_, 1);
                    v___x_1242_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                        v_a_1198_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1242_) == 0 {
                        v_a_1243_ = crate::leanh::lean_ctor_get(v___x_1242_, 0);
                        crate::leanh::lean_inc_n(v_a_1243_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_1242_, 1);
                        crate::leanh::lean_inc(v_a_1241_);
                        v___f_1244_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___lam__0___boxed
                                as *mut core::ffi::c_void,
                            11,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___f_1244_, 0, v_a_1243_);
                        crate::leanh::lean_closure_set(v___f_1244_, 1, v_a_1241_);
                        v___x_1245_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__1___redArg(v_a_1243_, v___f_1244_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
                        if crate::leanh::lean_obj_tag(v___x_1245_) == 0 {
                            v_a_1246_ = crate::leanh::lean_ctor_get(v___x_1245_, 0);
                            crate::leanh::lean_inc(v_a_1246_);
                            crate::leanh::lean_dec_ref_known(v___x_1245_, 1);
                            v___x_1247_ = crate::leanh::lean_unsigned_to_nat(0);
                            v_tk_1248_ = l_Lean_Syntax_getArg(v_x_1196_, v___x_1247_);
                            crate::leanh::lean_dec(v_x_1196_);
                            if crate::leanh::lean_obj_tag(v_a_1246_) == 0 {
                                crate::leanh::lean_dec(v_a_1241_);
                                crate::leanh::lean_dec(v_a_1222_);
                                crate::leanh::lean_dec(v___x_1210_);
                                v_ref_1269_ = crate::leanh::lean_ctor_get(v_a_1203_, 5);
                                v___x_1270_ = l_Lean_SourceInfo_fromRef(v_ref_1269_, v___x_1215_);
                                v___x_1271_ =
                                    l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__8;
                                v___x_1272_ =
                                    l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__14;
                                v___x_1273_ =
                                    l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__15;
                                crate::leanh::lean_inc_n(v___x_1270_, 3);
                                v___x_1274_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1274_, 0, v___x_1270_);
                                crate::leanh::lean_ctor_set(v___x_1274_, 1, v___x_1273_);
                                v___x_1275_ =
                                    l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__17;
                                v___x_1276_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__18), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__18_once), _init_l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__18);
                                v___x_1277_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1277_, 0, v___x_1270_);
                                crate::leanh::lean_ctor_set(v___x_1277_, 1, v___x_1275_);
                                crate::leanh::lean_ctor_set(v___x_1277_, 2, v___x_1276_);
                                v___x_1278_ =
                                    l_Lean_Syntax_node1(v___x_1270_, v___x_1211_, v___x_1277_);
                                v___x_1279_ = l_Lean_Syntax_node2(
                                    v___x_1270_,
                                    v___x_1272_,
                                    v___x_1274_,
                                    v___x_1278_,
                                );
                                v___x_1280_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1280_, 0, v___x_1271_);
                                crate::leanh::lean_ctor_set(v___x_1280_, 1, v___x_1279_);
                                v___x_1281_ = crate::leanh::lean_box(0);
                                v___x_1282_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1282_, 0, v___x_1280_);
                                crate::leanh::lean_ctor_set(v___x_1282_, 1, v_a_1246_);
                                crate::leanh::lean_ctor_set(v___x_1282_, 2, v_a_1246_);
                                crate::leanh::lean_ctor_set(v___x_1282_, 3, v___x_1281_);
                                crate::leanh::lean_ctor_set(v___x_1282_, 4, v___x_1281_);
                                crate::leanh::lean_ctor_set(v___x_1282_, 5, v___x_1281_);
                                crate::leanh::lean_inc(v_ref_1269_);
                                v___x_1283_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1283_, 0, v_ref_1269_);
                                v___x_1284_ =
                                    l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__12;
                                v___x_1285_ = 4;
                                v___x_1286_ = l_Lean_MessageData_nil;
                                v___x_1287_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(
                                    v_tk_1248_,
                                    v___x_1282_,
                                    v___x_1283_,
                                    v___x_1284_,
                                    v_a_1246_,
                                    v___x_1285_,
                                    v___x_1286_,
                                    v_a_1203_,
                                    v_a_1204_,
                                );
                                return v___x_1287_;
                            } else {
                                v_isSharedCheck_1355_ =
                                    (!crate::leanh::lean_is_exclusive(v_a_1246_)) as u8;
                                if v_isSharedCheck_1355_ == 0 {
                                    v_unused_1356_ = crate::leanh::lean_ctor_get(v_a_1246_, 0);
                                    crate::leanh::lean_dec(v_unused_1356_);
                                    v___x_1289_ = v_a_1246_;
                                    v_isShared_1290_ = v_isSharedCheck_1355_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_1246_);
                                    v___x_1289_ = crate::leanh::lean_box(0);
                                    v_isShared_1290_ = v_isSharedCheck_1355_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1241_);
                            crate::leanh::lean_dec(v_a_1222_);
                            crate::leanh::lean_dec(v___x_1210_);
                            crate::leanh::lean_dec(v_x_1196_);
                            v_a_1357_ = crate::leanh::lean_ctor_get(v___x_1245_, 0);
                            v_isSharedCheck_1364_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1245_)) as u8;
                            if v_isSharedCheck_1364_ == 0 {
                                v___x_1359_ = v___x_1245_;
                                v_isShared_1360_ = v_isSharedCheck_1364_;
                                state = 16;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1357_);
                                crate::leanh::lean_dec(v___x_1245_);
                                v___x_1359_ = crate::leanh::lean_box(0);
                                v_isShared_1360_ = v_isSharedCheck_1364_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1241_);
                        crate::leanh::lean_dec(v_a_1222_);
                        crate::leanh::lean_dec(v___x_1210_);
                        crate::leanh::lean_dec(v_x_1196_);
                        v_a_1365_ = crate::leanh::lean_ctor_get(v___x_1242_, 0);
                        v_isSharedCheck_1372_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1242_)) as u8;
                        if v_isSharedCheck_1372_ == 0 {
                            v___x_1367_ = v___x_1242_;
                            v_isShared_1368_ = v_isSharedCheck_1372_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1365_);
                            crate::leanh::lean_dec(v___x_1242_);
                            v___x_1367_ = crate::leanh::lean_box(0);
                            v_isShared_1368_ = v_isSharedCheck_1372_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1222_);
                    crate::leanh::lean_dec(v___x_1210_);
                    crate::leanh::lean_dec(v_x_1196_);
                    v_a_1373_ = crate::leanh::lean_ctor_get(v___x_1240_, 0);
                    v_isSharedCheck_1380_ = (!crate::leanh::lean_is_exclusive(v___x_1240_)) as u8;
                    if v_isSharedCheck_1380_ == 0 {
                        v___x_1375_ = v___x_1240_;
                        v_isShared_1376_ = v_isSharedCheck_1380_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1373_);
                        crate::leanh::lean_dec(v___x_1240_);
                        v___x_1375_ = crate::leanh::lean_box(0);
                        v_isShared_1376_ = v_isSharedCheck_1380_;
                        state = 20;
                        continue;
                    }
                }
            }
            3 => {
                v_ref_1252_ = crate::leanh::lean_ctor_get(v___y_1250_, 5);
                v___x_1253_ = l_Lean_SourceInfo_fromRef(v_ref_1252_, v___x_1215_);
                v___x_1254_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__8;
                v___x_1255_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__10;
                v___x_1256_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__11;
                crate::leanh::lean_inc(v___x_1253_);
                v___x_1257_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1257_, 0, v___x_1253_);
                crate::leanh::lean_ctor_set(v___x_1257_, 1, v___x_1256_);
                v___x_1258_ = crate::leanh::lean_box(2);
                v___x_1259_ = l_Lean_Syntax_mkStrLit(v_a_1222_, v___x_1258_);
                v___x_1260_ = l_Lean_Syntax_node3(
                    v___x_1253_,
                    v___x_1255_,
                    v___x_1257_,
                    v___x_1210_,
                    v___x_1259_,
                );
                v___x_1261_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1261_, 0, v___x_1254_);
                crate::leanh::lean_ctor_set(v___x_1261_, 1, v___x_1260_);
                v___x_1262_ = crate::leanh::lean_box(0);
                v___x_1263_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1263_, 0, v___x_1261_);
                crate::leanh::lean_ctor_set(v___x_1263_, 1, v___x_1262_);
                crate::leanh::lean_ctor_set(v___x_1263_, 2, v___x_1262_);
                crate::leanh::lean_ctor_set(v___x_1263_, 3, v___x_1262_);
                crate::leanh::lean_ctor_set(v___x_1263_, 4, v___x_1262_);
                crate::leanh::lean_ctor_set(v___x_1263_, 5, v___x_1262_);
                crate::leanh::lean_inc(v_ref_1252_);
                v___x_1264_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1264_, 0, v_ref_1252_);
                v___x_1265_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__12;
                v___x_1266_ = 4;
                v___x_1267_ = l_Lean_MessageData_nil;
                v___x_1268_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(
                    v_tk_1248_,
                    v___x_1263_,
                    v___x_1264_,
                    v___x_1265_,
                    v___x_1262_,
                    v___x_1266_,
                    v___x_1267_,
                    v___y_1250_,
                    v___y_1251_,
                );
                return v___x_1268_;
            }
            4 => {
                v_config_1291_ = crate::leanh::lean_ctor_get(v_a_1241_, 5);
                crate::leanh::lean_inc_ref(v_config_1291_);
                crate::leanh::lean_dec(v_a_1241_);
                v_trimProofs_1292_ = crate::leanh::lean_ctor_get_uint8(
                    v_config_1291_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                crate::leanh::lean_dec_ref(v_config_1291_);
                if v_trimProofs_1292_ == 0 {
                    crate::leanh::lean_del_object(v___x_1289_);
                    v___y_1250_ = v_a_1203_;
                    v___y_1251_ = v_a_1204_;
                    state = 3;
                    continue;
                } else {
                    v___x_1293_ = l_Lean_Elab_Tactic_BVDecide_BVCheck_getSrcDir(
                        v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1293_) == 0 {
                        v_a_1294_ = crate::leanh::lean_ctor_get(v___x_1293_, 0);
                        crate::leanh::lean_inc(v_a_1294_);
                        crate::leanh::lean_dec_ref_known(v___x_1293_, 1);
                        crate::leanh::lean_inc(v_a_1222_);
                        v___x_1295_ = l_System_FilePath_join(v_a_1294_, v_a_1222_);
                        v___x_1296_ = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(v___x_1295_);
                        if crate::leanh::lean_obj_tag(v___x_1296_) == 0 {
                            v_a_1297_ = crate::leanh::lean_ctor_get(v___x_1296_, 0);
                            crate::leanh::lean_inc(v_a_1297_);
                            crate::leanh::lean_dec_ref_known(v___x_1296_, 1);
                            v___x_1298_ = l_Lean_Meta_Tactic_BVDecide_LRAT_trim(v_a_1297_);
                            crate::leanh::lean_dec(v_a_1297_);
                            v___x_1299_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace_spec__2___redArg(v___x_1298_);
                            if crate::leanh::lean_obj_tag(v___x_1299_) == 0 {
                                v_a_1300_ = crate::leanh::lean_ctor_get(v___x_1299_, 0);
                                crate::leanh::lean_inc(v_a_1300_);
                                crate::leanh::lean_dec_ref_known(v___x_1299_, 1);
                                v___x_1301_ = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(
                                    v___x_1295_,
                                    v_a_1300_,
                                    v_binaryProofs_1224_,
                                );
                                crate::leanh::lean_dec(v_a_1300_);
                                crate::leanh::lean_dec_ref(v___x_1295_);
                                if crate::leanh::lean_obj_tag(v___x_1301_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_1301_, 1);
                                    crate::leanh::lean_del_object(v___x_1289_);
                                    v___y_1250_ = v_a_1203_;
                                    v___y_1251_ = v_a_1204_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_tk_1248_);
                                    crate::leanh::lean_dec(v_a_1222_);
                                    crate::leanh::lean_dec(v___x_1210_);
                                    v_a_1302_ = crate::leanh::lean_ctor_get(v___x_1301_, 0);
                                    v_isSharedCheck_1316_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1301_)) as u8;
                                    if v_isSharedCheck_1316_ == 0 {
                                        v___x_1304_ = v___x_1301_;
                                        v_isShared_1305_ = v_isSharedCheck_1316_;
                                        state = 5;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1302_);
                                        crate::leanh::lean_dec(v___x_1301_);
                                        v___x_1304_ = crate::leanh::lean_box(0);
                                        v_isShared_1305_ = v_isSharedCheck_1316_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_1295_);
                                crate::leanh::lean_dec(v_tk_1248_);
                                crate::leanh::lean_dec(v_a_1222_);
                                crate::leanh::lean_dec(v___x_1210_);
                                v_a_1317_ = crate::leanh::lean_ctor_get(v___x_1299_, 0);
                                v_isSharedCheck_1331_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1299_)) as u8;
                                if v_isSharedCheck_1331_ == 0 {
                                    v___x_1319_ = v___x_1299_;
                                    v_isShared_1320_ = v_isSharedCheck_1331_;
                                    state = 8;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1317_);
                                    crate::leanh::lean_dec(v___x_1299_);
                                    v___x_1319_ = crate::leanh::lean_box(0);
                                    v_isShared_1320_ = v_isSharedCheck_1331_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_1295_);
                            crate::leanh::lean_dec(v_tk_1248_);
                            crate::leanh::lean_dec(v_a_1222_);
                            crate::leanh::lean_dec(v___x_1210_);
                            v_a_1332_ = crate::leanh::lean_ctor_get(v___x_1296_, 0);
                            v_isSharedCheck_1346_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1296_)) as u8;
                            if v_isSharedCheck_1346_ == 0 {
                                v___x_1334_ = v___x_1296_;
                                v_isShared_1335_ = v_isSharedCheck_1346_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1332_);
                                crate::leanh::lean_dec(v___x_1296_);
                                v___x_1334_ = crate::leanh::lean_box(0);
                                v_isShared_1335_ = v_isSharedCheck_1346_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1289_);
                        crate::leanh::lean_dec(v_tk_1248_);
                        crate::leanh::lean_dec(v_a_1222_);
                        crate::leanh::lean_dec(v___x_1210_);
                        v_a_1347_ = crate::leanh::lean_ctor_get(v___x_1293_, 0);
                        v_isSharedCheck_1354_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1293_)) as u8;
                        if v_isSharedCheck_1354_ == 0 {
                            v___x_1349_ = v___x_1293_;
                            v_isShared_1350_ = v_isSharedCheck_1354_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1347_);
                            crate::leanh::lean_dec(v___x_1293_);
                            v___x_1349_ = crate::leanh::lean_box(0);
                            v_isShared_1350_ = v_isSharedCheck_1354_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            5 => {
                v_ref_1306_ = crate::leanh::lean_ctor_get(v_a_1203_, 5);
                v___x_1307_ = lean_io_error_to_string(v_a_1302_);
                if v_isShared_1290_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1289_, 3);
                    crate::leanh::lean_ctor_set(v___x_1289_, 0, v___x_1307_);
                    v___x_1309_ = v___x_1289_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1315_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1307_);
                    v___x_1309_ = v_reuseFailAlloc_1315_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1310_ = l_Lean_MessageData_ofFormat(v___x_1309_);
                crate::leanh::lean_inc(v_ref_1306_);
                v___x_1311_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1311_, 0, v_ref_1306_);
                crate::leanh::lean_ctor_set(v___x_1311_, 1, v___x_1310_);
                if v_isShared_1305_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1304_, 0, v___x_1311_);
                    v___x_1313_ = v___x_1304_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1314_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1311_);
                    v___x_1313_ = v_reuseFailAlloc_1314_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1313_;
            }
            8 => {
                v_ref_1321_ = crate::leanh::lean_ctor_get(v_a_1203_, 5);
                v___x_1322_ = lean_io_error_to_string(v_a_1317_);
                if v_isShared_1290_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1289_, 3);
                    crate::leanh::lean_ctor_set(v___x_1289_, 0, v___x_1322_);
                    v___x_1324_ = v___x_1289_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1330_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1322_);
                    v___x_1324_ = v_reuseFailAlloc_1330_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1325_ = l_Lean_MessageData_ofFormat(v___x_1324_);
                crate::leanh::lean_inc(v_ref_1321_);
                v___x_1326_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1326_, 0, v_ref_1321_);
                crate::leanh::lean_ctor_set(v___x_1326_, 1, v___x_1325_);
                if v_isShared_1320_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1319_, 0, v___x_1326_);
                    v___x_1328_ = v___x_1319_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1329_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1326_);
                    v___x_1328_ = v_reuseFailAlloc_1329_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1328_;
            }
            11 => {
                v_ref_1336_ = crate::leanh::lean_ctor_get(v_a_1203_, 5);
                v___x_1337_ = lean_io_error_to_string(v_a_1332_);
                if v_isShared_1290_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1289_, 3);
                    crate::leanh::lean_ctor_set(v___x_1289_, 0, v___x_1337_);
                    v___x_1339_ = v___x_1289_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1345_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1337_);
                    v___x_1339_ = v_reuseFailAlloc_1345_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_1340_ = l_Lean_MessageData_ofFormat(v___x_1339_);
                crate::leanh::lean_inc(v_ref_1336_);
                v___x_1341_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1341_, 0, v_ref_1336_);
                crate::leanh::lean_ctor_set(v___x_1341_, 1, v___x_1340_);
                if v_isShared_1335_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1334_, 0, v___x_1341_);
                    v___x_1343_ = v___x_1334_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1344_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
                    v___x_1343_ = v_reuseFailAlloc_1344_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1343_;
            }
            14 => {
                if v_isShared_1350_ == 0 {
                    v___x_1352_ = v___x_1349_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1353_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
                    v___x_1352_ = v_reuseFailAlloc_1353_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1352_;
            }
            16 => {
                if v_isShared_1360_ == 0 {
                    v___x_1362_ = v___x_1359_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1363_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
                    v___x_1362_ = v_reuseFailAlloc_1363_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1362_;
            }
            18 => {
                if v_isShared_1368_ == 0 {
                    v___x_1370_ = v___x_1367_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1371_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
                    v___x_1370_ = v_reuseFailAlloc_1371_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1370_;
            }
            20 => {
                if v_isShared_1376_ == 0 {
                    v___x_1378_ = v___x_1375_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1379_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
                    v___x_1378_ = v_reuseFailAlloc_1379_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1378_;
            }
            22 => {
                if v_isShared_1386_ == 0 {
                    v___x_1388_ = v___x_1385_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1389_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
                    v___x_1388_ = v_reuseFailAlloc_1389_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_1388_;
            }
            24 => {
                if v_isShared_1394_ == 0 {
                    v___x_1396_ = v___x_1393_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_1397_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
                    v___x_1396_ = v_reuseFailAlloc_1397_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_1396_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___boxed(
    mut v_x_1399_: *mut crate::leanh::LeanObject,
    mut v_a_1400_: *mut crate::leanh::LeanObject,
    mut v_a_1401_: *mut crate::leanh::LeanObject,
    mut v_a_1402_: *mut crate::leanh::LeanObject,
    mut v_a_1403_: *mut crate::leanh::LeanObject,
    mut v_a_1404_: *mut crate::leanh::LeanObject,
    mut v_a_1405_: *mut crate::leanh::LeanObject,
    mut v_a_1406_: *mut crate::leanh::LeanObject,
    mut v_a_1407_: *mut crate::leanh::LeanObject,
    mut v_a_1408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1409_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace(
        v_x_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_,
        v_a_1407_,
    );
    crate::leanh::lean_dec(v_a_1407_);
    crate::leanh::lean_dec_ref(v_a_1406_);
    crate::leanh::lean_dec(v_a_1405_);
    crate::leanh::lean_dec_ref(v_a_1404_);
    crate::leanh::lean_dec(v_a_1403_);
    crate::leanh::lean_dec_ref(v_a_1402_);
    crate::leanh::lean_dec(v_a_1401_);
    crate::leanh::lean_dec_ref(v_a_1400_);
    return v_res_1409_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1422_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1423_ = l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___closed__4;
    v___x_1424_ = l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___closed__4;
    v___x_1425_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1426_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1422_,
        v___x_1423_,
        v___x_1424_,
        v___x_1425_,
    );
    return v___x_1426_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1___boxed(
    mut v_a_1427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1428_ = l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1();
    return v_res_1428_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_BVDecide_BVTrace(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_BVDecide_BVCheck(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_BVDecide_BVTrace_0__Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace___regBuiltin_Lean_Elab_Tactic_BVDecide_BVTrace_evalBvTrace__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_BVDecide_BVTrace(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_BVDecide_BVTrace(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_BVDecide_BVCheck(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide_LRAT_Trim(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_BVDecide_BVTrace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_BVDecide_BVTrace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_BVDecide_BVTrace(builtin);
}

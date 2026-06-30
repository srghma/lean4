// Lean compiler output
// Module: Lean.Util.Reprove
// Imports: Lean.Elab.Command Init.Notation Lean.Exception
use crate::ffi::{
    lean_array_size, lean_array_uget_borrowed, lean_mk_empty_array_with_capacity, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Notation::{initialize_Init_Notation, runtime_initialize_Init_Notation};
use crate::r#gen::Init::Prelude::{l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs};
use crate::r#gen::Lean::AddDecl::l_Lean_addAndCompile___boxed;
use crate::r#gen::Lean::CoreM::l_Lean_Core_mkFreshUserName___boxed;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::{l_Lean_ConstantInfo_levelParams, l_Lean_ConstantInfo_type};
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_getRef___redArg,
    l_Lean_Elab_Command_liftCoreM___redArg, l_Lean_Elab_Command_liftTermElabM___redArg,
    runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::InfoTree::Main::l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_evalTactic___boxed, l_Lean_Elab_Tactic_run,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::l_Lean_Elab_Term_withDeclName___boxed;
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Environment::l_Lean_Environment_find_x3f;
use crate::r#gen::Lean::Exception::{initialize_Lean_Exception, runtime_initialize_Lean_Exception};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_hasMVar, l_Lean_Expr_mvarId_x21};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax,
    l_Lean_indentD, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_mkFreshExprMVar;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__1_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__1_value) as *mut leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_reproveDecl___closed__0_value: leanh::LeanStringObject<16> =
    leanh::LeanStringObject {
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
            114, 101, 112, 114, 111, 118, 101, 95, 101, 120, 97, 109, 112, 108, 101, 0,
        ],
    };
static mut l_Lean_Elab_Command_reproveDecl___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reproveDecl___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_reproveDecl___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_reproveDecl___closed__0_value)
                as *mut leanh::LeanObject,
            10945119183814660356 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_reproveDecl___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reproveDecl___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_reproveDecl___closed__2_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_Lean_Core_mkFreshUserName___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_reproveDecl___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_reproveDecl___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reproveDecl___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_reproveDecl___closed__3_value: leanh::LeanStringObject<22> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            117, 110, 107, 110, 111, 119, 110, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111,
            110, 32, 39, 0,
        ],
    };
static mut l_Lean_Elab_Command_reproveDecl___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reproveDecl___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_reproveDecl___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_reproveDecl___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_reproveDecl___closed__5_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [39, 0],
    };
static mut l_Lean_Elab_Command_reproveDecl___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reproveDecl___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_reproveDecl___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_reproveDecl___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_reprove___closed__0_value: leanh::LeanStringObject<5> =
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
static mut l_Lean_Elab_Command_reprove___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_reprove___closed__1_value: leanh::LeanStringObject<5> =
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
        m_data: [69, 108, 97, 98, 0],
    };
static mut l_Lean_Elab_Command_reprove___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_reprove___closed__2_value: leanh::LeanStringObject<8> =
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
        m_data: [67, 111, 109, 109, 97, 110, 100, 0],
    };
static mut l_Lean_Elab_Command_reprove___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_reprove___closed__3_value: leanh::LeanStringObject<8> =
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
        m_data: [114, 101, 112, 114, 111, 118, 101, 0],
    };
static mut l_Lean_Elab_Command_reprove___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_reprove___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_reprove___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__1_value)
                as *mut leanh::LeanObject,
            11510100434945111860 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_reprove___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__2_value)
                as *mut leanh::LeanObject,
            16981400742628996529 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_reprove___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__3_value)
                as *mut leanh::LeanObject,
            2205891246701399413 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_reprove___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_reprove___closed__5_value: leanh::LeanStringObject<8> =
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
        m_data: [97, 110, 100, 116, 104, 101, 110, 0],
    };
static mut l_Lean_Elab_Command_reprove___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_reprove___closed__6_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__5_value)
                as *mut leanh::LeanObject,
            12571085391447129896 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_reprove___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_reprove___closed__7_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [114, 101, 112, 114, 111, 118, 101, 32, 0],
    };
static mut l_Lean_Elab_Command_reprove___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_reprove___closed__8_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_reprove___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_reprove___closed__9_value: leanh::LeanStringObject<6> =
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
        m_data: [109, 97, 110, 121, 49, 0],
    };
static mut l_Lean_Elab_Command_reprove___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_reprove___closed__10_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__9_value)
                as *mut leanh::LeanObject,
            17243740965612849207 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_reprove___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_reprove___closed__11_value: leanh::LeanStringObject<6> =
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
        m_data: [105, 100, 101, 110, 116, 0],
    };
static mut l_Lean_Elab_Command_reprove___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_reprove___closed__12_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__11_value)
                as *mut leanh::LeanObject,
            5117844058249666356 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_reprove___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_reprove___closed__13_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__12_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_reprove___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_reprove___closed__14_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__10_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__13_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_reprove___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_reprove___closed__15_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_reprove___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_reprove___closed__16_value: leanh::LeanStringObject<5> =
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
        m_data: [32, 98, 121, 32, 0],
    };
static mut l_Lean_Elab_Command_reprove___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_reprove___closed__17_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__16_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_reprove___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_reprove___closed__18_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__17_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_reprove___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_reprove___closed__19_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
    };
static mut l_Lean_Elab_Command_reprove___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_reprove___closed__20_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__19_value)
                as *mut leanh::LeanObject,
            11103865283154438669 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_reprove___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_reprove___closed__21_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__20_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_reprove___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_reprove___closed__22_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 2,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__18_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__21_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_reprove___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_reprove___closed__23_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__4_value)
                as *mut leanh::LeanObject,
            (((1022 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__22_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_reprove___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__23_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Command_reprove: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_reprove___closed__23_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0___redArg(
    mut v_e_475_: *mut leanh::LeanObject,
    mut v___y_476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_478_: u8 = 0;
    let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_492_: u8 = 0;
    let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_498_: u8 = 0;
    let mut v_unused_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_478_ = l_Lean_Expr_hasMVar(v_e_475_);
                if v___x_478_ == 0 {
                    v___x_479_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_479_, 0, v_e_475_);
                    return v___x_479_;
                } else {
                    v___x_480_ = lean_st_ref_get(v___y_476_);
                    v_mctx_481_ = leanh::lean_ctor_get(v___x_480_, 0);
                    leanh::lean_inc_ref(v_mctx_481_);
                    leanh::lean_dec(v___x_480_);
                    v___x_482_ = l_Lean_instantiateMVarsCore(v_mctx_481_, v_e_475_);
                    v_fst_483_ = leanh::lean_ctor_get(v___x_482_, 0);
                    leanh::lean_inc(v_fst_483_);
                    v_snd_484_ = leanh::lean_ctor_get(v___x_482_, 1);
                    leanh::lean_inc(v_snd_484_);
                    leanh::lean_dec_ref(v___x_482_);
                    v___x_485_ = lean_st_ref_take(v___y_476_);
                    v_cache_486_ = leanh::lean_ctor_get(v___x_485_, 1);
                    v_zetaDeltaFVarIds_487_ = leanh::lean_ctor_get(v___x_485_, 2);
                    v_postponed_488_ = leanh::lean_ctor_get(v___x_485_, 3);
                    v_diag_489_ = leanh::lean_ctor_get(v___x_485_, 4);
                    v_isSharedCheck_498_ = (!leanh::lean_is_exclusive(v___x_485_)) as u8;
                    if v_isSharedCheck_498_ == 0 {
                        v_unused_499_ = leanh::lean_ctor_get(v___x_485_, 0);
                        leanh::lean_dec(v_unused_499_);
                        v___x_491_ = v___x_485_;
                        v_isShared_492_ = v_isSharedCheck_498_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_489_);
                        leanh::lean_inc(v_postponed_488_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_487_);
                        leanh::lean_inc(v_cache_486_);
                        leanh::lean_dec(v___x_485_);
                        v___x_491_ = leanh::lean_box(0);
                        v_isShared_492_ = v_isSharedCheck_498_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_492_ == 0 {
                    leanh::lean_ctor_set(v___x_491_, 0, v_snd_484_);
                    v___x_494_ = v___x_491_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_497_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_497_, 0, v_snd_484_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_497_, 1, v_cache_486_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_497_, 2, v_zetaDeltaFVarIds_487_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_497_, 3, v_postponed_488_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_497_, 4, v_diag_489_);
                    v___x_494_ = v_reuseFailAlloc_497_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_495_ = lean_st_ref_set(v___y_476_, v___x_494_);
                v___x_496_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_496_, 0, v_fst_483_);
                return v___x_496_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0___redArg___boxed(
    mut v_e_500_: *mut leanh::LeanObject,
    mut v___y_501_: *mut leanh::LeanObject,
    mut v___y_502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_503_ = l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0___redArg(
        v_e_500_, v___y_501_,
    );
    leanh::lean_dec(v___y_501_);
    return v_res_503_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0(
    mut v_e_504_: *mut leanh::LeanObject,
    mut v___y_505_: *mut leanh::LeanObject,
    mut v___y_506_: *mut leanh::LeanObject,
    mut v___y_507_: *mut leanh::LeanObject,
    mut v___y_508_: *mut leanh::LeanObject,
    mut v___y_509_: *mut leanh::LeanObject,
    mut v___y_510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_512_ = l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0___redArg(
        v_e_504_, v___y_508_,
    );
    return v___x_512_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0___boxed(
    mut v_e_513_: *mut leanh::LeanObject,
    mut v___y_514_: *mut leanh::LeanObject,
    mut v___y_515_: *mut leanh::LeanObject,
    mut v___y_516_: *mut leanh::LeanObject,
    mut v___y_517_: *mut leanh::LeanObject,
    mut v___y_518_: *mut leanh::LeanObject,
    mut v___y_519_: *mut leanh::LeanObject,
    mut v___y_520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_521_ = l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0(
        v_e_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_,
    );
    leanh::lean_dec(v___y_519_);
    leanh::lean_dec_ref(v___y_518_);
    leanh::lean_dec(v___y_517_);
    leanh::lean_dec_ref(v___y_516_);
    leanh::lean_dec(v___y_515_);
    leanh::lean_dec_ref(v___y_514_);
    return v_res_521_;
}
pub unsafe fn l_Lean_Elab_Command_reproveDecl___lam__0(
    mut v___x_522_: *mut leanh::LeanObject,
    mut v___x_523_: u8,
    mut v___x_524_: *mut leanh::LeanObject,
    mut v_tacticSeq_525_: *mut leanh::LeanObject,
    mut v___y_526_: *mut leanh::LeanObject,
    mut v___y_527_: *mut leanh::LeanObject,
    mut v___y_528_: *mut leanh::LeanObject,
    mut v___y_529_: *mut leanh::LeanObject,
    mut v___y_530_: *mut leanh::LeanObject,
    mut v___y_531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_542_: u8 = 0;
    let mut v___x_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_546_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_533_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_522_, v___x_523_, v___x_524_, v___y_528_, v___y_529_, v___y_530_,
                    v___y_531_,
                );
                if leanh::lean_obj_tag(v___x_533_) == 0 {
                    v_a_534_ = leanh::lean_ctor_get(v___x_533_, 0);
                    leanh::lean_inc(v_a_534_);
                    leanh::lean_dec_ref_known(v___x_533_, 1);
                    v___x_535_ = l_Lean_Expr_mvarId_x21(v_a_534_);
                    v___x_536_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalTactic___boxed as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    leanh::lean_closure_set(v___x_536_, 0, v_tacticSeq_525_);
                    v___x_537_ = l_Lean_Elab_Tactic_run(
                        v___x_535_, v___x_536_, v___y_526_, v___y_527_, v___y_528_, v___y_529_,
                        v___y_530_, v___y_531_,
                    );
                    if leanh::lean_obj_tag(v___x_537_) == 0 {
                        leanh::lean_dec_ref_known(v___x_537_, 1);
                        v___x_538_ = l_Lean_instantiateMVars___at___00Lean_Elab_Command_reproveDecl_spec__0___redArg(v_a_534_, v___y_529_);
                        return v___x_538_;
                    } else {
                        leanh::lean_dec(v_a_534_);
                        v_a_539_ = leanh::lean_ctor_get(v___x_537_, 0);
                        v_isSharedCheck_546_ = (!leanh::lean_is_exclusive(v___x_537_)) as u8;
                        if v_isSharedCheck_546_ == 0 {
                            v___x_541_ = v___x_537_;
                            v_isShared_542_ = v_isSharedCheck_546_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_539_);
                            leanh::lean_dec(v___x_537_);
                            v___x_541_ = leanh::lean_box(0);
                            v_isShared_542_ = v_isSharedCheck_546_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_tacticSeq_525_);
                    return v___x_533_;
                }
            }
            1 => {
                if v_isShared_542_ == 0 {
                    v___x_544_ = v___x_541_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_545_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
                    v___x_544_ = v_reuseFailAlloc_545_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_544_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_reproveDecl___lam__0___boxed(
    mut v___x_547_: *mut leanh::LeanObject,
    mut v___x_548_: *mut leanh::LeanObject,
    mut v___x_549_: *mut leanh::LeanObject,
    mut v_tacticSeq_550_: *mut leanh::LeanObject,
    mut v___y_551_: *mut leanh::LeanObject,
    mut v___y_552_: *mut leanh::LeanObject,
    mut v___y_553_: *mut leanh::LeanObject,
    mut v___y_554_: *mut leanh::LeanObject,
    mut v___y_555_: *mut leanh::LeanObject,
    mut v___y_556_: *mut leanh::LeanObject,
    mut v___y_557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2579__boxed_558_: u8 = 0;
    let mut v_res_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2579__boxed_558_ = (leanh::lean_unbox(v___x_548_) as u8);
    v_res_559_ = l_Lean_Elab_Command_reproveDecl___lam__0(
        v___x_547_,
        v___x_2579__boxed_558_,
        v___x_549_,
        v_tacticSeq_550_,
        v___y_551_,
        v___y_552_,
        v___y_553_,
        v___y_554_,
        v___y_555_,
        v___y_556_,
    );
    leanh::lean_dec(v___y_556_);
    leanh::lean_dec_ref(v___y_555_);
    leanh::lean_dec(v___y_554_);
    leanh::lean_dec_ref(v___y_553_);
    leanh::lean_dec(v___y_552_);
    leanh::lean_dec_ref(v___y_551_);
    return v_res_559_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_560_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_560_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_561_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__0);
    v___x_562_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_562_, 0, v___x_561_);
    return v___x_562_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_563_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__1);
    v___x_564_ = leanh::lean_unsigned_to_nat(0);
    v___x_565_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_565_, 0, v___x_564_);
    leanh::lean_ctor_set(v___x_565_, 1, v___x_564_);
    leanh::lean_ctor_set(v___x_565_, 2, v___x_564_);
    leanh::lean_ctor_set(v___x_565_, 3, v___x_564_);
    leanh::lean_ctor_set(v___x_565_, 4, v___x_563_);
    leanh::lean_ctor_set(v___x_565_, 5, v___x_563_);
    leanh::lean_ctor_set(v___x_565_, 6, v___x_563_);
    leanh::lean_ctor_set(v___x_565_, 7, v___x_563_);
    leanh::lean_ctor_set(v___x_565_, 8, v___x_563_);
    leanh::lean_ctor_set(v___x_565_, 9, v___x_563_);
    return v___x_565_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_566_ = leanh::lean_unsigned_to_nat(32);
    v___x_567_ = lean_mk_empty_array_with_capacity(v___x_566_);
    v___x_568_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_568_, 0, v___x_567_);
    return v___x_568_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_569_: usize = 0;
    let mut v___x_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_569_ = 5usize;
    v___x_570_ = leanh::lean_unsigned_to_nat(0);
    v___x_571_ = leanh::lean_unsigned_to_nat(32);
    v___x_572_ = lean_mk_empty_array_with_capacity(v___x_571_);
    v___x_573_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__3);
    v___x_574_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_574_, 0, v___x_573_);
    leanh::lean_ctor_set(v___x_574_, 1, v___x_572_);
    leanh::lean_ctor_set(v___x_574_, 2, v___x_570_);
    leanh::lean_ctor_set(v___x_574_, 3, v___x_570_);
    leanh::lean_ctor_set_usize(v___x_574_, 4, v___x_569_);
    return v___x_574_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_575_ = leanh::lean_box(1);
    v___x_576_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__4);
    v___x_577_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__1);
    v___x_578_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_578_, 0, v___x_577_);
    leanh::lean_ctor_set(v___x_578_, 1, v___x_576_);
    leanh::lean_ctor_set(v___x_578_, 2, v___x_575_);
    return v___x_578_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg(
    mut v_msgData_579_: *mut leanh::LeanObject,
    mut v___y_580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_582_ = lean_st_ref_get(v___y_580_);
    v_env_583_ = leanh::lean_ctor_get(v___x_582_, 0);
    leanh::lean_inc_ref(v_env_583_);
    leanh::lean_dec(v___x_582_);
    v___x_584_ = lean_st_ref_get(v___y_580_);
    v_scopes_585_ = leanh::lean_ctor_get(v___x_584_, 2);
    leanh::lean_inc(v_scopes_585_);
    leanh::lean_dec(v___x_584_);
    v___x_586_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_587_ = l_List_head_x21___redArg(v___x_586_, v_scopes_585_);
    leanh::lean_dec(v_scopes_585_);
    v_opts_588_ = leanh::lean_ctor_get(v___x_587_, 1);
    leanh::lean_inc_ref(v_opts_588_);
    leanh::lean_dec(v___x_587_);
    v___x_589_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__2);
    v___x_590_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___closed__5);
    v___x_591_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_591_, 0, v_env_583_);
    leanh::lean_ctor_set(v___x_591_, 1, v___x_589_);
    leanh::lean_ctor_set(v___x_591_, 2, v___x_590_);
    leanh::lean_ctor_set(v___x_591_, 3, v_opts_588_);
    v___x_592_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_592_, 0, v___x_591_);
    leanh::lean_ctor_set(v___x_592_, 1, v_msgData_579_);
    v___x_593_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_593_, 0, v___x_592_);
    return v___x_593_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg___boxed(
    mut v_msgData_594_: *mut leanh::LeanObject,
    mut v___y_595_: *mut leanh::LeanObject,
    mut v___y_596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_597_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg(v_msgData_594_, v___y_595_);
    leanh::lean_dec(v___y_595_);
    return v_res_597_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_598_ = leanh::lean_box(1);
    v___x_599_ = l_Lean_MessageData_ofFormat(v___x_598_);
    return v___x_599_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_603_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__2;
    v___x_604_ = l_Lean_MessageData_ofFormat(v___x_603_);
    return v___x_604_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4(
    mut v_x_605_: *mut leanh::LeanObject,
    mut v_x_606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_611_: u8 = 0;
    let mut v_before_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_615_: u8 = 0;
    let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_628_: u8 = 0;
    let mut v_unused_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_630_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_606_) == 0 {
                    return v_x_605_;
                } else {
                    v_head_607_ = leanh::lean_ctor_get(v_x_606_, 0);
                    v_tail_608_ = leanh::lean_ctor_get(v_x_606_, 1);
                    v_isSharedCheck_630_ = (!leanh::lean_is_exclusive(v_x_606_)) as u8;
                    if v_isSharedCheck_630_ == 0 {
                        v___x_610_ = v_x_606_;
                        v_isShared_611_ = v_isSharedCheck_630_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_608_);
                        leanh::lean_inc(v_head_607_);
                        leanh::lean_dec(v_x_606_);
                        v___x_610_ = leanh::lean_box(0);
                        v_isShared_611_ = v_isSharedCheck_630_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_612_ = leanh::lean_ctor_get(v_head_607_, 0);
                v_isSharedCheck_628_ = (!leanh::lean_is_exclusive(v_head_607_)) as u8;
                if v_isSharedCheck_628_ == 0 {
                    v_unused_629_ = leanh::lean_ctor_get(v_head_607_, 1);
                    leanh::lean_dec(v_unused_629_);
                    v___x_614_ = v_head_607_;
                    v_isShared_615_ = v_isSharedCheck_628_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_before_612_);
                    leanh::lean_dec(v_head_607_);
                    v___x_614_ = leanh::lean_box(0);
                    v_isShared_615_ = v_isSharedCheck_628_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_616_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__0);
                if v_isShared_615_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_614_, 7);
                    leanh::lean_ctor_set(v___x_614_, 1, v___x_616_);
                    leanh::lean_ctor_set(v___x_614_, 0, v_x_605_);
                    v___x_618_ = v___x_614_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_627_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_627_, 0, v_x_605_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_627_, 1, v___x_616_);
                    v___x_618_ = v_reuseFailAlloc_627_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_619_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__3);
                if v_isShared_611_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_610_, 7);
                    leanh::lean_ctor_set(v___x_610_, 1, v___x_619_);
                    leanh::lean_ctor_set(v___x_610_, 0, v___x_618_);
                    v___x_621_ = v___x_610_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_626_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_618_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_626_, 1, v___x_619_);
                    v___x_621_ = v_reuseFailAlloc_626_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_622_ = l_Lean_MessageData_ofSyntax(v_before_612_);
                v___x_623_ = l_Lean_indentD(v___x_622_);
                v___x_624_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_624_, 0, v___x_621_);
                leanh::lean_ctor_set(v___x_624_, 1, v___x_623_);
                v_x_605_ = v___x_624_;
                v_x_606_ = v_tail_608_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__3(
    mut v_opts_631_: *mut leanh::LeanObject,
    mut v_opt_632_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_633_ = leanh::lean_ctor_get(v_opt_632_, 0);
    v_defValue_634_ = leanh::lean_ctor_get(v_opt_632_, 1);
    v_map_635_ = leanh::lean_ctor_get(v_opts_631_, 0);
    v___x_636_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_635_,
            v_name_633_,
        );
    if leanh::lean_obj_tag(v___x_636_) == 0 {
        let mut v___x_637_: u8 = 0;
        v___x_637_ = (leanh::lean_unbox(v_defValue_634_) as u8);
        return v___x_637_;
    } else {
        let mut v_val_638_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_638_ = leanh::lean_ctor_get(v___x_636_, 0);
        leanh::lean_inc(v_val_638_);
        leanh::lean_dec_ref_known(v___x_636_, 1);
        if leanh::lean_obj_tag(v_val_638_) == 1 {
            let mut v_v_639_: u8 = 0;
            v_v_639_ = leanh::lean_ctor_get_uint8(v_val_638_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_638_, 0);
            return v_v_639_;
        } else {
            let mut v___x_640_: u8 = 0;
            leanh::lean_dec(v_val_638_);
            v___x_640_ = (leanh::lean_unbox(v_defValue_634_) as u8);
            return v___x_640_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__3___boxed(
    mut v_opts_641_: *mut leanh::LeanObject,
    mut v_opt_642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_643_: u8 = 0;
    let mut v_r_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_643_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__3(v_opts_641_, v_opt_642_);
    leanh::lean_dec_ref(v_opt_642_);
    leanh::lean_dec_ref(v_opts_641_);
    v_r_644_ = leanh::lean_box((v_res_643_) as usize);
    return v_r_644_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_648_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__1;
    v___x_649_ = l_Lean_MessageData_ofFormat(v___x_648_);
    return v___x_649_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg(
    mut v_msgData_650_: *mut leanh::LeanObject,
    mut v_macroStack_651_: *mut leanh::LeanObject,
    mut v___y_652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: u8 = 0;
    let mut v___x_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_667_: u8 = 0;
    let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_679_: u8 = 0;
    let mut v_unused_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_654_ = lean_st_ref_get(v___y_652_);
                v_scopes_655_ = leanh::lean_ctor_get(v___x_654_, 2);
                leanh::lean_inc(v_scopes_655_);
                leanh::lean_dec(v___x_654_);
                v___x_656_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_657_ = l_List_head_x21___redArg(v___x_656_, v_scopes_655_);
                leanh::lean_dec(v_scopes_655_);
                v_opts_658_ = leanh::lean_ctor_get(v___x_657_, 1);
                leanh::lean_inc_ref(v_opts_658_);
                leanh::lean_dec(v___x_657_);
                v___x_659_ = l_Lean_Elab_pp_macroStack;
                v___x_660_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__3(v_opts_658_, v___x_659_);
                leanh::lean_dec_ref(v_opts_658_);
                if v___x_660_ == 0 {
                    leanh::lean_dec(v_macroStack_651_);
                    v___x_661_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_661_, 0, v_msgData_650_);
                    return v___x_661_;
                } else {
                    if leanh::lean_obj_tag(v_macroStack_651_) == 0 {
                        v___x_662_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_662_, 0, v_msgData_650_);
                        return v___x_662_;
                    } else {
                        v_head_663_ = leanh::lean_ctor_get(v_macroStack_651_, 0);
                        leanh::lean_inc(v_head_663_);
                        v_after_664_ = leanh::lean_ctor_get(v_head_663_, 1);
                        v_isSharedCheck_679_ =
                            (!leanh::lean_is_exclusive(v_head_663_)) as u8;
                        if v_isSharedCheck_679_ == 0 {
                            v_unused_680_ = leanh::lean_ctor_get(v_head_663_, 0);
                            leanh::lean_dec(v_unused_680_);
                            v___x_666_ = v_head_663_;
                            v_isShared_667_ = v_isSharedCheck_679_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_after_664_);
                            leanh::lean_dec(v_head_663_);
                            v___x_666_ = leanh::lean_box(0);
                            v_isShared_667_ = v_isSharedCheck_679_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_668_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4___closed__0);
                if v_isShared_667_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_666_, 7);
                    leanh::lean_ctor_set(v___x_666_, 1, v___x_668_);
                    leanh::lean_ctor_set(v___x_666_, 0, v_msgData_650_);
                    v___x_670_ = v___x_666_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_678_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_678_, 0, v_msgData_650_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_678_, 1, v___x_668_);
                    v___x_670_ = v_reuseFailAlloc_678_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_671_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___closed__2);
                v___x_672_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_672_, 0, v___x_670_);
                leanh::lean_ctor_set(v___x_672_, 1, v___x_671_);
                v___x_673_ = l_Lean_MessageData_ofSyntax(v_after_664_);
                v___x_674_ = l_Lean_indentD(v___x_673_);
                v_msgData_675_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v_msgData_675_, 0, v___x_672_);
                leanh::lean_ctor_set(v_msgData_675_, 1, v___x_674_);
                v___x_676_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2_spec__4(v_msgData_675_, v_macroStack_651_);
                v___x_677_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_677_, 0, v___x_676_);
                return v___x_677_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg___boxed(
    mut v_msgData_681_: *mut leanh::LeanObject,
    mut v_macroStack_682_: *mut leanh::LeanObject,
    mut v___y_683_: *mut leanh::LeanObject,
    mut v___y_684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_685_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg(v_msgData_681_, v_macroStack_682_, v___y_683_);
    leanh::lean_dec(v___y_683_);
    return v_res_685_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1___redArg(
    mut v_msg_686_: *mut leanh::LeanObject,
    mut v___y_687_: *mut leanh::LeanObject,
    mut v___y_688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_700_: u8 = 0;
    let mut v___x_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_705_: u8 = 0;
    let mut v_a_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_709_: u8 = 0;
    let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_713_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_690_ = l_Lean_Elab_Command_getRef___redArg(v___y_687_);
                if leanh::lean_obj_tag(v___x_690_) == 0 {
                    v_a_691_ = leanh::lean_ctor_get(v___x_690_, 0);
                    leanh::lean_inc(v_a_691_);
                    leanh::lean_dec_ref_known(v___x_690_, 1);
                    v_macroStack_692_ = leanh::lean_ctor_get(v___y_687_, 4);
                    v___x_693_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg(v_msg_686_, v___y_688_);
                    v_a_694_ = leanh::lean_ctor_get(v___x_693_, 0);
                    leanh::lean_inc(v_a_694_);
                    leanh::lean_dec_ref(v___x_693_);
                    v___x_695_ = l_Lean_Elab_getBetterRef(v_a_691_, v_macroStack_692_);
                    leanh::lean_dec(v_a_691_);
                    leanh::lean_inc(v_macroStack_692_);
                    v___x_696_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg(v_a_694_, v_macroStack_692_, v___y_688_);
                    v_a_697_ = leanh::lean_ctor_get(v___x_696_, 0);
                    v_isSharedCheck_705_ = (!leanh::lean_is_exclusive(v___x_696_)) as u8;
                    if v_isSharedCheck_705_ == 0 {
                        v___x_699_ = v___x_696_;
                        v_isShared_700_ = v_isSharedCheck_705_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_697_);
                        leanh::lean_dec(v___x_696_);
                        v___x_699_ = leanh::lean_box(0);
                        v_isShared_700_ = v_isSharedCheck_705_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msg_686_);
                    v_a_706_ = leanh::lean_ctor_get(v___x_690_, 0);
                    v_isSharedCheck_713_ = (!leanh::lean_is_exclusive(v___x_690_)) as u8;
                    if v_isSharedCheck_713_ == 0 {
                        v___x_708_ = v___x_690_;
                        v_isShared_709_ = v_isSharedCheck_713_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_706_);
                        leanh::lean_dec(v___x_690_);
                        v___x_708_ = leanh::lean_box(0);
                        v_isShared_709_ = v_isSharedCheck_713_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_701_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_701_, 0, v___x_695_);
                leanh::lean_ctor_set(v___x_701_, 1, v_a_697_);
                if v_isShared_700_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_699_, 1);
                    leanh::lean_ctor_set(v___x_699_, 0, v___x_701_);
                    v___x_703_ = v___x_699_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_704_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
                    v___x_703_ = v_reuseFailAlloc_704_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_703_;
            }
            3 => {
                if v_isShared_709_ == 0 {
                    v___x_711_ = v___x_708_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_712_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
                    v___x_711_ = v_reuseFailAlloc_712_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_711_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1___redArg___boxed(
    mut v_msg_714_: *mut leanh::LeanObject,
    mut v___y_715_: *mut leanh::LeanObject,
    mut v___y_716_: *mut leanh::LeanObject,
    mut v___y_717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_718_ = l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1___redArg(
        v_msg_714_, v___y_715_, v___y_716_,
    );
    leanh::lean_dec(v___y_716_);
    leanh::lean_dec_ref(v___y_715_);
    return v_res_718_;
}
pub unsafe fn _init_l_Lean_Elab_Command_reproveDecl___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_725_ = l_Lean_Elab_Command_reproveDecl___closed__3;
    v___x_726_ = l_Lean_stringToMessageData(v___x_725_);
    return v___x_726_;
}
pub unsafe fn _init_l_Lean_Elab_Command_reproveDecl___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_728_ = l_Lean_Elab_Command_reproveDecl___closed__5;
    v___x_729_ = l_Lean_stringToMessageData(v___x_728_);
    return v___x_729_;
}
pub unsafe fn l_Lean_Elab_Command_reproveDecl(
    mut v_declName_730_: *mut leanh::LeanObject,
    mut v_tacticSeq_731_: *mut leanh::LeanObject,
    mut v_a_732_: *mut leanh::LeanObject,
    mut v_a_733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: u8 = 0;
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_742_: u8 = 0;
    let mut v___x_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: u8 = 0;
    let mut v___x_750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: u8 = 0;
    let mut v___x_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: u8 = 0;
    let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_772_: u8 = 0;
    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_776_: u8 = 0;
    let mut v_reuseFailAlloc_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_781_: u8 = 0;
    let mut v___x_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_785_: u8 = 0;
    let mut v_isSharedCheck_786_: u8 = 0;
    let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_735_ = lean_st_ref_get(v_a_733_);
                v_env_736_ = leanh::lean_ctor_get(v___x_735_, 0);
                leanh::lean_inc_ref(v_env_736_);
                leanh::lean_dec(v___x_735_);
                v___x_737_ = 0;
                leanh::lean_inc(v_declName_730_);
                v___x_738_ = l_Lean_Environment_find_x3f(v_env_736_, v_declName_730_, v___x_737_);
                if leanh::lean_obj_tag(v___x_738_) == 1 {
                    leanh::lean_dec(v_declName_730_);
                    v_val_739_ = leanh::lean_ctor_get(v___x_738_, 0);
                    v_isSharedCheck_786_ = (!leanh::lean_is_exclusive(v___x_738_)) as u8;
                    if v_isSharedCheck_786_ == 0 {
                        v___x_741_ = v___x_738_;
                        v_isShared_742_ = v_isSharedCheck_786_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_739_);
                        leanh::lean_dec(v___x_738_);
                        v___x_741_ = leanh::lean_box(0);
                        v_isShared_742_ = v_isSharedCheck_786_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_738_);
                    leanh::lean_dec(v_tacticSeq_731_);
                    v___x_787_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Command_reproveDecl___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Elab_Command_reproveDecl___closed__4_once),
                        _init_l_Lean_Elab_Command_reproveDecl___closed__4,
                    );
                    v___x_788_ = l_Lean_MessageData_ofName(v_declName_730_);
                    v___x_789_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_789_, 0, v___x_787_);
                    leanh::lean_ctor_set(v___x_789_, 1, v___x_788_);
                    v___x_790_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Command_reproveDecl___closed__6),
                        core::ptr::addr_of_mut!(l_Lean_Elab_Command_reproveDecl___closed__6_once),
                        _init_l_Lean_Elab_Command_reproveDecl___closed__6,
                    );
                    v___x_791_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_791_, 0, v___x_789_);
                    leanh::lean_ctor_set(v___x_791_, 1, v___x_790_);
                    v___x_792_ =
                        l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1___redArg(
                            v___x_791_, v_a_732_, v_a_733_,
                        );
                    return v___x_792_;
                }
            }
            1 => {
                v___x_743_ = l_Lean_Elab_Command_reproveDecl___closed__2;
                v___x_744_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_743_, v_a_732_, v_a_733_);
                if leanh::lean_obj_tag(v___x_744_) == 0 {
                    v_a_745_ = leanh::lean_ctor_get(v___x_744_, 0);
                    leanh::lean_inc(v_a_745_);
                    leanh::lean_dec_ref_known(v___x_744_, 1);
                    v___x_746_ = l_Lean_ConstantInfo_type(v_val_739_);
                    leanh::lean_inc_ref(v___x_746_);
                    if v_isShared_742_ == 0 {
                        leanh::lean_ctor_set(v___x_741_, 0, v___x_746_);
                        v___x_748_ = v___x_741_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_777_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_746_);
                        v___x_748_ = v_reuseFailAlloc_777_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_741_);
                    leanh::lean_dec(v_val_739_);
                    leanh::lean_dec(v_tacticSeq_731_);
                    v_a_778_ = leanh::lean_ctor_get(v___x_744_, 0);
                    v_isSharedCheck_785_ = (!leanh::lean_is_exclusive(v___x_744_)) as u8;
                    if v_isSharedCheck_785_ == 0 {
                        v___x_780_ = v___x_744_;
                        v_isShared_781_ = v_isSharedCheck_785_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_778_);
                        leanh::lean_dec(v___x_744_);
                        v___x_780_ = leanh::lean_box(0);
                        v_isShared_781_ = v_isSharedCheck_785_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_749_ = 0;
                v___x_750_ = leanh::lean_box(0);
                v___x_751_ = leanh::lean_box((v___x_749_) as usize);
                v___f_752_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Command_reproveDecl___lam__0___boxed as *mut core::ffi::c_void,
                    11,
                    4,
                );
                leanh::lean_closure_set(v___f_752_, 0, v___x_748_);
                leanh::lean_closure_set(v___f_752_, 1, v___x_751_);
                leanh::lean_closure_set(v___f_752_, 2, v___x_750_);
                leanh::lean_closure_set(v___f_752_, 3, v_tacticSeq_731_);
                leanh::lean_inc(v_a_745_);
                v___x_753_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Term_withDeclName___boxed as *mut core::ffi::c_void,
                    10,
                    3,
                );
                leanh::lean_closure_set(v___x_753_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_753_, 1, v_a_745_);
                leanh::lean_closure_set(v___x_753_, 2, v___f_752_);
                v___x_754_ =
                    l_Lean_Elab_Command_liftTermElabM___redArg(v___x_753_, v_a_732_, v_a_733_);
                if leanh::lean_obj_tag(v___x_754_) == 0 {
                    v_a_755_ = leanh::lean_ctor_get(v___x_754_, 0);
                    leanh::lean_inc(v_a_755_);
                    leanh::lean_dec_ref_known(v___x_754_, 1);
                    v___x_756_ = l_Lean_ConstantInfo_levelParams(v_val_739_);
                    leanh::lean_dec(v_val_739_);
                    leanh::lean_inc(v_a_745_);
                    v___x_757_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_757_, 0, v_a_745_);
                    leanh::lean_ctor_set(v___x_757_, 1, v___x_756_);
                    leanh::lean_ctor_set(v___x_757_, 2, v___x_746_);
                    v___x_758_ = leanh::lean_box(0);
                    v___x_759_ = 1;
                    v___x_760_ = leanh::lean_box(0);
                    v___x_761_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_761_, 0, v_a_745_);
                    leanh::lean_ctor_set(v___x_761_, 1, v___x_760_);
                    v___x_762_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                    leanh::lean_ctor_set(v___x_762_, 0, v___x_757_);
                    leanh::lean_ctor_set(v___x_762_, 1, v_a_755_);
                    leanh::lean_ctor_set(v___x_762_, 2, v___x_758_);
                    leanh::lean_ctor_set(v___x_762_, 3, v___x_761_);
                    leanh::lean_ctor_set_uint8(
                        v___x_762_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                        v___x_759_,
                    );
                    v___x_763_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_763_, 0, v___x_762_);
                    v___x_764_ = 1;
                    v___x_765_ = leanh::lean_box((v___x_764_) as usize);
                    v___x_766_ = leanh::lean_box((v___x_737_) as usize);
                    v___x_767_ = leanh::lean_alloc_closure(
                        l_Lean_addAndCompile___boxed as *mut core::ffi::c_void,
                        6,
                        3,
                    );
                    leanh::lean_closure_set(v___x_767_, 0, v___x_763_);
                    leanh::lean_closure_set(v___x_767_, 1, v___x_765_);
                    leanh::lean_closure_set(v___x_767_, 2, v___x_766_);
                    v___x_768_ =
                        l_Lean_Elab_Command_liftCoreM___redArg(v___x_767_, v_a_732_, v_a_733_);
                    return v___x_768_;
                } else {
                    leanh::lean_dec_ref(v___x_746_);
                    leanh::lean_dec(v_a_745_);
                    leanh::lean_dec(v_val_739_);
                    v_a_769_ = leanh::lean_ctor_get(v___x_754_, 0);
                    v_isSharedCheck_776_ = (!leanh::lean_is_exclusive(v___x_754_)) as u8;
                    if v_isSharedCheck_776_ == 0 {
                        v___x_771_ = v___x_754_;
                        v_isShared_772_ = v_isSharedCheck_776_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_769_);
                        leanh::lean_dec(v___x_754_);
                        v___x_771_ = leanh::lean_box(0);
                        v_isShared_772_ = v_isSharedCheck_776_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_772_ == 0 {
                    v___x_774_ = v___x_771_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_775_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
                    v___x_774_ = v_reuseFailAlloc_775_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_774_;
            }
            5 => {
                if v_isShared_781_ == 0 {
                    v___x_783_ = v___x_780_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_784_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
                    v___x_783_ = v_reuseFailAlloc_784_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_783_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_reproveDecl___boxed(
    mut v_declName_793_: *mut leanh::LeanObject,
    mut v_tacticSeq_794_: *mut leanh::LeanObject,
    mut v_a_795_: *mut leanh::LeanObject,
    mut v_a_796_: *mut leanh::LeanObject,
    mut v_a_797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_798_ =
        l_Lean_Elab_Command_reproveDecl(v_declName_793_, v_tacticSeq_794_, v_a_795_, v_a_796_);
    leanh::lean_dec(v_a_796_);
    leanh::lean_dec_ref(v_a_795_);
    return v_res_798_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1(
    mut v_msgData_799_: *mut leanh::LeanObject,
    mut v___y_800_: *mut leanh::LeanObject,
    mut v___y_801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_803_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___redArg(v_msgData_799_, v___y_801_);
    return v___x_803_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1___boxed(
    mut v_msgData_804_: *mut leanh::LeanObject,
    mut v___y_805_: *mut leanh::LeanObject,
    mut v___y_806_: *mut leanh::LeanObject,
    mut v___y_807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_808_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__1(v_msgData_804_, v___y_805_, v___y_806_);
    leanh::lean_dec(v___y_806_);
    leanh::lean_dec_ref(v___y_805_);
    return v_res_808_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1(
    mut v_00_u03b1_809_: *mut leanh::LeanObject,
    mut v_msg_810_: *mut leanh::LeanObject,
    mut v___y_811_: *mut leanh::LeanObject,
    mut v___y_812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_814_ = l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1___redArg(
        v_msg_810_, v___y_811_, v___y_812_,
    );
    return v___x_814_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1___boxed(
    mut v_00_u03b1_815_: *mut leanh::LeanObject,
    mut v_msg_816_: *mut leanh::LeanObject,
    mut v___y_817_: *mut leanh::LeanObject,
    mut v___y_818_: *mut leanh::LeanObject,
    mut v___y_819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_820_ = l_Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1(
        v_00_u03b1_815_,
        v_msg_816_,
        v___y_817_,
        v___y_818_,
    );
    leanh::lean_dec(v___y_818_);
    leanh::lean_dec_ref(v___y_817_);
    return v_res_820_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2(
    mut v_msgData_821_: *mut leanh::LeanObject,
    mut v_macroStack_822_: *mut leanh::LeanObject,
    mut v___y_823_: *mut leanh::LeanObject,
    mut v___y_824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_826_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___redArg(v_msgData_821_, v_macroStack_822_, v___y_824_);
    return v___x_826_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2___boxed(
    mut v_msgData_827_: *mut leanh::LeanObject,
    mut v_macroStack_828_: *mut leanh::LeanObject,
    mut v___y_829_: *mut leanh::LeanObject,
    mut v___y_830_: *mut leanh::LeanObject,
    mut v___y_831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_832_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_reproveDecl_spec__1_spec__2(v_msgData_827_, v_macroStack_828_, v___y_829_, v___y_830_);
    leanh::lean_dec(v___y_830_);
    leanh::lean_dec_ref(v___y_829_);
    return v_res_832_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabReprove_spec__0(
    mut v_tacticSeq_884_: *mut leanh::LeanObject,
    mut v_as_885_: *mut leanh::LeanObject,
    mut v_sz_886_: usize,
    mut v_i_887_: usize,
    mut v_b_888_: *mut leanh::LeanObject,
    mut v___y_889_: *mut leanh::LeanObject,
    mut v___y_890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_892_: u8 = 0;
    let mut v___x_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: usize = 0;
    let mut v___x_902_: usize = 0;
    let mut v_a_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_907_: u8 = 0;
    let mut v___x_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_911_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_892_ = lean_usize_dec_lt(v_i_887_, v_sz_886_);
                if v___x_892_ == 0 {
                    leanh::lean_dec(v_tacticSeq_884_);
                    v___x_893_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_893_, 0, v_b_888_);
                    return v___x_893_;
                } else {
                    v_a_894_ = lean_array_uget_borrowed(v_as_885_, v_i_887_);
                    v___x_895_ = leanh::lean_box(0);
                    leanh::lean_inc(v_a_894_);
                    v___x_896_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed
                            as *mut core::ffi::c_void,
                        5,
                        2,
                    );
                    leanh::lean_closure_set(v___x_896_, 0, v_a_894_);
                    leanh::lean_closure_set(v___x_896_, 1, v___x_895_);
                    v___x_897_ =
                        l_Lean_Elab_Command_liftCoreM___redArg(v___x_896_, v___y_889_, v___y_890_);
                    if leanh::lean_obj_tag(v___x_897_) == 0 {
                        v_a_898_ = leanh::lean_ctor_get(v___x_897_, 0);
                        leanh::lean_inc(v_a_898_);
                        leanh::lean_dec_ref_known(v___x_897_, 1);
                        leanh::lean_inc(v_tacticSeq_884_);
                        v___x_899_ = l_Lean_Elab_Command_reproveDecl(
                            v_a_898_,
                            v_tacticSeq_884_,
                            v___y_889_,
                            v___y_890_,
                        );
                        if leanh::lean_obj_tag(v___x_899_) == 0 {
                            leanh::lean_dec_ref_known(v___x_899_, 1);
                            v___x_900_ = leanh::lean_box(0);
                            v___x_901_ = 1usize;
                            v___x_902_ = lean_usize_add(v_i_887_, v___x_901_);
                            v_i_887_ = v___x_902_;
                            v_b_888_ = v___x_900_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec(v_tacticSeq_884_);
                            return v___x_899_;
                        }
                    } else {
                        leanh::lean_dec(v_tacticSeq_884_);
                        v_a_904_ = leanh::lean_ctor_get(v___x_897_, 0);
                        v_isSharedCheck_911_ = (!leanh::lean_is_exclusive(v___x_897_)) as u8;
                        if v_isSharedCheck_911_ == 0 {
                            v___x_906_ = v___x_897_;
                            v_isShared_907_ = v_isSharedCheck_911_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_904_);
                            leanh::lean_dec(v___x_897_);
                            v___x_906_ = leanh::lean_box(0);
                            v_isShared_907_ = v_isSharedCheck_911_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_907_ == 0 {
                    v___x_909_ = v___x_906_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_910_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
                    v___x_909_ = v_reuseFailAlloc_910_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_909_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabReprove_spec__0___boxed(
    mut v_tacticSeq_912_: *mut leanh::LeanObject,
    mut v_as_913_: *mut leanh::LeanObject,
    mut v_sz_914_: *mut leanh::LeanObject,
    mut v_i_915_: *mut leanh::LeanObject,
    mut v_b_916_: *mut leanh::LeanObject,
    mut v___y_917_: *mut leanh::LeanObject,
    mut v___y_918_: *mut leanh::LeanObject,
    mut v___y_919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_920_: usize = 0;
    let mut v_i_boxed_921_: usize = 0;
    let mut v_res_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_920_ = leanh::lean_unbox_usize(v_sz_914_);
    leanh::lean_dec(v_sz_914_);
    v_i_boxed_921_ = leanh::lean_unbox_usize(v_i_915_);
    leanh::lean_dec(v_i_915_);
    v_res_922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabReprove_spec__0(v_tacticSeq_912_, v_as_913_, v_sz_boxed_920_, v_i_boxed_921_, v_b_916_, v___y_917_, v___y_918_);
    leanh::lean_dec(v___y_918_);
    leanh::lean_dec_ref(v___y_917_);
    leanh::lean_dec_ref(v_as_913_);
    return v_res_922_;
}
pub unsafe fn l_Lean_Elab_Command_elabReprove(
    mut v_stx_923_: *mut leanh::LeanObject,
    mut v_a_924_: *mut leanh::LeanObject,
    mut v_a_925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_identStxs_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tacticSeq_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_933_: usize = 0;
    let mut v___x_934_: usize = 0;
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_938_: u8 = 0;
    let mut v___x_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_942_: u8 = 0;
    let mut v_unused_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_927_ = leanh::lean_unsigned_to_nat(1);
                v___x_928_ = l_Lean_Syntax_getArg(v_stx_923_, v___x_927_);
                v_identStxs_929_ = l_Lean_Syntax_getArgs(v___x_928_);
                leanh::lean_dec(v___x_928_);
                v___x_930_ = leanh::lean_unsigned_to_nat(3);
                v_tacticSeq_931_ = l_Lean_Syntax_getArg(v_stx_923_, v___x_930_);
                v___x_932_ = leanh::lean_box(0);
                v_sz_933_ = lean_array_size(v_identStxs_929_);
                v___x_934_ = 0usize;
                v___x_935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabReprove_spec__0(v_tacticSeq_931_, v_identStxs_929_, v_sz_933_, v___x_934_, v___x_932_, v_a_924_, v_a_925_);
                leanh::lean_dec_ref(v_identStxs_929_);
                if leanh::lean_obj_tag(v___x_935_) == 0 {
                    v_isSharedCheck_942_ = (!leanh::lean_is_exclusive(v___x_935_)) as u8;
                    if v_isSharedCheck_942_ == 0 {
                        v_unused_943_ = leanh::lean_ctor_get(v___x_935_, 0);
                        leanh::lean_dec(v_unused_943_);
                        v___x_937_ = v___x_935_;
                        v_isShared_938_ = v_isSharedCheck_942_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_935_);
                        v___x_937_ = leanh::lean_box(0);
                        v_isShared_938_ = v_isSharedCheck_942_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_935_;
                }
            }
            1 => {
                if v_isShared_938_ == 0 {
                    leanh::lean_ctor_set(v___x_937_, 0, v___x_932_);
                    v___x_940_ = v___x_937_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_941_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_932_);
                    v___x_940_ = v_reuseFailAlloc_941_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_940_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_elabReprove___boxed(
    mut v_stx_944_: *mut leanh::LeanObject,
    mut v_a_945_: *mut leanh::LeanObject,
    mut v_a_946_: *mut leanh::LeanObject,
    mut v_a_947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_948_ = l_Lean_Elab_Command_elabReprove(v_stx_944_, v_a_945_, v_a_946_);
    leanh::lean_dec(v_a_946_);
    leanh::lean_dec_ref(v_a_945_);
    leanh::lean_dec(v_stx_944_);
    return v_res_948_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_Reprove(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Notation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Exception(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_Reprove(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_Reprove(builtin: u8) -> *mut leanh::LeanObject {
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
    res = initialize_Init_Notation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Exception(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Reprove(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_Reprove(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Util_Reprove(builtin);
}
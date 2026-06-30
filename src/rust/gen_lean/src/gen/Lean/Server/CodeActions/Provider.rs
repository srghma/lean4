// Lean compiler output
// Module: Lean.Server.CodeActions.Provider
// Imports: Std.Data.Iterators.Producers.Range Std.Data.Iterators.Combinators.StepSize Lean.Elab.BuiltinTerm Lean.Elab.BuiltinNotation Lean.Server.CodeActions.Attr
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_uget_borrowed, lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_mul, lean_nat_shiftr, lean_nat_sub, lean_panic_fn_borrowed,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_instInhabited};
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_getTailInfo;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_getKind, l_Lean_Syntax_getNumArgs,
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    l_instInhabitedForall___redArg___lam__0___boxed,
};
use crate::r#gen::Init::System::IO::l_instInhabitedEIO___aux__1___boxed;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::Lsp::Utf16::l_Lean_FileMap_lspPosToUtf8Pos;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Elab::BuiltinNotation::{
    initialize_Lean_Elab_BuiltinNotation, runtime_initialize_Lean_Elab_BuiltinNotation,
};
use crate::r#gen::Lean::Elab::BuiltinTerm::{
    initialize_Lean_Elab_BuiltinTerm, runtime_initialize_Lean_Elab_BuiltinTerm,
};
use crate::r#gen::Lean::Elab::InfoTree::Main::{
    l_Lean_Elab_Info_updateContext_x3f, l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f,
};
use crate::r#gen::Lean::Environment::l_Lean_PersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Server::CodeActions::Attr::{
    initialize_Lean_Server_CodeActions_Attr, l_Lean_CodeAction_cmdCodeActionExt,
    l_Lean_CodeAction_holeCodeActionExt, l_Lean_CodeAction_instInhabitedCommandCodeActions_default,
    runtime_initialize_Lean_Server_CodeActions_Attr,
};
use crate::r#gen::Lean::Server::CodeActions::Basic::l_Lean_Server_addBuiltinCodeActionProvider;
use crate::r#gen::Lean::Server::InfoUtils::{
    l_Lean_Elab_Info_stx, l_Lean_Elab_InfoTree_foldInfo___redArg,
    l_Lean_Elab_InfoTree_foldInfoTree___redArg,
};
use crate::r#gen::Lean::Server::Requests::l_Lean_Server_instInhabitedRequestError_default;
use crate::r#gen::Lean::Server::Snapshots::{
    l_Lean_Server_Snapshots_Snapshot_env, l_Lean_Server_Snapshots_Snapshot_infoTree,
};
use crate::r#gen::Lean::Syntax::{l_Lean_Syntax_getRange_x3f, l_Lean_Syntax_instBEqRange_beq};
use crate::r#gen::Std::Data::Iterators::Combinators::StepSize::{
    initialize_Std_Data_Iterators_Combinators_StepSize,
    runtime_initialize_Std_Data_Iterators_Combinators_StepSize,
};
use crate::r#gen::Std::Data::Iterators::Producers::Range::{
    initialize_Std_Data_Iterators_Producers_Range,
    runtime_initialize_Std_Data_Iterators_Producers_Range,
};
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value:
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
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__1_value:
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
    m_data: [69, 108, 97, 98, 0],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__2_value:
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
    m_data: [84, 101, 114, 109, 0],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__3_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [101, 108, 97, 98, 72, 111, 108, 101, 0],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__1_value)
            as *mut leanh::LeanObject,
        11510100434945111860 as *mut leanh::LeanObject,
    ],
};
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__2_value)
            as *mut leanh::LeanObject,
        7892421401833366012 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value:
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
        core::ptr::addr_of!(
            l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__3_value)
            as *mut leanh::LeanObject,
        11340967426965104390 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__5_value:
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
        101, 108, 97, 98, 83, 121, 110, 116, 104, 101, 116, 105, 99, 72, 111, 108, 101, 0,
    ],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__5_value)
        as *mut leanh::LeanObject;
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__1_value)
            as *mut leanh::LeanObject,
        11510100434945111860 as *mut leanh::LeanObject,
    ],
};
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__2_value)
            as *mut leanh::LeanObject,
        7892421401833366012 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value:
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
        core::ptr::addr_of!(
            l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__5_value)
            as *mut leanh::LeanObject,
        8403575154271798838 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__7_value:
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
    m_data: [101, 108, 97, 98, 83, 111, 114, 114, 121, 0],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__7_value)
        as *mut leanh::LeanObject;
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__1_value)
            as *mut leanh::LeanObject,
        11510100434945111860 as *mut leanh::LeanObject,
    ],
};
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__2_value)
            as *mut leanh::LeanObject,
        7892421401833366012 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value:
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
        core::ptr::addr_of!(
            l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__7_value)
            as *mut leanh::LeanObject,
        6267058134344042428 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__9_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__10_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__11_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__10_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___closed__0_value:
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
static mut l_Lean_CodeAction_holeCodeActionProvider___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_CodeAction_holeCodeActionProvider___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_CodeAction_holeCodeActionProvider___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_CodeAction_holeCodeActionProvider___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_CodeAction_holeCodeActionProvider___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_CodeAction_holeCodeActionProvider___closed__3_value:
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
static mut l_Lean_CodeAction_holeCodeActionProvider___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___closed__3_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__0_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__1_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [104, 111, 108, 101, 67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 80, 114, 111, 118, 105, 100, 101, 114, 0]};
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__0_value) as *mut leanh::LeanObject,1630946840184265901 as *mut leanh::LeanObject] };
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__1_value) as *mut leanh::LeanObject,2550652980631965832 as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__2_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__0_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__1_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__2_value) as *mut leanh::LeanObject,8504843326314613972 as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__4_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__5_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 66, 114, 97, 99, 107, 101, 116, 101, 100, 0]};
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__5_value) as *mut leanh::LeanObject;
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__0_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__1_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__5_value) as *mut leanh::LeanObject,10468396288943149198 as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__1_value) as *mut leanh::LeanObject;
static mut l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__0_value: leanh::LeanStringObject<33> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 115, 46, 80, 114, 111, 118, 105, 100, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__1_value: leanh::LeanStringObject<38> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [76, 101, 97, 110, 46, 67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 46, 99, 109, 100, 67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 80, 114, 111, 118, 105, 100, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__2_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_CodeAction_cmdCodeActionProvider___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_CodeAction_cmdCodeActionProvider___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_CodeAction_cmdCodeActionProvider___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_CodeAction_cmdCodeActionProvider___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_CodeAction_cmdCodeActionProvider___closed__2_value:
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
static mut l_Lean_CodeAction_cmdCodeActionProvider___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_cmdCodeActionProvider___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__0_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [99, 109, 100, 67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 80, 114, 111, 118, 105, 100, 101, 114, 0]};
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__0_value) as *mut leanh::LeanObject,1630946840184265901 as *mut leanh::LeanObject] };
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__0_value) as *mut leanh::LeanObject,890343562233056736 as *mut leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(
    mut v___y_1366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_doc_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_doc_1368_ = leanh::lean_ctor_get(v___y_1366_, 1);
    leanh::lean_inc_ref(v_doc_1368_);
    v___x_1369_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1369_, 0, v_doc_1368_);
    return v___x_1369_;
}
pub unsafe fn l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0___boxed(
    mut v___y_1370_: *mut leanh::LeanObject,
    mut v___y_1371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1372_ =
        l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(
            v___y_1370_,
        );
    leanh::lean_dec_ref(v___y_1370_);
    return v_res_1372_;
}
pub unsafe fn l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1(
    mut v_a_1373_: *mut leanh::LeanObject,
    mut v_x_1374_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1375_: u8 = 0;
    let mut v_head_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1374_) == 0 {
                    v___x_1375_ = 0;
                    return v___x_1375_;
                } else {
                    v_head_1376_ = leanh::lean_ctor_get(v_x_1374_, 0);
                    v_tail_1377_ = leanh::lean_ctor_get(v_x_1374_, 1);
                    v___x_1378_ = lean_name_eq(v_a_1373_, v_head_1376_);
                    if v___x_1378_ == 0 {
                        v_x_1374_ = v_tail_1377_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1378_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1___boxed(
    mut v_a_1380_: *mut leanh::LeanObject,
    mut v_x_1381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1382_: u8 = 0;
    let mut v_r_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1382_ =
        l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1(v_a_1380_, v_x_1381_);
    leanh::lean_dec(v_x_1381_);
    leanh::lean_dec(v_a_1380_);
    v_r_1383_ = leanh::lean_box((v_res_1382_) as usize);
    return v_r_1383_;
}
pub unsafe fn l_Lean_CodeAction_holeCodeActionProvider___lam__0(
    mut v___x_1414_: *mut leanh::LeanObject,
    mut v___x_1415_: *mut leanh::LeanObject,
    mut v_ctx_1416_: *mut leanh::LeanObject,
    mut v_info_1417_: *mut leanh::LeanObject,
    mut v_result_1418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1421_: u8 = 0;
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toElabInfo_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_elaborator_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: u8 = 0;
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: u8 = 0;
    let mut v___x_1434_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_info_1417_) == 1 {
                    v_i_1419_ = leanh::lean_ctor_get(v_info_1417_, 0);
                    v_toElabInfo_1424_ = leanh::lean_ctor_get(v_i_1419_, 0);
                    v_elaborator_1425_ = leanh::lean_ctor_get(v_toElabInfo_1424_, 0);
                    v_stx_1426_ = leanh::lean_ctor_get(v_toElabInfo_1424_, 1);
                    v___x_1427_ = l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__11;
                    v___x_1428_ =
                        l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1(
                            v_elaborator_1425_,
                            v___x_1427_,
                        );
                    if v___x_1428_ == 0 {
                        leanh::lean_dec_ref(v_ctx_1416_);
                        return v_result_1418_;
                    } else {
                        v___x_1429_ = l_Lean_Syntax_getPos_x3f(v_stx_1426_, v___x_1428_);
                        if leanh::lean_obj_tag(v___x_1429_) == 1 {
                            v_val_1430_ = leanh::lean_ctor_get(v___x_1429_, 0);
                            leanh::lean_inc(v_val_1430_);
                            leanh::lean_dec_ref_known(v___x_1429_, 1);
                            v___x_1431_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1426_, v___x_1428_);
                            if leanh::lean_obj_tag(v___x_1431_) == 1 {
                                v_val_1432_ = leanh::lean_ctor_get(v___x_1431_, 0);
                                leanh::lean_inc(v_val_1432_);
                                leanh::lean_dec_ref_known(v___x_1431_, 1);
                                v___x_1433_ = lean_nat_dec_le(v_val_1430_, v___x_1414_);
                                leanh::lean_dec(v_val_1430_);
                                if v___x_1433_ == 0 {
                                    leanh::lean_dec(v_val_1432_);
                                    v___y_1421_ = v___x_1433_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_1434_ = lean_nat_dec_le(v___x_1415_, v_val_1432_);
                                    leanh::lean_dec(v_val_1432_);
                                    v___y_1421_ = v___x_1434_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v___x_1431_);
                                leanh::lean_dec(v_val_1430_);
                                leanh::lean_dec_ref(v_ctx_1416_);
                                return v_result_1418_;
                            }
                        } else {
                            leanh::lean_dec(v___x_1429_);
                            leanh::lean_dec_ref(v_ctx_1416_);
                            return v_result_1418_;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_ctx_1416_);
                    return v_result_1418_;
                }
            }
            1 => {
                if v___y_1421_ == 0 {
                    leanh::lean_dec_ref(v_ctx_1416_);
                    return v_result_1418_;
                } else {
                    leanh::lean_inc_ref(v_i_1419_);
                    v___x_1422_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1422_, 0, v_ctx_1416_);
                    leanh::lean_ctor_set(v___x_1422_, 1, v_i_1419_);
                    v___x_1423_ = lean_array_push(v_result_1418_, v___x_1422_);
                    return v___x_1423_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_CodeAction_holeCodeActionProvider___lam__0___boxed(
    mut v___x_1435_: *mut leanh::LeanObject,
    mut v___x_1436_: *mut leanh::LeanObject,
    mut v_ctx_1437_: *mut leanh::LeanObject,
    mut v_info_1438_: *mut leanh::LeanObject,
    mut v_result_1439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1440_ = l_Lean_CodeAction_holeCodeActionProvider___lam__0(
        v___x_1435_,
        v___x_1436_,
        v_ctx_1437_,
        v_info_1438_,
        v_result_1439_,
    );
    leanh::lean_dec_ref(v_info_1438_);
    leanh::lean_dec(v___x_1436_);
    leanh::lean_dec(v___x_1435_);
    return v_res_1440_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(
    mut v_params_1441_: *mut leanh::LeanObject,
    mut v_snap_1442_: *mut leanh::LeanObject,
    mut v_fst_1443_: *mut leanh::LeanObject,
    mut v_snd_1444_: *mut leanh::LeanObject,
    mut v_as_1445_: *mut leanh::LeanObject,
    mut v_i_1446_: usize,
    mut v_stop_1447_: usize,
    mut v_b_1448_: *mut leanh::LeanObject,
    mut v___y_1449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: usize = 0;
    let mut v___x_1454_: usize = 0;
    let mut v___x_1456_: u8 = 0;
    let mut v___x_1833__overap_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1456_ = lean_usize_dec_eq(v_i_1446_, v_stop_1447_);
                if v___x_1456_ == 0 {
                    v___x_1833__overap_1457_ = lean_array_uget_borrowed(v_as_1445_, v_i_1446_);
                    leanh::lean_inc(v___x_1833__overap_1457_);
                    leanh::lean_inc_ref(v___y_1449_);
                    leanh::lean_inc_ref(v_snd_1444_);
                    leanh::lean_inc_ref(v_fst_1443_);
                    leanh::lean_inc_ref(v_snap_1442_);
                    leanh::lean_inc_ref(v_params_1441_);
                    v___x_1458_ = leanh::lean_apply_6(
                        v___x_1833__overap_1457_,
                        v_params_1441_,
                        v_snap_1442_,
                        v_fst_1443_,
                        v_snd_1444_,
                        v___y_1449_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_1458_) == 0 {
                        v_a_1459_ = leanh::lean_ctor_get(v___x_1458_, 0);
                        leanh::lean_inc(v_a_1459_);
                        leanh::lean_dec_ref_known(v___x_1458_, 1);
                        v___x_1460_ = l_Array_append___redArg(v_b_1448_, v_a_1459_);
                        leanh::lean_dec(v_a_1459_);
                        v_a_1452_ = v___x_1460_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_b_1448_);
                        if leanh::lean_obj_tag(v___x_1458_) == 0 {
                            v_a_1461_ = leanh::lean_ctor_get(v___x_1458_, 0);
                            leanh::lean_inc(v_a_1461_);
                            leanh::lean_dec_ref_known(v___x_1458_, 1);
                            v_a_1452_ = v_a_1461_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_snd_1444_);
                            leanh::lean_dec_ref(v_fst_1443_);
                            leanh::lean_dec_ref(v_snap_1442_);
                            leanh::lean_dec_ref(v_params_1441_);
                            return v___x_1458_;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_snd_1444_);
                    leanh::lean_dec_ref(v_fst_1443_);
                    leanh::lean_dec_ref(v_snap_1442_);
                    leanh::lean_dec_ref(v_params_1441_);
                    v___x_1462_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1462_, 0, v_b_1448_);
                    return v___x_1462_;
                }
            }
            1 => {
                v___x_1453_ = 1usize;
                v___x_1454_ = lean_usize_add(v_i_1446_, v___x_1453_);
                v_i_1446_ = v___x_1454_;
                v_b_1448_ = v_a_1452_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2___boxed(
    mut v_params_1463_: *mut leanh::LeanObject,
    mut v_snap_1464_: *mut leanh::LeanObject,
    mut v_fst_1465_: *mut leanh::LeanObject,
    mut v_snd_1466_: *mut leanh::LeanObject,
    mut v_as_1467_: *mut leanh::LeanObject,
    mut v_i_1468_: *mut leanh::LeanObject,
    mut v_stop_1469_: *mut leanh::LeanObject,
    mut v_b_1470_: *mut leanh::LeanObject,
    mut v___y_1471_: *mut leanh::LeanObject,
    mut v___y_1472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1473_: usize = 0;
    let mut v_stop_boxed_1474_: usize = 0;
    let mut v_res_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1473_ = leanh::lean_unbox_usize(v_i_1468_);
    leanh::lean_dec(v_i_1468_);
    v_stop_boxed_1474_ = leanh::lean_unbox_usize(v_stop_1469_);
    leanh::lean_dec(v_stop_1469_);
    v_res_1475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(v_params_1463_, v_snap_1464_, v_fst_1465_, v_snd_1466_, v_as_1467_, v_i_boxed_1473_, v_stop_boxed_1474_, v_b_1470_, v___y_1471_);
    leanh::lean_dec_ref(v___y_1471_);
    leanh::lean_dec_ref(v_as_1467_);
    return v_res_1475_;
}
pub unsafe fn _init_l_Lean_CodeAction_holeCodeActionProvider___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1478_ = l_Array_instInhabited(leanh::lean_box(0));
    return v___x_1478_;
}
pub unsafe fn _init_l_Lean_CodeAction_holeCodeActionProvider___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1479_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_CodeAction_holeCodeActionProvider___closed__1),
        core::ptr::addr_of_mut!(l_Lean_CodeAction_holeCodeActionProvider___closed__1_once),
        _init_l_Lean_CodeAction_holeCodeActionProvider___closed__1,
    );
    v___x_1480_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1480_, 0, v___x_1479_);
    leanh::lean_ctor_set(v___x_1480_, 1, v___x_1479_);
    return v___x_1480_;
}
pub unsafe fn l_Lean_CodeAction_holeCodeActionProvider(
    mut v_params_1483_: *mut leanh::LeanObject,
    mut v_snap_1484_: *mut leanh::LeanObject,
    mut v_a_1485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1491_: u8 = 0;
    let mut v_toEditableDocumentCore_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_meta_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_end_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: u8 = 0;
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: u8 = 0;
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: u8 = 0;
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: usize = 0;
    let mut v___x_1533_: usize = 0;
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: usize = 0;
    let mut v___x_1536_: usize = 0;
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1538_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1487_ = l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(v_a_1485_);
                v_a_1488_ = leanh::lean_ctor_get(v___x_1487_, 0);
                v_isSharedCheck_1538_ = (!leanh::lean_is_exclusive(v___x_1487_)) as u8;
                if v_isSharedCheck_1538_ == 0 {
                    v___x_1490_ = v___x_1487_;
                    v_isShared_1491_ = v_isSharedCheck_1538_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1488_);
                    leanh::lean_dec(v___x_1487_);
                    v___x_1490_ = leanh::lean_box(0);
                    v_isShared_1491_ = v_isSharedCheck_1538_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toEditableDocumentCore_1492_ = leanh::lean_ctor_get(v_a_1488_, 0);
                leanh::lean_inc_ref(v_toEditableDocumentCore_1492_);
                leanh::lean_dec(v_a_1488_);
                v_meta_1493_ = leanh::lean_ctor_get(v_toEditableDocumentCore_1492_, 0);
                leanh::lean_inc_ref(v_meta_1493_);
                leanh::lean_dec_ref(v_toEditableDocumentCore_1492_);
                v_range_1494_ = leanh::lean_ctor_get(v_params_1483_, 3);
                v_text_1495_ = leanh::lean_ctor_get(v_meta_1493_, 3);
                leanh::lean_inc_ref(v_text_1495_);
                leanh::lean_dec_ref(v_meta_1493_);
                v_start_1496_ = leanh::lean_ctor_get(v_range_1494_, 0);
                v_end_1497_ = leanh::lean_ctor_get(v_range_1494_, 1);
                leanh::lean_inc_ref(v_start_1496_);
                v___x_1498_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1495_, v_start_1496_);
                leanh::lean_inc_ref(v_end_1497_);
                v___x_1499_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1495_, v_end_1497_);
                leanh::lean_dec_ref(v_text_1495_);
                v___f_1500_ = leanh::lean_alloc_closure(
                    l_Lean_CodeAction_holeCodeActionProvider___lam__0___boxed
                        as *mut core::ffi::c_void,
                    5,
                    2,
                );
                leanh::lean_closure_set(v___f_1500_, 0, v___x_1499_);
                leanh::lean_closure_set(v___f_1500_, 1, v___x_1498_);
                v___x_1501_ = leanh::lean_unsigned_to_nat(0);
                v___x_1502_ = l_Lean_CodeAction_holeCodeActionProvider___closed__0;
                leanh::lean_inc_ref(v_snap_1484_);
                v___x_1503_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_snap_1484_);
                v___x_1504_ =
                    l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_1500_, v___x_1502_, v___x_1503_);
                v___x_1505_ = lean_array_get_size(v___x_1504_);
                v___x_1506_ = leanh::lean_unsigned_to_nat(1);
                v___x_1507_ = lean_nat_dec_eq(v___x_1505_, v___x_1506_);
                if v___x_1507_ == 0 {
                    leanh::lean_dec(v___x_1504_);
                    leanh::lean_dec_ref(v_snap_1484_);
                    leanh::lean_dec_ref(v_params_1483_);
                    if v_isShared_1491_ == 0 {
                        leanh::lean_ctor_set(v___x_1490_, 0, v___x_1502_);
                        v___x_1509_ = v___x_1490_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1510_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1502_);
                        v___x_1509_ = v_reuseFailAlloc_1510_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1511_ = lean_array_fget(v___x_1504_, v___x_1501_);
                    leanh::lean_dec(v___x_1504_);
                    v_fst_1512_ = leanh::lean_ctor_get(v___x_1511_, 0);
                    leanh::lean_inc(v_fst_1512_);
                    v_snd_1513_ = leanh::lean_ctor_get(v___x_1511_, 1);
                    leanh::lean_inc(v_snd_1513_);
                    leanh::lean_dec(v___x_1511_);
                    v___x_1514_ = l_Lean_CodeAction_holeCodeActionExt;
                    v_toEnvExtension_1515_ = leanh::lean_ctor_get(v___x_1514_, 0);
                    v_asyncMode_1516_ = leanh::lean_ctor_get(v_toEnvExtension_1515_, 2);
                    v___x_1517_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_CodeAction_holeCodeActionProvider___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_CodeAction_holeCodeActionProvider___closed__2_once
                        ),
                        _init_l_Lean_CodeAction_holeCodeActionProvider___closed__2,
                    );
                    v___x_1518_ = l_Lean_Server_Snapshots_Snapshot_env(v_snap_1484_);
                    v___x_1519_ = leanh::lean_box(0);
                    v___x_1520_ = l_Lean_PersistentEnvExtension_getState___redArg(
                        v___x_1517_,
                        v___x_1514_,
                        v___x_1518_,
                        v_asyncMode_1516_,
                        v___x_1519_,
                    );
                    v_snd_1521_ = leanh::lean_ctor_get(v___x_1520_, 1);
                    leanh::lean_inc(v_snd_1521_);
                    leanh::lean_dec(v___x_1520_);
                    v___x_1522_ = l_Lean_CodeAction_holeCodeActionProvider___closed__3;
                    v___x_1523_ = lean_array_get_size(v_snd_1521_);
                    v___x_1524_ = lean_nat_dec_lt(v___x_1501_, v___x_1523_);
                    if v___x_1524_ == 0 {
                        leanh::lean_dec(v_snd_1521_);
                        leanh::lean_dec(v_snd_1513_);
                        leanh::lean_dec(v_fst_1512_);
                        leanh::lean_dec_ref(v_snap_1484_);
                        leanh::lean_dec_ref(v_params_1483_);
                        if v_isShared_1491_ == 0 {
                            leanh::lean_ctor_set(v___x_1490_, 0, v___x_1522_);
                            v___x_1526_ = v___x_1490_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1527_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1522_);
                            v___x_1526_ = v_reuseFailAlloc_1527_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1528_ = lean_nat_dec_le(v___x_1523_, v___x_1523_);
                        if v___x_1528_ == 0 {
                            if v___x_1524_ == 0 {
                                leanh::lean_dec(v_snd_1521_);
                                leanh::lean_dec(v_snd_1513_);
                                leanh::lean_dec(v_fst_1512_);
                                leanh::lean_dec_ref(v_snap_1484_);
                                leanh::lean_dec_ref(v_params_1483_);
                                if v_isShared_1491_ == 0 {
                                    leanh::lean_ctor_set(v___x_1490_, 0, v___x_1522_);
                                    v___x_1530_ = v___x_1490_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1531_ =
                                        leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1531_,
                                        0,
                                        v___x_1522_,
                                    );
                                    v___x_1530_ = v_reuseFailAlloc_1531_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                leanh::lean_del_object(v___x_1490_);
                                v___x_1532_ = 0usize;
                                v___x_1533_ = lean_usize_of_nat(v___x_1523_);
                                v___x_1534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(v_params_1483_, v_snap_1484_, v_fst_1512_, v_snd_1513_, v_snd_1521_, v___x_1532_, v___x_1533_, v___x_1522_, v_a_1485_);
                                leanh::lean_dec(v_snd_1521_);
                                return v___x_1534_;
                            }
                        } else {
                            leanh::lean_del_object(v___x_1490_);
                            v___x_1535_ = 0usize;
                            v___x_1536_ = lean_usize_of_nat(v___x_1523_);
                            v___x_1537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(v_params_1483_, v_snap_1484_, v_fst_1512_, v_snd_1513_, v_snd_1521_, v___x_1535_, v___x_1536_, v___x_1522_, v_a_1485_);
                            leanh::lean_dec(v_snd_1521_);
                            return v___x_1537_;
                        }
                    }
                }
            }
            2 => {
                return v___x_1509_;
            }
            3 => {
                return v___x_1526_;
            }
            4 => {
                return v___x_1530_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_CodeAction_holeCodeActionProvider___boxed(
    mut v_params_1539_: *mut leanh::LeanObject,
    mut v_snap_1540_: *mut leanh::LeanObject,
    mut v_a_1541_: *mut leanh::LeanObject,
    mut v_a_1542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1543_ = l_Lean_CodeAction_holeCodeActionProvider(v_params_1539_, v_snap_1540_, v_a_1541_);
    leanh::lean_dec_ref(v_a_1541_);
    return v_res_1543_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1()
-> *mut leanh::LeanObject {
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1551_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2;
    v___x_1552_ = leanh::lean_alloc_closure(
        l_Lean_CodeAction_holeCodeActionProvider___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_1553_ = l_Lean_Server_addBuiltinCodeActionProvider(v___x_1551_, v___x_1552_);
    return v___x_1553_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___boxed(
    mut v_a_1554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1555_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1();
    return v_res_1555_;
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_ctorIdx(
    mut v_x_1556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1556_) == 0 {
        let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1557_ = leanh::lean_unsigned_to_nat(0);
        return v___x_1557_;
    } else {
        let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1558_ = leanh::lean_unsigned_to_nat(1);
        return v___x_1558_;
    }
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_ctorIdx___boxed(
    mut v_x_1559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1560_ = l_Lean_CodeAction_FindTacticResult_ctorIdx(v_x_1559_);
    leanh::lean_dec_ref(v_x_1559_);
    return v_res_1560_;
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(
    mut v_t_1561_: *mut leanh::LeanObject,
    mut v_k_1562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1561_) == 0 {
        let mut v_a_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1563_ = leanh::lean_ctor_get(v_t_1561_, 0);
        leanh::lean_inc(v_a_1563_);
        leanh::lean_dec_ref_known(v_t_1561_, 1);
        v___x_1564_ = leanh::lean_apply_1(v_k_1562_, v_a_1563_);
        return v___x_1564_;
    } else {
        let mut v_preferred_1565_: u8 = 0;
        let mut v_insertIdx_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_preferred_1565_ = leanh::lean_ctor_get_uint8(
            v_t_1561_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        );
        v_insertIdx_1566_ = leanh::lean_ctor_get(v_t_1561_, 0);
        leanh::lean_inc(v_insertIdx_1566_);
        v_a_1567_ = leanh::lean_ctor_get(v_t_1561_, 1);
        leanh::lean_inc(v_a_1567_);
        leanh::lean_dec_ref_known(v_t_1561_, 2);
        v___x_1568_ = leanh::lean_box((v_preferred_1565_) as usize);
        v___x_1569_ =
            leanh::lean_apply_3(v_k_1562_, v___x_1568_, v_insertIdx_1566_, v_a_1567_);
        return v___x_1569_;
    }
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_ctorElim(
    mut v_motive_1570_: *mut leanh::LeanObject,
    mut v_ctorIdx_1571_: *mut leanh::LeanObject,
    mut v_t_1572_: *mut leanh::LeanObject,
    mut v_h_1573_: *mut leanh::LeanObject,
    mut v_k_1574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1575_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_1572_, v_k_1574_);
    return v___x_1575_;
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_ctorElim___boxed(
    mut v_motive_1576_: *mut leanh::LeanObject,
    mut v_ctorIdx_1577_: *mut leanh::LeanObject,
    mut v_t_1578_: *mut leanh::LeanObject,
    mut v_h_1579_: *mut leanh::LeanObject,
    mut v_k_1580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1581_ = l_Lean_CodeAction_FindTacticResult_ctorElim(
        v_motive_1576_,
        v_ctorIdx_1577_,
        v_t_1578_,
        v_h_1579_,
        v_k_1580_,
    );
    leanh::lean_dec(v_ctorIdx_1577_);
    return v_res_1581_;
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_tactic_elim___redArg(
    mut v_t_1582_: *mut leanh::LeanObject,
    mut v_tactic_1583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1584_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_1582_, v_tactic_1583_);
    return v___x_1584_;
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_tactic_elim(
    mut v_motive_1585_: *mut leanh::LeanObject,
    mut v_t_1586_: *mut leanh::LeanObject,
    mut v_h_1587_: *mut leanh::LeanObject,
    mut v_tactic_1588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1589_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_1586_, v_tactic_1588_);
    return v___x_1589_;
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_tacticSeq_elim___redArg(
    mut v_t_1590_: *mut leanh::LeanObject,
    mut v_tacticSeq_1591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1592_ =
        l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_1590_, v_tacticSeq_1591_);
    return v___x_1592_;
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_tacticSeq_elim(
    mut v_motive_1593_: *mut leanh::LeanObject,
    mut v_t_1594_: *mut leanh::LeanObject,
    mut v_h_1595_: *mut leanh::LeanObject,
    mut v_tacticSeq_1596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1597_ =
        l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_1594_, v_tacticSeq_1596_);
    return v___x_1597_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(
    mut v_range_1598_: *mut leanh::LeanObject,
    mut v_stx_1599_: *mut leanh::LeanObject,
    mut v_prev_x3f_1600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1601_: u8 = 0;
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1607_: u8 = 0;
    let mut v___y_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: u8 = 0;
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trailing_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: u8 = 0;
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: u8 = 0;
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: u8 = 0;
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1635_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1601_ = 1;
                v___x_1602_ = l_Lean_Syntax_getPos_x3f(v_stx_1599_, v___x_1601_);
                if leanh::lean_obj_tag(v___x_1602_) == 0 {
                    leanh::lean_dec(v_prev_x3f_1600_);
                    v___x_1603_ = leanh::lean_box(0);
                    return v___x_1603_;
                } else {
                    v_val_1604_ = leanh::lean_ctor_get(v___x_1602_, 0);
                    v_isSharedCheck_1635_ = (!leanh::lean_is_exclusive(v___x_1602_)) as u8;
                    if v_isSharedCheck_1635_ == 0 {
                        v___x_1606_ = v___x_1602_;
                        v_isShared_1607_ = v_isSharedCheck_1635_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1604_);
                        leanh::lean_dec(v___x_1602_);
                        v___x_1606_ = leanh::lean_box(0);
                        v_isShared_1607_ = v_isSharedCheck_1635_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_prev_x3f_1600_) == 0 {
                    leanh::lean_inc(v_val_1604_);
                    v___y_1609_ = v_val_1604_;
                    state = 2;
                    continue;
                } else {
                    v_val_1634_ = leanh::lean_ctor_get(v_prev_x3f_1600_, 0);
                    leanh::lean_inc(v_val_1634_);
                    leanh::lean_dec_ref_known(v_prev_x3f_1600_, 1);
                    v___y_1609_ = v_val_1634_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_start_1610_ = leanh::lean_ctor_get(v_range_1598_, 0);
                v_stop_1611_ = leanh::lean_ctor_get(v_range_1598_, 1);
                v___x_1612_ = lean_nat_dec_le(v___y_1609_, v_start_1610_);
                leanh::lean_dec(v___y_1609_);
                if v___x_1612_ == 0 {
                    leanh::lean_del_object(v___x_1606_);
                    leanh::lean_dec(v_val_1604_);
                    v___x_1613_ = leanh::lean_box(0);
                    return v___x_1613_;
                } else {
                    v___x_1614_ = l_Lean_Syntax_getTailInfo(v_stx_1599_);
                    if leanh::lean_obj_tag(v___x_1614_) == 0 {
                        v_trailing_1615_ = leanh::lean_ctor_get(v___x_1614_, 2);
                        leanh::lean_inc_ref(v_trailing_1615_);
                        v_endPos_1616_ = leanh::lean_ctor_get(v___x_1614_, 3);
                        leanh::lean_inc(v_endPos_1616_);
                        leanh::lean_dec_ref_known(v___x_1614_, 4);
                        v_startPos_1617_ = leanh::lean_ctor_get(v_trailing_1615_, 1);
                        leanh::lean_inc(v_startPos_1617_);
                        v_stopPos_1618_ = leanh::lean_ctor_get(v_trailing_1615_, 2);
                        leanh::lean_inc(v_stopPos_1618_);
                        leanh::lean_dec_ref(v_trailing_1615_);
                        v___x_1619_ = lean_nat_sub(v_stopPos_1618_, v_startPos_1617_);
                        leanh::lean_dec(v_startPos_1617_);
                        leanh::lean_dec(v_stopPos_1618_);
                        v___x_1620_ = lean_nat_add(v_endPos_1616_, v___x_1619_);
                        leanh::lean_dec(v___x_1619_);
                        v___x_1621_ = lean_nat_dec_le(v_stop_1611_, v___x_1620_);
                        leanh::lean_dec(v___x_1620_);
                        if v___x_1621_ == 0 {
                            leanh::lean_dec(v_endPos_1616_);
                            leanh::lean_del_object(v___x_1606_);
                            leanh::lean_dec(v_val_1604_);
                            v___x_1622_ = leanh::lean_box(0);
                            return v___x_1622_;
                        } else {
                            v___x_1623_ = lean_nat_dec_le(v_val_1604_, v_start_1610_);
                            leanh::lean_dec(v_val_1604_);
                            if v___x_1623_ == 0 {
                                leanh::lean_dec(v_endPos_1616_);
                                v___x_1624_ = leanh::lean_box((v___x_1623_) as usize);
                                if v_isShared_1607_ == 0 {
                                    leanh::lean_ctor_set(v___x_1606_, 0, v___x_1624_);
                                    v___x_1626_ = v___x_1606_;
                                    state = 3;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1627_ =
                                        leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1627_,
                                        0,
                                        v___x_1624_,
                                    );
                                    v___x_1626_ = v_reuseFailAlloc_1627_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                v___x_1628_ = lean_nat_dec_le(v_stop_1611_, v_endPos_1616_);
                                leanh::lean_dec(v_endPos_1616_);
                                v___x_1629_ = leanh::lean_box((v___x_1628_) as usize);
                                if v_isShared_1607_ == 0 {
                                    leanh::lean_ctor_set(v___x_1606_, 0, v___x_1629_);
                                    v___x_1631_ = v___x_1606_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1632_ =
                                        leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1632_,
                                        0,
                                        v___x_1629_,
                                    );
                                    v___x_1631_ = v_reuseFailAlloc_1632_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_1614_);
                        leanh::lean_del_object(v___x_1606_);
                        leanh::lean_dec(v_val_1604_);
                        v___x_1633_ = leanh::lean_box(0);
                        return v___x_1633_;
                    }
                }
            }
            3 => {
                return v___x_1626_;
            }
            4 => {
                return v___x_1631_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit___boxed(
    mut v_range_1636_: *mut leanh::LeanObject,
    mut v_stx_1637_: *mut leanh::LeanObject,
    mut v_prev_x3f_1638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1639_ =
        l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(
            v_range_1636_,
            v_stx_1637_,
            v_prev_x3f_1638_,
        );
    leanh::lean_dec(v_stx_1637_);
    leanh::lean_dec_ref(v_range_1636_);
    return v_res_1639_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(
    mut v_r_u2081_1640_: *mut leanh::LeanObject,
    mut v_r_u2082_1641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_r_u2081_1640_) == 1 {
        let mut v_val_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1642_ = leanh::lean_ctor_get(v_r_u2081_1640_, 0);
        if leanh::lean_obj_tag(v_val_1642_) == 1 {
            let mut v_preferred_1643_: u8 = 0;
            v_preferred_1643_ = leanh::lean_ctor_get_uint8(
                v_val_1642_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
            );
            if v_preferred_1643_ == 1 {
                if leanh::lean_obj_tag(v_r_u2082_1641_) == 1 {
                    let mut v_preferred_1644_: u8 = 0;
                    v_preferred_1644_ = leanh::lean_ctor_get_uint8(
                        v_r_u2082_1641_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    if v_preferred_1644_ == 0 {
                        leanh::lean_inc_ref(v_val_1642_);
                        return v_val_1642_;
                    } else {
                        leanh::lean_inc_ref(v_r_u2082_1641_);
                        return v_r_u2082_1641_;
                    }
                } else {
                    leanh::lean_inc_ref(v_r_u2082_1641_);
                    return v_r_u2082_1641_;
                }
            } else {
                leanh::lean_inc_ref(v_r_u2082_1641_);
                return v_r_u2082_1641_;
            }
        } else {
            leanh::lean_inc_ref(v_r_u2082_1641_);
            return v_r_u2082_1641_;
        }
    } else {
        leanh::lean_inc_ref(v_r_u2082_1641_);
        return v_r_u2082_1641_;
    }
}
pub unsafe fn l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge___boxed(
    mut v_r_u2081_1645_: *mut leanh::LeanObject,
    mut v_r_u2082_1646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1647_ =
        l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(
            v_r_u2081_1645_,
            v_r_u2082_1646_,
        );
    leanh::lean_dec_ref(v_r_u2082_1646_);
    leanh::lean_dec(v_r_u2081_1645_);
    return v_res_1647_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(
    mut v_upperBound_1651_: *mut leanh::LeanObject,
    mut v___x_1652_: *mut leanh::LeanObject,
    mut v_range_1653_: *mut leanh::LeanObject,
    mut v_a_1654_: *mut leanh::LeanObject,
    mut v_b_1655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: u8 = 0;
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: u8 = 0;
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1672_: u8 = 0;
    let mut v_stop_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: u8 = 0;
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1677_: u8 = 0;
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1684_: u8 = 0;
    let mut v_unused_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1687_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1661_ = lean_nat_dec_lt(v_a_1654_, v_upperBound_1651_);
                if v___x_1661_ == 0 {
                    leanh::lean_dec(v_a_1654_);
                    leanh::lean_dec_ref(v_range_1653_);
                    leanh::lean_inc_ref(v_b_1655_);
                    return v_b_1655_;
                } else {
                    v___x_1662_ = leanh::lean_box(0);
                    v___x_1663_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0;
                    v___x_1664_ = leanh::lean_unsigned_to_nat(2);
                    v___x_1665_ = lean_nat_mul(v___x_1664_, v_a_1654_);
                    v___x_1666_ = l_Lean_Syntax_getArg(v___x_1652_, v___x_1665_);
                    leanh::lean_dec(v___x_1665_);
                    v___x_1667_ = 0;
                    v___x_1668_ = l_Lean_Syntax_getPos_x3f(v___x_1666_, v___x_1667_);
                    leanh::lean_dec(v___x_1666_);
                    if leanh::lean_obj_tag(v___x_1668_) == 1 {
                        v_val_1669_ = leanh::lean_ctor_get(v___x_1668_, 0);
                        v_isSharedCheck_1687_ =
                            (!leanh::lean_is_exclusive(v___x_1668_)) as u8;
                        if v_isSharedCheck_1687_ == 0 {
                            v___x_1671_ = v___x_1668_;
                            v_isShared_1672_ = v_isSharedCheck_1687_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1669_);
                            leanh::lean_dec(v___x_1668_);
                            v___x_1671_ = leanh::lean_box(0);
                            v_isShared_1672_ = v_isSharedCheck_1687_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1668_);
                        v_a_1657_ = v___x_1663_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1658_ = leanh::lean_unsigned_to_nat(1);
                v___x_1659_ = lean_nat_add(v_a_1654_, v___x_1658_);
                leanh::lean_dec(v_a_1654_);
                v_a_1654_ = v___x_1659_;
                v_b_1655_ = v_a_1657_;
                state = 0;
                continue;
            }
            2 => {
                v_stop_1673_ = leanh::lean_ctor_get(v_range_1653_, 1);
                v___x_1674_ = lean_nat_dec_lt(v_stop_1673_, v_val_1669_);
                leanh::lean_dec(v_val_1669_);
                if v___x_1674_ == 0 {
                    leanh::lean_del_object(v___x_1671_);
                    v_a_1657_ = v___x_1663_;
                    state = 1;
                    continue;
                } else {
                    v_isSharedCheck_1684_ = (!leanh::lean_is_exclusive(v_range_1653_)) as u8;
                    if v_isSharedCheck_1684_ == 0 {
                        v_unused_1685_ = leanh::lean_ctor_get(v_range_1653_, 1);
                        leanh::lean_dec(v_unused_1685_);
                        v_unused_1686_ = leanh::lean_ctor_get(v_range_1653_, 0);
                        leanh::lean_dec(v_unused_1686_);
                        v___x_1676_ = v_range_1653_;
                        v_isShared_1677_ = v_isSharedCheck_1684_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_range_1653_);
                        v___x_1676_ = leanh::lean_box(0);
                        v_isShared_1677_ = v_isSharedCheck_1684_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1672_ == 0 {
                    leanh::lean_ctor_set(v___x_1671_, 0, v_a_1654_);
                    v___x_1679_ = v___x_1671_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1683_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1654_);
                    v___x_1679_ = v_reuseFailAlloc_1683_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1677_ == 0 {
                    leanh::lean_ctor_set(v___x_1676_, 1, v___x_1662_);
                    leanh::lean_ctor_set(v___x_1676_, 0, v___x_1679_);
                    v___x_1681_ = v___x_1676_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1682_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1682_, 1, v___x_1662_);
                    v___x_1681_ = v_reuseFailAlloc_1682_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1681_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___boxed(
    mut v_upperBound_1688_: *mut leanh::LeanObject,
    mut v___x_1689_: *mut leanh::LeanObject,
    mut v_range_1690_: *mut leanh::LeanObject,
    mut v_a_1691_: *mut leanh::LeanObject,
    mut v_b_1692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(v_upperBound_1688_, v___x_1689_, v_range_1690_, v_a_1691_, v_b_1692_);
    leanh::lean_dec_ref(v_b_1692_);
    leanh::lean_dec(v___x_1689_);
    leanh::lean_dec(v_upperBound_1688_);
    return v_res_1693_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(
    mut v_stx_1694_: *mut leanh::LeanObject,
    mut v_a_1695_: *mut leanh::LeanObject,
    mut v___x_1696_: u8,
    mut v_snd_1697_: *mut leanh::LeanObject,
    mut v_____r_1698_: *mut leanh::LeanObject,
    mut v_childRes_1699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1705_ = l_Lean_Syntax_getArg(v_stx_1694_, v_a_1695_);
                v___x_1706_ = l_Lean_Syntax_getTailPos_x3f(v___x_1705_, v___x_1696_);
                leanh::lean_dec(v___x_1705_);
                if leanh::lean_obj_tag(v___x_1706_) == 0 {
                    v___y_1701_ = v_snd_1697_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_1697_);
                    v___y_1701_ = v___x_1706_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1702_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1702_, 0, v_childRes_1699_);
                leanh::lean_ctor_set(v___x_1702_, 1, v___y_1701_);
                v___x_1703_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1703_, 0, v___x_1702_);
                v___x_1704_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1704_, 0, v___x_1703_);
                return v___x_1704_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0___boxed(
    mut v_stx_1707_: *mut leanh::LeanObject,
    mut v_a_1708_: *mut leanh::LeanObject,
    mut v___x_1709_: *mut leanh::LeanObject,
    mut v_snd_1710_: *mut leanh::LeanObject,
    mut v_____r_1711_: *mut leanh::LeanObject,
    mut v_childRes_1712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4623__boxed_1713_: u8 = 0;
    let mut v_res_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4623__boxed_1713_ = (leanh::lean_unbox(v___x_1709_) as u8);
    v_res_1714_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_1707_, v_a_1708_, v___x_4623__boxed_1713_, v_snd_1710_, v_____r_1711_, v_childRes_1712_);
    leanh::lean_dec(v_a_1708_);
    leanh::lean_dec(v_stx_1707_);
    return v_res_1714_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(
    mut v___y_1725_: *mut leanh::LeanObject,
    mut v___x_1726_: u8,
    mut v___x_1727_: *mut leanh::LeanObject,
    mut v_range_1728_: *mut leanh::LeanObject,
    mut v___x_1729_: *mut leanh::LeanObject,
    mut v_preferred_1730_: *mut leanh::LeanObject,
    mut v_a_1731_: *mut leanh::LeanObject,
    mut v_b_1732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_inner_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1740_: u8 = 0;
    let mut v_upperBound_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1744_: u8 = 0;
    let mut v_val_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1748_: u8 = 0;
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: u8 = 0;
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1780_: u8 = 0;
    let mut v___x_1781_: u8 = 0;
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1790_: u8 = 0;
    let mut v_reuseFailAlloc_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1795_: u8 = 0;
    let mut v_isSharedCheck_1796_: u8 = 0;
    let mut v_unused_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1798_: u8 = 0;
    let mut v_unused_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_inner_1733_ = leanh::lean_ctor_get(v_a_1731_, 2);
                leanh::lean_inc(v_inner_1733_);
                v_next_1734_ = leanh::lean_ctor_get(v_inner_1733_, 0);
                leanh::lean_inc(v_next_1734_);
                if leanh::lean_obj_tag(v_next_1734_) == 0 {
                    leanh::lean_dec(v_inner_1733_);
                    leanh::lean_dec_ref(v_a_1731_);
                    leanh::lean_dec_ref(v_preferred_1730_);
                    leanh::lean_dec(v___x_1729_);
                    leanh::lean_dec_ref(v_range_1728_);
                    leanh::lean_dec(v___x_1727_);
                    v___x_1735_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1735_, 0, v_b_1732_);
                    return v___x_1735_;
                } else {
                    v_nextIdx_1736_ = leanh::lean_ctor_get(v_a_1731_, 0);
                    v_n_1737_ = leanh::lean_ctor_get(v_a_1731_, 1);
                    v_isSharedCheck_1798_ = (!leanh::lean_is_exclusive(v_a_1731_)) as u8;
                    if v_isSharedCheck_1798_ == 0 {
                        v_unused_1799_ = leanh::lean_ctor_get(v_a_1731_, 2);
                        leanh::lean_dec(v_unused_1799_);
                        v___x_1739_ = v_a_1731_;
                        v_isShared_1740_ = v_isSharedCheck_1798_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_n_1737_);
                        leanh::lean_inc(v_nextIdx_1736_);
                        leanh::lean_dec(v_a_1731_);
                        v___x_1739_ = leanh::lean_box(0);
                        v_isShared_1740_ = v_isSharedCheck_1798_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_upperBound_1741_ = leanh::lean_ctor_get(v_inner_1733_, 1);
                v_isSharedCheck_1796_ = (!leanh::lean_is_exclusive(v_inner_1733_)) as u8;
                if v_isSharedCheck_1796_ == 0 {
                    v_unused_1797_ = leanh::lean_ctor_get(v_inner_1733_, 0);
                    leanh::lean_dec(v_unused_1797_);
                    v___x_1743_ = v_inner_1733_;
                    v_isShared_1744_ = v_isSharedCheck_1796_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_upperBound_1741_);
                    leanh::lean_dec(v_inner_1733_);
                    v___x_1743_ = leanh::lean_box(0);
                    v_isShared_1744_ = v_isSharedCheck_1796_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_val_1745_ = leanh::lean_ctor_get(v_next_1734_, 0);
                v_isSharedCheck_1795_ = (!leanh::lean_is_exclusive(v_next_1734_)) as u8;
                if v_isSharedCheck_1795_ == 0 {
                    v___x_1747_ = v_next_1734_;
                    v_isShared_1748_ = v_isSharedCheck_1795_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_val_1745_);
                    leanh::lean_dec(v_next_1734_);
                    v___x_1747_ = leanh::lean_box(0);
                    v_isShared_1748_ = v_isSharedCheck_1795_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1749_ = lean_nat_add(v_val_1745_, v_nextIdx_1736_);
                leanh::lean_dec(v_nextIdx_1736_);
                leanh::lean_dec(v_val_1745_);
                v___x_1750_ = lean_nat_dec_lt(v___x_1749_, v_upperBound_1741_);
                if v___x_1750_ == 0 {
                    leanh::lean_dec(v___x_1749_);
                    leanh::lean_del_object(v___x_1743_);
                    leanh::lean_dec(v_upperBound_1741_);
                    leanh::lean_del_object(v___x_1739_);
                    leanh::lean_dec(v_n_1737_);
                    leanh::lean_dec_ref(v_preferred_1730_);
                    leanh::lean_dec(v___x_1729_);
                    leanh::lean_dec_ref(v_range_1728_);
                    leanh::lean_dec(v___x_1727_);
                    if v_isShared_1748_ == 0 {
                        leanh::lean_ctor_set(v___x_1747_, 0, v_b_1732_);
                        v___x_1752_ = v___x_1747_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1753_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_b_1732_);
                        v___x_1752_ = v_reuseFailAlloc_1753_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_1754_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1755_ = lean_nat_add(v___x_1749_, v___x_1754_);
                    if v_isShared_1748_ == 0 {
                        leanh::lean_ctor_set(v___x_1747_, 0, v___x_1755_);
                        v___x_1757_ = v___x_1747_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1794_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1755_);
                        v___x_1757_ = v_reuseFailAlloc_1794_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1752_;
            }
            5 => {
                if v_isShared_1744_ == 0 {
                    leanh::lean_ctor_set(v___x_1743_, 0, v___x_1757_);
                    v___x_1759_ = v___x_1743_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1793_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1757_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_upperBound_1741_);
                    v___x_1759_ = v_reuseFailAlloc_1793_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_inc(v_n_1737_);
                if v_isShared_1740_ == 0 {
                    leanh::lean_ctor_set(v___x_1739_, 2, v___x_1759_);
                    leanh::lean_ctor_set(v___x_1739_, 0, v_n_1737_);
                    v___x_1761_ = v___x_1739_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1792_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_n_1737_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_n_1737_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1792_, 2, v___x_1759_);
                    v___x_1761_ = v_reuseFailAlloc_1792_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1770_ = l_Lean_Syntax_getArg(v___x_1727_, v___x_1749_);
                v___x_1771_ = leanh::lean_box(0);
                v___x_1772_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(v_range_1728_, v___x_1770_, v___x_1771_);
                if leanh::lean_obj_tag(v___x_1772_) == 1 {
                    v_val_1773_ = leanh::lean_ctor_get(v___x_1772_, 0);
                    leanh::lean_inc(v_val_1773_);
                    leanh::lean_dec_ref_known(v___x_1772_, 1);
                    leanh::lean_inc(v___x_1727_);
                    v___x_1774_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1774_, 0, v___x_1727_);
                    leanh::lean_ctor_set(v___x_1774_, 1, v___x_1749_);
                    leanh::lean_inc(v___x_1729_);
                    v___x_1775_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1775_, 0, v___x_1774_);
                    leanh::lean_ctor_set(v___x_1775_, 1, v___x_1729_);
                    leanh::lean_inc(v___x_1770_);
                    leanh::lean_inc_ref(v___x_1775_);
                    leanh::lean_inc_ref(v_range_1728_);
                    leanh::lean_inc_ref(v_preferred_1730_);
                    v___x_1776_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(v_preferred_1730_, v_range_1728_, v___x_1775_, v___x_1770_, v___x_1771_);
                    if leanh::lean_obj_tag(v___x_1776_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1775_, 2);
                        leanh::lean_dec(v_val_1773_);
                        leanh::lean_dec(v___x_1770_);
                        leanh::lean_dec_ref(v___x_1761_);
                        leanh::lean_dec(v_b_1732_);
                        leanh::lean_dec_ref(v_preferred_1730_);
                        leanh::lean_dec(v___x_1729_);
                        leanh::lean_dec_ref(v_range_1728_);
                        leanh::lean_dec(v___x_1727_);
                        return v___x_1776_;
                    } else {
                        v_val_1777_ = leanh::lean_ctor_get(v___x_1776_, 0);
                        v_isSharedCheck_1790_ =
                            (!leanh::lean_is_exclusive(v___x_1776_)) as u8;
                        if v_isSharedCheck_1790_ == 0 {
                            v___x_1779_ = v___x_1776_;
                            v_isShared_1780_ = v_isSharedCheck_1790_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1777_);
                            leanh::lean_dec(v___x_1776_);
                            v___x_1779_ = leanh::lean_box(0);
                            v_isShared_1780_ = v_isSharedCheck_1790_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1772_);
                    leanh::lean_dec(v___x_1770_);
                    leanh::lean_dec(v___x_1749_);
                    v_a_1731_ = v___x_1761_;
                    state = 0;
                    continue;
                }
            }
            8 => {
                v___x_1764_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(v___y_1725_, v___y_1763_);
                leanh::lean_dec_ref(v___y_1763_);
                v___x_1765_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1765_, 0, v___x_1764_);
                v_a_1731_ = v___x_1761_;
                v_b_1732_ = v___x_1765_;
                state = 0;
                continue;
            }
            9 => {
                if leanh::lean_obj_tag(v_b_1732_) == 0 {
                    v___y_1763_ = v_val_1768_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v_b_1732_, 1);
                    if v___x_1726_ == 0 {
                        v___y_1763_ = v_val_1768_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_val_1768_);
                        leanh::lean_dec_ref(v___x_1761_);
                        leanh::lean_dec_ref(v_preferred_1730_);
                        leanh::lean_dec(v___x_1729_);
                        leanh::lean_dec_ref(v_range_1728_);
                        leanh::lean_dec(v___x_1727_);
                        v___x_1769_ = leanh::lean_box(0);
                        return v___x_1769_;
                    }
                }
            }
            10 => {
                if leanh::lean_obj_tag(v_val_1777_) == 0 {
                    v___x_1781_ = (leanh::lean_unbox(v_val_1773_) as u8);
                    leanh::lean_dec(v_val_1773_);
                    if v___x_1781_ == 0 {
                        leanh::lean_del_object(v___x_1779_);
                        leanh::lean_dec_ref_known(v___x_1775_, 2);
                        leanh::lean_dec(v___x_1770_);
                        v_a_1731_ = v___x_1761_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1783_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1784_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1784_, 0, v___x_1770_);
                        leanh::lean_ctor_set(v___x_1784_, 1, v___x_1783_);
                        v___x_1785_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1785_, 0, v___x_1784_);
                        leanh::lean_ctor_set(v___x_1785_, 1, v___x_1775_);
                        if v_isShared_1780_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_1779_, 0);
                            leanh::lean_ctor_set(v___x_1779_, 0, v___x_1785_);
                            v___x_1787_ = v___x_1779_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_1788_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
                            v___x_1787_ = v_reuseFailAlloc_1788_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1779_);
                    leanh::lean_dec_ref_known(v___x_1775_, 2);
                    leanh::lean_dec(v_val_1773_);
                    leanh::lean_dec(v___x_1770_);
                    v_val_1789_ = leanh::lean_ctor_get(v_val_1777_, 0);
                    leanh::lean_inc(v_val_1789_);
                    leanh::lean_dec_ref_known(v_val_1777_, 1);
                    v_val_1768_ = v_val_1789_;
                    state = 9;
                    continue;
                }
            }
            11 => {
                v_val_1768_ = v___x_1787_;
                state = 9;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(
    mut v_preferred_1806_: *mut leanh::LeanObject,
    mut v_range_1807_: *mut leanh::LeanObject,
    mut v_stack_1808_: *mut leanh::LeanObject,
    mut v_stx_1809_: *mut leanh::LeanObject,
    mut v_prev_x3f_1810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: u8 = 0;
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_childRes_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1822_: u8 = 0;
    let mut v_fst_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1827_: u8 = 0;
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_childRes_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1843_: u8 = 0;
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1847_: u8 = 0;
    let mut v_unused_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1853_: u8 = 0;
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bracket_1861_: u8 = 0;
    let mut v___y_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: u8 = 0;
    let mut v___y_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: u8 = 0;
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_stx_1809_);
                v___x_1811_ = l_Lean_Syntax_getKind(v_stx_1809_);
                v___x_1812_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3;
                v___x_1813_ = lean_name_eq(v___x_1811_, v___x_1812_);
                leanh::lean_dec(v___x_1811_);
                if v___x_1813_ == 0 {
                    v___x_1814_ = l_Lean_Syntax_getNumArgs(v_stx_1809_);
                    v___x_1815_ = leanh::lean_unsigned_to_nat(0);
                    v_childRes_1816_ = leanh::lean_box(0);
                    v___x_1817_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1817_, 0, v_childRes_1816_);
                    leanh::lean_ctor_set(v___x_1817_, 1, v_prev_x3f_1810_);
                    v___x_1818_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(v___x_1814_, v_stx_1809_, v_range_1807_, v_stack_1808_, v_preferred_1806_, v___x_1813_, v___x_1815_, v___x_1817_);
                    leanh::lean_dec(v___x_1814_);
                    if leanh::lean_obj_tag(v___x_1818_) == 0 {
                        return v_childRes_1816_;
                    } else {
                        v_val_1819_ = leanh::lean_ctor_get(v___x_1818_, 0);
                        v_isSharedCheck_1827_ =
                            (!leanh::lean_is_exclusive(v___x_1818_)) as u8;
                        if v_isSharedCheck_1827_ == 0 {
                            v___x_1821_ = v___x_1818_;
                            v_isShared_1822_ = v_isSharedCheck_1827_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1819_);
                            leanh::lean_dec(v___x_1818_);
                            v___x_1821_ = leanh::lean_box(0);
                            v_isShared_1822_ = v_isSharedCheck_1827_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_prev_x3f_1810_);
                    v___x_1828_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1858_ = l_Lean_Syntax_getArg(v_stx_1809_, v___x_1828_);
                    leanh::lean_inc(v___x_1858_);
                    v___x_1859_ = l_Lean_Syntax_getKind(v___x_1858_);
                    v___x_1860_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6;
                    v_bracket_1861_ = lean_name_eq(v___x_1859_, v___x_1860_);
                    leanh::lean_dec(v___x_1859_);
                    if v_bracket_1861_ == 0 {
                        v___y_1870_ = v___x_1828_;
                        state = 8;
                        continue;
                    } else {
                        v___x_1889_ = leanh::lean_unsigned_to_nat(1);
                        v___y_1870_ = v___x_1889_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1823_ = leanh::lean_ctor_get(v_val_1819_, 0);
                leanh::lean_inc(v_fst_1823_);
                leanh::lean_dec(v_val_1819_);
                if v_isShared_1822_ == 0 {
                    leanh::lean_ctor_set(v___x_1821_, 0, v_fst_1823_);
                    v___x_1825_ = v___x_1821_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1826_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_fst_1823_);
                    v___x_1825_ = v_reuseFailAlloc_1826_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1825_;
            }
            3 => {
                v_childRes_1833_ = leanh::lean_box(0);
                v___x_1834_ = l_Lean_Syntax_getNumArgs(v___y_1830_);
                v___x_1835_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__4;
                v___x_1836_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1836_, 0, v___x_1835_);
                leanh::lean_ctor_set(v___x_1836_, 1, v___x_1834_);
                v___x_1837_ = leanh::lean_unsigned_to_nat(1);
                v___x_1838_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1838_, 0, v___x_1828_);
                leanh::lean_ctor_set(v___x_1838_, 1, v___x_1837_);
                leanh::lean_ctor_set(v___x_1838_, 2, v___x_1836_);
                v___x_1839_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(v___y_1832_, v___x_1813_, v___y_1830_, v_range_1807_, v___y_1831_, v_preferred_1806_, v___x_1838_, v_childRes_1833_);
                if leanh::lean_obj_tag(v___x_1839_) == 0 {
                    leanh::lean_dec(v___y_1832_);
                    return v___x_1839_;
                } else {
                    v_val_1840_ = leanh::lean_ctor_get(v___x_1839_, 0);
                    leanh::lean_inc(v_val_1840_);
                    if leanh::lean_obj_tag(v_val_1840_) == 0 {
                        v_isSharedCheck_1847_ =
                            (!leanh::lean_is_exclusive(v___x_1839_)) as u8;
                        if v_isSharedCheck_1847_ == 0 {
                            v_unused_1848_ = leanh::lean_ctor_get(v___x_1839_, 0);
                            leanh::lean_dec(v_unused_1848_);
                            v___x_1842_ = v___x_1839_;
                            v_isShared_1843_ = v_isSharedCheck_1847_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1839_);
                            v___x_1842_ = leanh::lean_box(0);
                            v_isShared_1843_ = v_isSharedCheck_1847_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_val_1840_, 1);
                        leanh::lean_dec(v___y_1832_);
                        return v___x_1839_;
                    }
                }
            }
            4 => {
                if v_isShared_1843_ == 0 {
                    leanh::lean_ctor_set(v___x_1842_, 0, v___y_1832_);
                    v___x_1845_ = v___x_1842_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1846_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___y_1832_);
                    v___x_1845_ = v_reuseFailAlloc_1846_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1845_;
            }
            6 => {
                leanh::lean_inc(v___y_1850_);
                v___x_1854_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1854_, 0, v___y_1850_);
                leanh::lean_ctor_set(v___x_1854_, 1, v___x_1828_);
                leanh::lean_inc(v___y_1852_);
                v___x_1855_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1855_, 0, v___x_1854_);
                leanh::lean_ctor_set(v___x_1855_, 1, v___y_1852_);
                v___x_1856_ = leanh::lean_alloc_ctor(1, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_1856_, 0, v___y_1851_);
                leanh::lean_ctor_set(v___x_1856_, 1, v___x_1855_);
                leanh::lean_ctor_set_uint8(
                    v___x_1856_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___y_1853_,
                );
                v___x_1857_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1857_, 0, v___x_1856_);
                v___y_1830_ = v___y_1850_;
                v___y_1831_ = v___y_1852_;
                v___y_1832_ = v___x_1857_;
                state = 3;
                continue;
            }
            7 => {
                if v_bracket_1861_ == 0 {
                    leanh::lean_inc_ref(v_preferred_1806_);
                    v___x_1867_ = leanh::lean_apply_1(v_preferred_1806_, v___y_1864_);
                    v___x_1868_ = (leanh::lean_unbox(v___x_1867_) as u8);
                    v___y_1850_ = v___y_1863_;
                    v___y_1851_ = v___y_1866_;
                    v___y_1852_ = v___y_1865_;
                    v___y_1853_ = v___x_1868_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec(v___y_1864_);
                    v___y_1850_ = v___y_1863_;
                    v___y_1851_ = v___y_1866_;
                    v___y_1852_ = v___y_1865_;
                    v___y_1853_ = v___x_1813_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                leanh::lean_inc(v___y_1870_);
                leanh::lean_inc(v___x_1858_);
                v___x_1871_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1871_, 0, v___x_1858_);
                leanh::lean_ctor_set(v___x_1871_, 1, v___y_1870_);
                v___x_1872_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1872_, 0, v_stx_1809_);
                leanh::lean_ctor_set(v___x_1872_, 1, v___x_1828_);
                v___x_1873_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1873_, 0, v___x_1872_);
                leanh::lean_ctor_set(v___x_1873_, 1, v_stack_1808_);
                v___x_1874_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1874_, 0, v___x_1871_);
                leanh::lean_ctor_set(v___x_1874_, 1, v___x_1873_);
                v___x_1875_ = l_Lean_Syntax_getArg(v___x_1858_, v___y_1870_);
                leanh::lean_dec(v___y_1870_);
                leanh::lean_dec(v___x_1858_);
                v___x_1876_ = l_Lean_Syntax_getArg(v___x_1875_, v___x_1828_);
                v___x_1877_ = 0;
                v___x_1878_ = l_Lean_Syntax_getPos_x3f(v___x_1876_, v___x_1877_);
                leanh::lean_dec(v___x_1876_);
                if leanh::lean_obj_tag(v___x_1878_) == 0 {
                    v___x_1879_ = leanh::lean_box(0);
                    v___y_1830_ = v___x_1875_;
                    v___y_1831_ = v___x_1874_;
                    v___y_1832_ = v___x_1879_;
                    state = 3;
                    continue;
                } else {
                    v_val_1880_ = leanh::lean_ctor_get(v___x_1878_, 0);
                    leanh::lean_inc(v_val_1880_);
                    leanh::lean_dec_ref_known(v___x_1878_, 1);
                    v___x_1881_ = l_Lean_Syntax_getNumArgs(v___x_1875_);
                    v___x_1882_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0;
                    leanh::lean_inc_ref(v_range_1807_);
                    v___x_1883_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(v___x_1881_, v___x_1875_, v_range_1807_, v___x_1828_, v___x_1882_);
                    v_fst_1884_ = leanh::lean_ctor_get(v___x_1883_, 0);
                    leanh::lean_inc(v_fst_1884_);
                    leanh::lean_dec_ref(v___x_1883_);
                    if leanh::lean_obj_tag(v_fst_1884_) == 0 {
                        v___x_1885_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1886_ = lean_nat_add(v___x_1881_, v___x_1885_);
                        leanh::lean_dec(v___x_1881_);
                        v___x_1887_ = lean_nat_shiftr(v___x_1886_, v___x_1885_);
                        leanh::lean_dec(v___x_1886_);
                        v___y_1863_ = v___x_1875_;
                        v___y_1864_ = v_val_1880_;
                        v___y_1865_ = v___x_1874_;
                        v___y_1866_ = v___x_1887_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1881_);
                        v_val_1888_ = leanh::lean_ctor_get(v_fst_1884_, 0);
                        leanh::lean_inc(v_val_1888_);
                        leanh::lean_dec_ref_known(v_fst_1884_, 1);
                        v___y_1863_ = v___x_1875_;
                        v___y_1864_ = v_val_1880_;
                        v___y_1865_ = v___x_1874_;
                        v___y_1866_ = v_val_1888_;
                        state = 7;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(
    mut v_upperBound_1890_: *mut leanh::LeanObject,
    mut v_stx_1891_: *mut leanh::LeanObject,
    mut v_range_1892_: *mut leanh::LeanObject,
    mut v_stack_1893_: *mut leanh::LeanObject,
    mut v_preferred_1894_: *mut leanh::LeanObject,
    mut v___x_1895_: u8,
    mut v_a_1896_: *mut leanh::LeanObject,
    mut v_b_1897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1904_: u8 = 0;
    let mut v_a_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1913_: u8 = 0;
    let mut v___x_1914_: u8 = 0;
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1920_: u8 = 0;
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1938_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1914_ = lean_nat_dec_lt(v_a_1896_, v_upperBound_1890_);
                if v___x_1914_ == 0 {
                    leanh::lean_dec(v_a_1896_);
                    leanh::lean_dec_ref(v_preferred_1894_);
                    leanh::lean_dec(v_stack_1893_);
                    leanh::lean_dec_ref(v_range_1892_);
                    leanh::lean_dec(v_stx_1891_);
                    v___x_1915_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1915_, 0, v_b_1897_);
                    return v___x_1915_;
                } else {
                    v_fst_1916_ = leanh::lean_ctor_get(v_b_1897_, 0);
                    v_snd_1917_ = leanh::lean_ctor_get(v_b_1897_, 1);
                    v_isSharedCheck_1938_ = (!leanh::lean_is_exclusive(v_b_1897_)) as u8;
                    if v_isSharedCheck_1938_ == 0 {
                        v___x_1919_ = v_b_1897_;
                        v_isShared_1920_ = v_isSharedCheck_1938_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1917_);
                        leanh::lean_inc(v_fst_1916_);
                        leanh::lean_dec(v_b_1897_);
                        v___x_1919_ = leanh::lean_box(0);
                        v_isShared_1920_ = v_isSharedCheck_1938_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_1899_) == 0 {
                    leanh::lean_dec(v_a_1896_);
                    leanh::lean_dec_ref(v_preferred_1894_);
                    leanh::lean_dec(v_stack_1893_);
                    leanh::lean_dec_ref(v_range_1892_);
                    leanh::lean_dec(v_stx_1891_);
                    v___x_1900_ = leanh::lean_box(0);
                    return v___x_1900_;
                } else {
                    v_val_1901_ = leanh::lean_ctor_get(v___y_1899_, 0);
                    v_isSharedCheck_1913_ = (!leanh::lean_is_exclusive(v___y_1899_)) as u8;
                    if v_isSharedCheck_1913_ == 0 {
                        v___x_1903_ = v___y_1899_;
                        v_isShared_1904_ = v_isSharedCheck_1913_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1901_);
                        leanh::lean_dec(v___y_1899_);
                        v___x_1903_ = leanh::lean_box(0);
                        v_isShared_1904_ = v_isSharedCheck_1913_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_val_1901_) == 0 {
                    leanh::lean_dec(v_a_1896_);
                    leanh::lean_dec_ref(v_preferred_1894_);
                    leanh::lean_dec(v_stack_1893_);
                    leanh::lean_dec_ref(v_range_1892_);
                    leanh::lean_dec(v_stx_1891_);
                    v_a_1905_ = leanh::lean_ctor_get(v_val_1901_, 0);
                    leanh::lean_inc(v_a_1905_);
                    leanh::lean_dec_ref_known(v_val_1901_, 1);
                    if v_isShared_1904_ == 0 {
                        leanh::lean_ctor_set(v___x_1903_, 0, v_a_1905_);
                        v___x_1907_ = v___x_1903_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1908_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1905_);
                        v___x_1907_ = v_reuseFailAlloc_1908_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1903_);
                    v_a_1909_ = leanh::lean_ctor_get(v_val_1901_, 0);
                    leanh::lean_inc(v_a_1909_);
                    leanh::lean_dec_ref_known(v_val_1901_, 1);
                    v___x_1910_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1911_ = lean_nat_add(v_a_1896_, v___x_1910_);
                    leanh::lean_dec(v_a_1896_);
                    v_a_1896_ = v___x_1911_;
                    v_b_1897_ = v_a_1909_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_1907_;
            }
            4 => {
                v___x_1921_ = l_Lean_Syntax_getArg(v_stx_1891_, v_a_1896_);
                leanh::lean_inc(v_snd_1917_);
                v___x_1922_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(v_range_1892_, v___x_1921_, v_snd_1917_);
                if leanh::lean_obj_tag(v___x_1922_) == 1 {
                    leanh::lean_dec_ref_known(v___x_1922_, 1);
                    leanh::lean_inc(v_a_1896_);
                    leanh::lean_inc(v_stx_1891_);
                    if v_isShared_1920_ == 0 {
                        leanh::lean_ctor_set(v___x_1919_, 1, v_a_1896_);
                        leanh::lean_ctor_set(v___x_1919_, 0, v_stx_1891_);
                        v___x_1924_ = v___x_1919_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1935_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_stx_1891_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_a_1896_);
                        v___x_1924_ = v_reuseFailAlloc_1935_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1922_);
                    leanh::lean_dec(v___x_1921_);
                    leanh::lean_del_object(v___x_1919_);
                    v___x_1936_ = leanh::lean_box(0);
                    v___x_1937_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_1891_, v_a_1896_, v___x_1914_, v_snd_1917_, v___x_1936_, v_fst_1916_);
                    v___y_1899_ = v___x_1937_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc(v_stack_1893_);
                v___x_1925_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1925_, 0, v___x_1924_);
                leanh::lean_ctor_set(v___x_1925_, 1, v_stack_1893_);
                leanh::lean_inc(v_snd_1917_);
                leanh::lean_inc_ref(v_range_1892_);
                leanh::lean_inc_ref(v_preferred_1894_);
                v___x_1926_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(v_preferred_1894_, v_range_1892_, v___x_1925_, v___x_1921_, v_snd_1917_);
                if leanh::lean_obj_tag(v___x_1926_) == 0 {
                    leanh::lean_dec(v_snd_1917_);
                    leanh::lean_dec(v_fst_1916_);
                    leanh::lean_dec(v_a_1896_);
                    leanh::lean_dec_ref(v_preferred_1894_);
                    leanh::lean_dec(v_stack_1893_);
                    leanh::lean_dec_ref(v_range_1892_);
                    leanh::lean_dec(v_stx_1891_);
                    v___x_1927_ = leanh::lean_box(0);
                    return v___x_1927_;
                } else {
                    v_val_1928_ = leanh::lean_ctor_get(v___x_1926_, 0);
                    leanh::lean_inc(v_val_1928_);
                    leanh::lean_dec_ref_known(v___x_1926_, 1);
                    if leanh::lean_obj_tag(v_val_1928_) == 1 {
                        if leanh::lean_obj_tag(v_fst_1916_) == 0 {
                            if v___x_1895_ == 0 {
                                v___x_1929_ = leanh::lean_box(0);
                                v___x_1930_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_1891_, v_a_1896_, v___x_1914_, v_snd_1917_, v___x_1929_, v_val_1928_);
                                v___y_1899_ = v___x_1930_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref_known(v_val_1928_, 1);
                                leanh::lean_dec(v_snd_1917_);
                                leanh::lean_dec(v_a_1896_);
                                leanh::lean_dec_ref(v_preferred_1894_);
                                leanh::lean_dec(v_stack_1893_);
                                leanh::lean_dec_ref(v_range_1892_);
                                leanh::lean_dec(v_stx_1891_);
                                v___x_1931_ = leanh::lean_box(0);
                                return v___x_1931_;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_fst_1916_, 1);
                            leanh::lean_dec_ref_known(v_val_1928_, 1);
                            leanh::lean_dec(v_snd_1917_);
                            leanh::lean_dec(v_a_1896_);
                            leanh::lean_dec_ref(v_preferred_1894_);
                            leanh::lean_dec(v_stack_1893_);
                            leanh::lean_dec_ref(v_range_1892_);
                            leanh::lean_dec(v_stx_1891_);
                            v___x_1932_ = leanh::lean_box(0);
                            return v___x_1932_;
                        }
                    } else {
                        leanh::lean_dec(v_val_1928_);
                        v___x_1933_ = leanh::lean_box(0);
                        v___x_1934_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_1891_, v_a_1896_, v___x_1914_, v_snd_1917_, v___x_1933_, v_fst_1916_);
                        v___y_1899_ = v___x_1934_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___boxed(
    mut v_upperBound_1939_: *mut leanh::LeanObject,
    mut v_stx_1940_: *mut leanh::LeanObject,
    mut v_range_1941_: *mut leanh::LeanObject,
    mut v_stack_1942_: *mut leanh::LeanObject,
    mut v_preferred_1943_: *mut leanh::LeanObject,
    mut v___x_1944_: *mut leanh::LeanObject,
    mut v_a_1945_: *mut leanh::LeanObject,
    mut v_b_1946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4665__boxed_1947_: u8 = 0;
    let mut v_res_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4665__boxed_1947_ = (leanh::lean_unbox(v___x_1944_) as u8);
    v_res_1948_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(v_upperBound_1939_, v_stx_1940_, v_range_1941_, v_stack_1942_, v_preferred_1943_, v___x_4665__boxed_1947_, v_a_1945_, v_b_1946_);
    leanh::lean_dec(v_upperBound_1939_);
    return v_res_1948_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg___boxed(
    mut v___y_1949_: *mut leanh::LeanObject,
    mut v___x_1950_: *mut leanh::LeanObject,
    mut v___x_1951_: *mut leanh::LeanObject,
    mut v_range_1952_: *mut leanh::LeanObject,
    mut v___x_1953_: *mut leanh::LeanObject,
    mut v_preferred_1954_: *mut leanh::LeanObject,
    mut v_a_1955_: *mut leanh::LeanObject,
    mut v_b_1956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4696__boxed_1957_: u8 = 0;
    let mut v_res_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4696__boxed_1957_ = (leanh::lean_unbox(v___x_1950_) as u8);
    v_res_1958_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(v___y_1949_, v___x_4696__boxed_1957_, v___x_1951_, v_range_1952_, v___x_1953_, v_preferred_1954_, v_a_1955_, v_b_1956_);
    leanh::lean_dec(v___y_1949_);
    return v_res_1958_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0(
    mut v_upperBound_1959_: *mut leanh::LeanObject,
    mut v_stx_1960_: *mut leanh::LeanObject,
    mut v_range_1961_: *mut leanh::LeanObject,
    mut v_stack_1962_: *mut leanh::LeanObject,
    mut v_preferred_1963_: *mut leanh::LeanObject,
    mut v___x_1964_: u8,
    mut v_inst_1965_: *mut leanh::LeanObject,
    mut v_R_1966_: *mut leanh::LeanObject,
    mut v_a_1967_: *mut leanh::LeanObject,
    mut v_b_1968_: *mut leanh::LeanObject,
    mut v_c_1969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1970_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(v_upperBound_1959_, v_stx_1960_, v_range_1961_, v_stack_1962_, v_preferred_1963_, v___x_1964_, v_a_1967_, v_b_1968_);
    return v___x_1970_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___boxed(
    mut v_upperBound_1971_: *mut leanh::LeanObject,
    mut v_stx_1972_: *mut leanh::LeanObject,
    mut v_range_1973_: *mut leanh::LeanObject,
    mut v_stack_1974_: *mut leanh::LeanObject,
    mut v_preferred_1975_: *mut leanh::LeanObject,
    mut v___x_1976_: *mut leanh::LeanObject,
    mut v_inst_1977_: *mut leanh::LeanObject,
    mut v_R_1978_: *mut leanh::LeanObject,
    mut v_a_1979_: *mut leanh::LeanObject,
    mut v_b_1980_: *mut leanh::LeanObject,
    mut v_c_1981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5068__boxed_1982_: u8 = 0;
    let mut v_res_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5068__boxed_1982_ = (leanh::lean_unbox(v___x_1976_) as u8);
    v_res_1983_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0(v_upperBound_1971_, v_stx_1972_, v_range_1973_, v_stack_1974_, v_preferred_1975_, v___x_5068__boxed_1982_, v_inst_1977_, v_R_1978_, v_a_1979_, v_b_1980_, v_c_1981_);
    leanh::lean_dec(v_upperBound_1971_);
    return v_res_1983_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1(
    mut v___y_1984_: *mut leanh::LeanObject,
    mut v___x_1985_: u8,
    mut v___x_1986_: *mut leanh::LeanObject,
    mut v_range_1987_: *mut leanh::LeanObject,
    mut v___x_1988_: *mut leanh::LeanObject,
    mut v_preferred_1989_: *mut leanh::LeanObject,
    mut v_inst_1990_: *mut leanh::LeanObject,
    mut v_R_1991_: *mut leanh::LeanObject,
    mut v_a_1992_: *mut leanh::LeanObject,
    mut v_b_1993_: *mut leanh::LeanObject,
    mut v_c_1994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1995_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(v___y_1984_, v___x_1985_, v___x_1986_, v_range_1987_, v___x_1988_, v_preferred_1989_, v_a_1992_, v_b_1993_);
    return v___x_1995_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___boxed(
    mut v___y_1996_: *mut leanh::LeanObject,
    mut v___x_1997_: *mut leanh::LeanObject,
    mut v___x_1998_: *mut leanh::LeanObject,
    mut v_range_1999_: *mut leanh::LeanObject,
    mut v___x_2000_: *mut leanh::LeanObject,
    mut v_preferred_2001_: *mut leanh::LeanObject,
    mut v_inst_2002_: *mut leanh::LeanObject,
    mut v_R_2003_: *mut leanh::LeanObject,
    mut v_a_2004_: *mut leanh::LeanObject,
    mut v_b_2005_: *mut leanh::LeanObject,
    mut v_c_2006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5079__boxed_2007_: u8 = 0;
    let mut v_res_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5079__boxed_2007_ = (leanh::lean_unbox(v___x_1997_) as u8);
    v_res_2008_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1(v___y_1996_, v___x_5079__boxed_2007_, v___x_1998_, v_range_1999_, v___x_2000_, v_preferred_2001_, v_inst_2002_, v_R_2003_, v_a_2004_, v_b_2005_, v_c_2006_);
    leanh::lean_dec(v___y_1996_);
    return v_res_2008_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2(
    mut v_upperBound_2009_: *mut leanh::LeanObject,
    mut v___x_2010_: *mut leanh::LeanObject,
    mut v_range_2011_: *mut leanh::LeanObject,
    mut v_inst_2012_: *mut leanh::LeanObject,
    mut v_R_2013_: *mut leanh::LeanObject,
    mut v_a_2014_: *mut leanh::LeanObject,
    mut v_b_2015_: *mut leanh::LeanObject,
    mut v_c_2016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2017_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(v_upperBound_2009_, v___x_2010_, v_range_2011_, v_a_2014_, v_b_2015_);
    return v___x_2017_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___boxed(
    mut v_upperBound_2018_: *mut leanh::LeanObject,
    mut v___x_2019_: *mut leanh::LeanObject,
    mut v_range_2020_: *mut leanh::LeanObject,
    mut v_inst_2021_: *mut leanh::LeanObject,
    mut v_R_2022_: *mut leanh::LeanObject,
    mut v_a_2023_: *mut leanh::LeanObject,
    mut v_b_2024_: *mut leanh::LeanObject,
    mut v_c_2025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2026_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2(v_upperBound_2018_, v___x_2019_, v_range_2020_, v_inst_2021_, v_R_2022_, v_a_2023_, v_b_2024_, v_c_2025_);
    leanh::lean_dec_ref(v_b_2024_);
    leanh::lean_dec(v___x_2019_);
    leanh::lean_dec(v_upperBound_2018_);
    return v_res_2026_;
}
pub unsafe fn l_Lean_CodeAction_findTactic_x3f(
    mut v_preferred_2027_: *mut leanh::LeanObject,
    mut v_range_2028_: *mut leanh::LeanObject,
    mut v_root_2029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2030_ = leanh::lean_box(0);
    v___x_2031_ =
        l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(
            v_range_2028_,
            v_root_2029_,
            v___x_2030_,
        );
    if leanh::lean_obj_tag(v___x_2031_) == 0 {
        leanh::lean_dec(v_root_2029_);
        leanh::lean_dec_ref(v_range_2028_);
        leanh::lean_dec_ref(v_preferred_2027_);
        return v___x_2030_;
    } else {
        let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_2031_, 1);
        v___x_2032_ = leanh::lean_box(0);
        v___x_2033_ =
            l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(
                v_preferred_2027_,
                v_range_2028_,
                v___x_2032_,
                v_root_2029_,
                v___x_2030_,
            );
        if leanh::lean_obj_tag(v___x_2033_) == 0 {
            return v___x_2030_;
        } else {
            let mut v_val_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_2034_ = leanh::lean_ctor_get(v___x_2033_, 0);
            leanh::lean_inc(v_val_2034_);
            leanh::lean_dec_ref_known(v___x_2033_, 1);
            return v_val_2034_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(
    mut v_ctx_x3f_2047_: *mut leanh::LeanObject,
    mut v_i_2048_: *mut leanh::LeanObject,
    mut v_kind_2049_: *mut leanh::LeanObject,
    mut v_tgtRange_2050_: *mut leanh::LeanObject,
    mut v_f_2051_: *mut leanh::LeanObject,
    mut v_canonicalOnly_2052_: u8,
    mut v_as_2053_: *mut leanh::LeanObject,
    mut v_sz_2054_: usize,
    mut v_i_2055_: usize,
    mut v_b_2056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2057_: u8 = 0;
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2062_: u8 = 0;
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2071_: u8 = 0;
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2077_: u8 = 0;
    let mut v_unused_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: usize = 0;
    let mut v___x_2082_: usize = 0;
    let mut v_isSharedCheck_2084_: u8 = 0;
    let mut v_unused_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2057_ = lean_usize_dec_lt(v_i_2055_, v_sz_2054_);
                if v___x_2057_ == 0 {
                    leanh::lean_dec_ref(v_f_2051_);
                    leanh::lean_dec(v_ctx_x3f_2047_);
                    v___x_2058_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2058_, 0, v_b_2056_);
                    return v___x_2058_;
                } else {
                    v_snd_2059_ = leanh::lean_ctor_get(v_b_2056_, 1);
                    v_isSharedCheck_2084_ = (!leanh::lean_is_exclusive(v_b_2056_)) as u8;
                    if v_isSharedCheck_2084_ == 0 {
                        v_unused_2085_ = leanh::lean_ctor_get(v_b_2056_, 0);
                        leanh::lean_dec(v_unused_2085_);
                        v___x_2061_ = v_b_2056_;
                        v_isShared_2062_ = v_isSharedCheck_2084_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2059_);
                        leanh::lean_dec(v_b_2056_);
                        v___x_2061_ = leanh::lean_box(0);
                        v_isShared_2062_ = v_isSharedCheck_2084_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2063_ = leanh::lean_box(0);
                v_a_2064_ = lean_array_uget_borrowed(v_as_2053_, v_i_2055_);
                leanh::lean_inc(v_ctx_x3f_2047_);
                v___x_2065_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_2047_, v_i_2048_);
                leanh::lean_inc_ref(v_f_2051_);
                leanh::lean_inc(v_a_2064_);
                v___x_2066_ = l_Lean_CodeAction_findInfoTree_x3f(
                    v_kind_2049_,
                    v_tgtRange_2050_,
                    v___x_2065_,
                    v_a_2064_,
                    v_f_2051_,
                    v_canonicalOnly_2052_,
                );
                if leanh::lean_obj_tag(v___x_2066_) == 1 {
                    leanh::lean_dec_ref(v_f_2051_);
                    leanh::lean_dec(v_ctx_x3f_2047_);
                    leanh::lean_inc_ref(v___x_2066_);
                    if v_isShared_2062_ == 0 {
                        leanh::lean_ctor_set(v___x_2061_, 1, v___x_2063_);
                        leanh::lean_ctor_set(v___x_2061_, 0, v___x_2066_);
                        v___x_2068_ = v___x_2061_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2079_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2066_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 1, v___x_2063_);
                        v___x_2068_ = v_reuseFailAlloc_2079_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2066_);
                    leanh::lean_del_object(v___x_2061_);
                    leanh::lean_dec(v_snd_2059_);
                    v___x_2080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__1;
                    v___x_2081_ = 1usize;
                    v___x_2082_ = lean_usize_add(v_i_2055_, v___x_2081_);
                    v_i_2055_ = v___x_2082_;
                    v_b_2056_ = v___x_2080_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_isSharedCheck_2077_ = (!leanh::lean_is_exclusive(v___x_2066_)) as u8;
                if v_isSharedCheck_2077_ == 0 {
                    v_unused_2078_ = leanh::lean_ctor_get(v___x_2066_, 0);
                    leanh::lean_dec(v_unused_2078_);
                    v___x_2070_ = v___x_2066_;
                    v_isShared_2071_ = v_isSharedCheck_2077_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___x_2066_);
                    v___x_2070_ = leanh::lean_box(0);
                    v_isShared_2071_ = v_isSharedCheck_2077_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2071_ == 0 {
                    leanh::lean_ctor_set(v___x_2070_, 0, v___x_2068_);
                    v___x_2073_ = v___x_2070_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2076_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2068_);
                    v___x_2073_ = v_reuseFailAlloc_2076_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2074_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2074_, 0, v___x_2073_);
                leanh::lean_ctor_set(v___x_2074_, 1, v_snd_2059_);
                v___x_2075_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2075_, 0, v___x_2074_);
                return v___x_2075_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(
    mut v_ctx_x3f_2086_: *mut leanh::LeanObject,
    mut v_i_2087_: *mut leanh::LeanObject,
    mut v_kind_2088_: *mut leanh::LeanObject,
    mut v_tgtRange_2089_: *mut leanh::LeanObject,
    mut v_f_2090_: *mut leanh::LeanObject,
    mut v_canonicalOnly_2091_: u8,
    mut v_as_2092_: *mut leanh::LeanObject,
    mut v_sz_2093_: usize,
    mut v_i_2094_: usize,
    mut v_b_2095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2096_: u8 = 0;
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2101_: u8 = 0;
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2110_: u8 = 0;
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2116_: u8 = 0;
    let mut v_unused_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: usize = 0;
    let mut v___x_2121_: usize = 0;
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2123_: u8 = 0;
    let mut v_unused_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2096_ = lean_usize_dec_lt(v_i_2094_, v_sz_2093_);
                if v___x_2096_ == 0 {
                    leanh::lean_dec_ref(v_f_2090_);
                    leanh::lean_dec(v_ctx_x3f_2086_);
                    v___x_2097_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2097_, 0, v_b_2095_);
                    return v___x_2097_;
                } else {
                    v_snd_2098_ = leanh::lean_ctor_get(v_b_2095_, 1);
                    v_isSharedCheck_2123_ = (!leanh::lean_is_exclusive(v_b_2095_)) as u8;
                    if v_isSharedCheck_2123_ == 0 {
                        v_unused_2124_ = leanh::lean_ctor_get(v_b_2095_, 0);
                        leanh::lean_dec(v_unused_2124_);
                        v___x_2100_ = v_b_2095_;
                        v_isShared_2101_ = v_isSharedCheck_2123_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2098_);
                        leanh::lean_dec(v_b_2095_);
                        v___x_2100_ = leanh::lean_box(0);
                        v_isShared_2101_ = v_isSharedCheck_2123_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2102_ = leanh::lean_box(0);
                v_a_2103_ = lean_array_uget_borrowed(v_as_2092_, v_i_2094_);
                leanh::lean_inc(v_ctx_x3f_2086_);
                v___x_2104_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_2086_, v_i_2087_);
                leanh::lean_inc_ref(v_f_2090_);
                leanh::lean_inc(v_a_2103_);
                v___x_2105_ = l_Lean_CodeAction_findInfoTree_x3f(
                    v_kind_2088_,
                    v_tgtRange_2089_,
                    v___x_2104_,
                    v_a_2103_,
                    v_f_2090_,
                    v_canonicalOnly_2091_,
                );
                if leanh::lean_obj_tag(v___x_2105_) == 1 {
                    leanh::lean_dec_ref(v_f_2090_);
                    leanh::lean_dec(v_ctx_x3f_2086_);
                    leanh::lean_inc_ref(v___x_2105_);
                    if v_isShared_2101_ == 0 {
                        leanh::lean_ctor_set(v___x_2100_, 1, v___x_2102_);
                        leanh::lean_ctor_set(v___x_2100_, 0, v___x_2105_);
                        v___x_2107_ = v___x_2100_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2118_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2105_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2118_, 1, v___x_2102_);
                        v___x_2107_ = v_reuseFailAlloc_2118_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2105_);
                    leanh::lean_del_object(v___x_2100_);
                    leanh::lean_dec(v_snd_2098_);
                    v___x_2119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__1;
                    v___x_2120_ = 1usize;
                    v___x_2121_ = lean_usize_add(v_i_2094_, v___x_2120_);
                    v___x_2122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(v_ctx_x3f_2086_, v_i_2087_, v_kind_2088_, v_tgtRange_2089_, v_f_2090_, v_canonicalOnly_2091_, v_as_2092_, v_sz_2093_, v___x_2121_, v___x_2119_);
                    return v___x_2122_;
                }
            }
            2 => {
                v_isSharedCheck_2116_ = (!leanh::lean_is_exclusive(v___x_2105_)) as u8;
                if v_isSharedCheck_2116_ == 0 {
                    v_unused_2117_ = leanh::lean_ctor_get(v___x_2105_, 0);
                    leanh::lean_dec(v_unused_2117_);
                    v___x_2109_ = v___x_2105_;
                    v_isShared_2110_ = v_isSharedCheck_2116_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___x_2105_);
                    v___x_2109_ = leanh::lean_box(0);
                    v_isShared_2110_ = v_isSharedCheck_2116_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2110_ == 0 {
                    leanh::lean_ctor_set(v___x_2109_, 0, v___x_2107_);
                    v___x_2112_ = v___x_2109_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2115_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2107_);
                    v___x_2112_ = v_reuseFailAlloc_2115_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2113_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2113_, 0, v___x_2112_);
                leanh::lean_ctor_set(v___x_2113_, 1, v_snd_2098_);
                v___x_2114_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2114_, 0, v___x_2113_);
                return v___x_2114_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(
    mut v_ctx_x3f_2125_: *mut leanh::LeanObject,
    mut v_i_2126_: *mut leanh::LeanObject,
    mut v_kind_2127_: *mut leanh::LeanObject,
    mut v_tgtRange_2128_: *mut leanh::LeanObject,
    mut v_f_2129_: *mut leanh::LeanObject,
    mut v_canonicalOnly_2130_: u8,
    mut v_t_2131_: *mut leanh::LeanObject,
    mut v_init_2132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2140_: u8 = 0;
    let mut v_a_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2148_: usize = 0;
    let mut v___x_2149_: usize = 0;
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2154_: u8 = 0;
    let mut v_fst_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2160_: u8 = 0;
    let mut v_isSharedCheck_2161_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_2133_ = leanh::lean_ctor_get(v_t_2131_, 0);
                v_tail_2134_ = leanh::lean_ctor_get(v_t_2131_, 1);
                leanh::lean_inc_ref(v_f_2129_);
                leanh::lean_inc(v_ctx_x3f_2125_);
                leanh::lean_inc_ref(v_init_2132_);
                v___x_2135_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(v_init_2132_, v_ctx_x3f_2125_, v_i_2126_, v_kind_2127_, v_tgtRange_2128_, v_f_2129_, v_canonicalOnly_2130_, v_root_2133_, v_init_2132_);
                leanh::lean_dec_ref(v_init_2132_);
                if leanh::lean_obj_tag(v___x_2135_) == 0 {
                    leanh::lean_dec_ref(v_f_2129_);
                    leanh::lean_dec(v_ctx_x3f_2125_);
                    v___x_2136_ = leanh::lean_box(0);
                    return v___x_2136_;
                } else {
                    v_val_2137_ = leanh::lean_ctor_get(v___x_2135_, 0);
                    v_isSharedCheck_2161_ = (!leanh::lean_is_exclusive(v___x_2135_)) as u8;
                    if v_isSharedCheck_2161_ == 0 {
                        v___x_2139_ = v___x_2135_;
                        v_isShared_2140_ = v_isSharedCheck_2161_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2137_);
                        leanh::lean_dec(v___x_2135_);
                        v___x_2139_ = leanh::lean_box(0);
                        v_isShared_2140_ = v_isSharedCheck_2161_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_val_2137_) == 0 {
                    leanh::lean_dec_ref(v_f_2129_);
                    leanh::lean_dec(v_ctx_x3f_2125_);
                    v_a_2141_ = leanh::lean_ctor_get(v_val_2137_, 0);
                    leanh::lean_inc(v_a_2141_);
                    leanh::lean_dec_ref_known(v_val_2137_, 1);
                    if v_isShared_2140_ == 0 {
                        leanh::lean_ctor_set(v___x_2139_, 0, v_a_2141_);
                        v___x_2143_ = v___x_2139_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2144_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2141_);
                        v___x_2143_ = v_reuseFailAlloc_2144_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2139_);
                    v_a_2145_ = leanh::lean_ctor_get(v_val_2137_, 0);
                    leanh::lean_inc(v_a_2145_);
                    leanh::lean_dec_ref_known(v_val_2137_, 1);
                    v___x_2146_ = leanh::lean_box(0);
                    v___x_2147_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2147_, 0, v___x_2146_);
                    leanh::lean_ctor_set(v___x_2147_, 1, v_a_2145_);
                    v_sz_2148_ = lean_array_size(v_tail_2134_);
                    v___x_2149_ = 0usize;
                    v___x_2150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(v_ctx_x3f_2125_, v_i_2126_, v_kind_2127_, v_tgtRange_2128_, v_f_2129_, v_canonicalOnly_2130_, v_tail_2134_, v_sz_2148_, v___x_2149_, v___x_2147_);
                    if leanh::lean_obj_tag(v___x_2150_) == 0 {
                        return v___x_2146_;
                    } else {
                        v_val_2151_ = leanh::lean_ctor_get(v___x_2150_, 0);
                        v_isSharedCheck_2160_ =
                            (!leanh::lean_is_exclusive(v___x_2150_)) as u8;
                        if v_isSharedCheck_2160_ == 0 {
                            v___x_2153_ = v___x_2150_;
                            v_isShared_2154_ = v_isSharedCheck_2160_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2151_);
                            leanh::lean_dec(v___x_2150_);
                            v___x_2153_ = leanh::lean_box(0);
                            v_isShared_2154_ = v_isSharedCheck_2160_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2143_;
            }
            3 => {
                v_fst_2155_ = leanh::lean_ctor_get(v_val_2151_, 0);
                if leanh::lean_obj_tag(v_fst_2155_) == 0 {
                    v_snd_2156_ = leanh::lean_ctor_get(v_val_2151_, 1);
                    leanh::lean_inc(v_snd_2156_);
                    leanh::lean_dec(v_val_2151_);
                    if v_isShared_2154_ == 0 {
                        leanh::lean_ctor_set(v___x_2153_, 0, v_snd_2156_);
                        v___x_2158_ = v___x_2153_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2159_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_snd_2156_);
                        v___x_2158_ = v_reuseFailAlloc_2159_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_2155_);
                    leanh::lean_del_object(v___x_2153_);
                    leanh::lean_dec(v_val_2151_);
                    return v_fst_2155_;
                }
            }
            4 => {
                return v___x_2158_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_CodeAction_findInfoTree_x3f(
    mut v_kind_2162_: *mut leanh::LeanObject,
    mut v_tgtRange_2163_: *mut leanh::LeanObject,
    mut v_ctx_x3f_2164_: *mut leanh::LeanObject,
    mut v_t_2165_: *mut leanh::LeanObject,
    mut v_f_2166_: *mut leanh::LeanObject,
    mut v_canonicalOnly_2167_: u8,
) -> *mut leanh::LeanObject {
    let mut v_i_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2182_: u8 = 0;
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: u8 = 0;
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2187_: u8 = 0;
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2192_: u8 = 0;
    let mut v_unused_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: u8 = 0;
    let mut v___x_2199_: u8 = 0;
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_t_2165_) {
                0 => {
                    v_i_2168_ = leanh::lean_ctor_get(v_t_2165_, 0);
                    leanh::lean_inc_ref(v_i_2168_);
                    v_t_2169_ = leanh::lean_ctor_get(v_t_2165_, 1);
                    leanh::lean_inc_ref(v_t_2169_);
                    leanh::lean_dec_ref_known(v_t_2165_, 2);
                    v___x_2170_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(
                        v_i_2168_,
                        v_ctx_x3f_2164_,
                    );
                    v_ctx_x3f_2164_ = v___x_2170_;
                    v_t_2165_ = v_t_2169_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_i_2172_ = leanh::lean_ctor_get(v_t_2165_, 0);
                    v_children_2173_ = leanh::lean_ctor_get(v_t_2165_, 1);
                    if leanh::lean_obj_tag(v_ctx_x3f_2164_) == 1 {
                        v_val_2180_ = leanh::lean_ctor_get(v_ctx_x3f_2164_, 0);
                        v___x_2194_ = l_Lean_Elab_Info_stx(v_i_2172_);
                        v___x_2195_ =
                            l_Lean_Syntax_getRange_x3f(v___x_2194_, v_canonicalOnly_2167_);
                        if leanh::lean_obj_tag(v___x_2195_) == 1 {
                            v_val_2196_ = leanh::lean_ctor_get(v___x_2195_, 0);
                            leanh::lean_inc(v_val_2196_);
                            leanh::lean_dec_ref_known(v___x_2195_, 1);
                            v___x_2197_ = l_Lean_Syntax_getKind(v___x_2194_);
                            v___x_2198_ = lean_name_eq(v___x_2197_, v_kind_2162_);
                            leanh::lean_dec(v___x_2197_);
                            if v___x_2198_ == 0 {
                                leanh::lean_dec(v_val_2196_);
                                v___y_2182_ = v___x_2198_;
                                state = 2;
                                continue;
                            } else {
                                v___x_2199_ =
                                    l_Lean_Syntax_instBEqRange_beq(v_val_2196_, v_tgtRange_2163_);
                                leanh::lean_dec(v_val_2196_);
                                v___y_2182_ = v___x_2199_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_inc_ref(v_children_2173_);
                            leanh::lean_inc_ref(v_i_2172_);
                            leanh::lean_dec(v___x_2195_);
                            leanh::lean_dec(v___x_2194_);
                            leanh::lean_dec_ref_known(v_t_2165_, 2);
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_inc_ref(v_children_2173_);
                        leanh::lean_inc_ref(v_i_2172_);
                        leanh::lean_dec_ref_known(v_t_2165_, 2);
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec_ref(v_f_2166_);
                    leanh::lean_dec_ref(v_t_2165_);
                    leanh::lean_dec(v_ctx_x3f_2164_);
                    v___x_2200_ = leanh::lean_box(0);
                    return v___x_2200_;
                }
            },
            1 => {
                v___x_2175_ = leanh::lean_box(0);
                v___x_2176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0;
                v___x_2177_ =
                    l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(
                        v_ctx_x3f_2164_,
                        v_i_2172_,
                        v_kind_2162_,
                        v_tgtRange_2163_,
                        v_f_2166_,
                        v_canonicalOnly_2167_,
                        v_children_2173_,
                        v___x_2176_,
                    );
                leanh::lean_dec_ref(v_children_2173_);
                leanh::lean_dec_ref(v_i_2172_);
                if leanh::lean_obj_tag(v___x_2177_) == 0 {
                    return v___x_2175_;
                } else {
                    v_val_2178_ = leanh::lean_ctor_get(v___x_2177_, 0);
                    leanh::lean_inc(v_val_2178_);
                    leanh::lean_dec_ref_known(v___x_2177_, 1);
                    v_fst_2179_ = leanh::lean_ctor_get(v_val_2178_, 0);
                    leanh::lean_inc(v_fst_2179_);
                    leanh::lean_dec(v_val_2178_);
                    if leanh::lean_obj_tag(v_fst_2179_) == 0 {
                        return v___x_2175_;
                    } else {
                        return v_fst_2179_;
                    }
                }
            }
            2 => {
                if v___y_2182_ == 0 {
                    leanh::lean_inc_ref(v_children_2173_);
                    leanh::lean_inc_ref(v_i_2172_);
                    leanh::lean_dec_ref_known(v_t_2165_, 2);
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_f_2166_);
                    leanh::lean_inc_ref(v_i_2172_);
                    leanh::lean_inc(v_val_2180_);
                    v___x_2183_ = leanh::lean_apply_2(v_f_2166_, v_val_2180_, v_i_2172_);
                    v___x_2184_ = (leanh::lean_unbox(v___x_2183_) as u8);
                    if v___x_2184_ == 0 {
                        leanh::lean_inc_ref(v_children_2173_);
                        leanh::lean_inc_ref(v_i_2172_);
                        leanh::lean_dec_ref_known(v_t_2165_, 2);
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2180_);
                        leanh::lean_dec_ref(v_f_2166_);
                        v_isSharedCheck_2192_ =
                            (!leanh::lean_is_exclusive(v_ctx_x3f_2164_)) as u8;
                        if v_isSharedCheck_2192_ == 0 {
                            v_unused_2193_ = leanh::lean_ctor_get(v_ctx_x3f_2164_, 0);
                            leanh::lean_dec(v_unused_2193_);
                            v___x_2186_ = v_ctx_x3f_2164_;
                            v_isShared_2187_ = v_isSharedCheck_2192_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec(v_ctx_x3f_2164_);
                            v___x_2186_ = leanh::lean_box(0);
                            v_isShared_2187_ = v_isSharedCheck_2192_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_2188_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2188_, 0, v_val_2180_);
                leanh::lean_ctor_set(v___x_2188_, 1, v_t_2165_);
                if v_isShared_2187_ == 0 {
                    leanh::lean_ctor_set(v___x_2186_, 0, v___x_2188_);
                    v___x_2190_ = v___x_2186_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2191_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2188_);
                    v___x_2190_ = v_reuseFailAlloc_2191_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2190_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(
    mut v_ctx_x3f_2210_: *mut leanh::LeanObject,
    mut v_i_2211_: *mut leanh::LeanObject,
    mut v_kind_2212_: *mut leanh::LeanObject,
    mut v_tgtRange_2213_: *mut leanh::LeanObject,
    mut v_f_2214_: *mut leanh::LeanObject,
    mut v_canonicalOnly_2215_: u8,
    mut v_as_2216_: *mut leanh::LeanObject,
    mut v_sz_2217_: usize,
    mut v_i_2218_: usize,
    mut v_b_2219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2220_: u8 = 0;
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2225_: u8 = 0;
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2234_: u8 = 0;
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2241_: u8 = 0;
    let mut v_unused_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: usize = 0;
    let mut v___x_2246_: usize = 0;
    let mut v_isSharedCheck_2248_: u8 = 0;
    let mut v_unused_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2220_ = lean_usize_dec_lt(v_i_2218_, v_sz_2217_);
                if v___x_2220_ == 0 {
                    leanh::lean_dec_ref(v_f_2214_);
                    leanh::lean_dec(v_ctx_x3f_2210_);
                    v___x_2221_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2221_, 0, v_b_2219_);
                    return v___x_2221_;
                } else {
                    v_snd_2222_ = leanh::lean_ctor_get(v_b_2219_, 1);
                    v_isSharedCheck_2248_ = (!leanh::lean_is_exclusive(v_b_2219_)) as u8;
                    if v_isSharedCheck_2248_ == 0 {
                        v_unused_2249_ = leanh::lean_ctor_get(v_b_2219_, 0);
                        leanh::lean_dec(v_unused_2249_);
                        v___x_2224_ = v_b_2219_;
                        v_isShared_2225_ = v_isSharedCheck_2248_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2222_);
                        leanh::lean_dec(v_b_2219_);
                        v___x_2224_ = leanh::lean_box(0);
                        v_isShared_2225_ = v_isSharedCheck_2248_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2226_ = leanh::lean_box(0);
                v_a_2227_ = lean_array_uget_borrowed(v_as_2216_, v_i_2218_);
                leanh::lean_inc(v_ctx_x3f_2210_);
                v___x_2228_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_2210_, v_i_2211_);
                leanh::lean_inc_ref(v_f_2214_);
                leanh::lean_inc(v_a_2227_);
                v___x_2229_ = l_Lean_CodeAction_findInfoTree_x3f(
                    v_kind_2212_,
                    v_tgtRange_2213_,
                    v___x_2228_,
                    v_a_2227_,
                    v_f_2214_,
                    v_canonicalOnly_2215_,
                );
                if leanh::lean_obj_tag(v___x_2229_) == 1 {
                    leanh::lean_dec_ref(v_f_2214_);
                    leanh::lean_dec(v_ctx_x3f_2210_);
                    leanh::lean_inc_ref(v___x_2229_);
                    if v_isShared_2225_ == 0 {
                        leanh::lean_ctor_set(v___x_2224_, 1, v___x_2226_);
                        leanh::lean_ctor_set(v___x_2224_, 0, v___x_2229_);
                        v___x_2231_ = v___x_2224_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2243_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2229_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 1, v___x_2226_);
                        v___x_2231_ = v_reuseFailAlloc_2243_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2229_);
                    leanh::lean_del_object(v___x_2224_);
                    leanh::lean_dec(v_snd_2222_);
                    v___x_2244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__1;
                    v___x_2245_ = 1usize;
                    v___x_2246_ = lean_usize_add(v_i_2218_, v___x_2245_);
                    v_i_2218_ = v___x_2246_;
                    v_b_2219_ = v___x_2244_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_isSharedCheck_2241_ = (!leanh::lean_is_exclusive(v___x_2229_)) as u8;
                if v_isSharedCheck_2241_ == 0 {
                    v_unused_2242_ = leanh::lean_ctor_get(v___x_2229_, 0);
                    leanh::lean_dec(v_unused_2242_);
                    v___x_2233_ = v___x_2229_;
                    v_isShared_2234_ = v_isSharedCheck_2241_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___x_2229_);
                    v___x_2233_ = leanh::lean_box(0);
                    v_isShared_2234_ = v_isSharedCheck_2241_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2234_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2233_, 0);
                    leanh::lean_ctor_set(v___x_2233_, 0, v___x_2231_);
                    v___x_2236_ = v___x_2233_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2240_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2231_);
                    v___x_2236_ = v_reuseFailAlloc_2240_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2237_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2237_, 0, v___x_2236_);
                v___x_2238_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2238_, 0, v___x_2237_);
                leanh::lean_ctor_set(v___x_2238_, 1, v_snd_2222_);
                v___x_2239_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2239_, 0, v___x_2238_);
                return v___x_2239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(
    mut v_ctx_x3f_2250_: *mut leanh::LeanObject,
    mut v_i_2251_: *mut leanh::LeanObject,
    mut v_kind_2252_: *mut leanh::LeanObject,
    mut v_tgtRange_2253_: *mut leanh::LeanObject,
    mut v_f_2254_: *mut leanh::LeanObject,
    mut v_canonicalOnly_2255_: u8,
    mut v_as_2256_: *mut leanh::LeanObject,
    mut v_sz_2257_: usize,
    mut v_i_2258_: usize,
    mut v_b_2259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2260_: u8 = 0;
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2265_: u8 = 0;
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2274_: u8 = 0;
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2281_: u8 = 0;
    let mut v_unused_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: usize = 0;
    let mut v___x_2286_: usize = 0;
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2288_: u8 = 0;
    let mut v_unused_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2260_ = lean_usize_dec_lt(v_i_2258_, v_sz_2257_);
                if v___x_2260_ == 0 {
                    leanh::lean_dec_ref(v_f_2254_);
                    leanh::lean_dec(v_ctx_x3f_2250_);
                    v___x_2261_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2261_, 0, v_b_2259_);
                    return v___x_2261_;
                } else {
                    v_snd_2262_ = leanh::lean_ctor_get(v_b_2259_, 1);
                    v_isSharedCheck_2288_ = (!leanh::lean_is_exclusive(v_b_2259_)) as u8;
                    if v_isSharedCheck_2288_ == 0 {
                        v_unused_2289_ = leanh::lean_ctor_get(v_b_2259_, 0);
                        leanh::lean_dec(v_unused_2289_);
                        v___x_2264_ = v_b_2259_;
                        v_isShared_2265_ = v_isSharedCheck_2288_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2262_);
                        leanh::lean_dec(v_b_2259_);
                        v___x_2264_ = leanh::lean_box(0);
                        v_isShared_2265_ = v_isSharedCheck_2288_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2266_ = leanh::lean_box(0);
                v_a_2267_ = lean_array_uget_borrowed(v_as_2256_, v_i_2258_);
                leanh::lean_inc(v_ctx_x3f_2250_);
                v___x_2268_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_2250_, v_i_2251_);
                leanh::lean_inc_ref(v_f_2254_);
                leanh::lean_inc(v_a_2267_);
                v___x_2269_ = l_Lean_CodeAction_findInfoTree_x3f(
                    v_kind_2252_,
                    v_tgtRange_2253_,
                    v___x_2268_,
                    v_a_2267_,
                    v_f_2254_,
                    v_canonicalOnly_2255_,
                );
                if leanh::lean_obj_tag(v___x_2269_) == 1 {
                    leanh::lean_dec_ref(v_f_2254_);
                    leanh::lean_dec(v_ctx_x3f_2250_);
                    leanh::lean_inc_ref(v___x_2269_);
                    if v_isShared_2265_ == 0 {
                        leanh::lean_ctor_set(v___x_2264_, 1, v___x_2266_);
                        leanh::lean_ctor_set(v___x_2264_, 0, v___x_2269_);
                        v___x_2271_ = v___x_2264_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2283_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2269_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2283_, 1, v___x_2266_);
                        v___x_2271_ = v_reuseFailAlloc_2283_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2269_);
                    leanh::lean_del_object(v___x_2264_);
                    leanh::lean_dec(v_snd_2262_);
                    v___x_2284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___closed__0;
                    v___x_2285_ = 1usize;
                    v___x_2286_ = lean_usize_add(v_i_2258_, v___x_2285_);
                    v___x_2287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(v_ctx_x3f_2250_, v_i_2251_, v_kind_2252_, v_tgtRange_2253_, v_f_2254_, v_canonicalOnly_2255_, v_as_2256_, v_sz_2257_, v___x_2286_, v___x_2284_);
                    return v___x_2287_;
                }
            }
            2 => {
                v_isSharedCheck_2281_ = (!leanh::lean_is_exclusive(v___x_2269_)) as u8;
                if v_isSharedCheck_2281_ == 0 {
                    v_unused_2282_ = leanh::lean_ctor_get(v___x_2269_, 0);
                    leanh::lean_dec(v_unused_2282_);
                    v___x_2273_ = v___x_2269_;
                    v_isShared_2274_ = v_isSharedCheck_2281_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___x_2269_);
                    v___x_2273_ = leanh::lean_box(0);
                    v_isShared_2274_ = v_isSharedCheck_2281_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2274_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2273_, 0);
                    leanh::lean_ctor_set(v___x_2273_, 0, v___x_2271_);
                    v___x_2276_ = v___x_2273_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2280_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2271_);
                    v___x_2276_ = v_reuseFailAlloc_2280_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2277_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2277_, 0, v___x_2276_);
                v___x_2278_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2278_, 0, v___x_2277_);
                leanh::lean_ctor_set(v___x_2278_, 1, v_snd_2262_);
                v___x_2279_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2279_, 0, v___x_2278_);
                return v___x_2279_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(
    mut v_init_2290_: *mut leanh::LeanObject,
    mut v_ctx_x3f_2291_: *mut leanh::LeanObject,
    mut v_i_2292_: *mut leanh::LeanObject,
    mut v_kind_2293_: *mut leanh::LeanObject,
    mut v_tgtRange_2294_: *mut leanh::LeanObject,
    mut v_f_2295_: *mut leanh::LeanObject,
    mut v_canonicalOnly_2296_: u8,
    mut v_n_2297_: *mut leanh::LeanObject,
    mut v_b_2298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2302_: usize = 0;
    let mut v___x_2303_: usize = 0;
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2308_: u8 = 0;
    let mut v_fst_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2315_: u8 = 0;
    let mut v_vs_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2319_: usize = 0;
    let mut v___x_2320_: usize = 0;
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2325_: u8 = 0;
    let mut v_fst_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2332_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_2297_) == 0 {
                    v_cs_2299_ = leanh::lean_ctor_get(v_n_2297_, 0);
                    v___x_2300_ = leanh::lean_box(0);
                    v___x_2301_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2301_, 0, v___x_2300_);
                    leanh::lean_ctor_set(v___x_2301_, 1, v_b_2298_);
                    v_sz_2302_ = lean_array_size(v_cs_2299_);
                    v___x_2303_ = 0usize;
                    v___x_2304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(v_init_2290_, v_ctx_x3f_2291_, v_i_2292_, v_kind_2293_, v_tgtRange_2294_, v_f_2295_, v_canonicalOnly_2296_, v_cs_2299_, v_sz_2302_, v___x_2303_, v___x_2301_);
                    if leanh::lean_obj_tag(v___x_2304_) == 0 {
                        return v___x_2300_;
                    } else {
                        v_val_2305_ = leanh::lean_ctor_get(v___x_2304_, 0);
                        v_isSharedCheck_2315_ =
                            (!leanh::lean_is_exclusive(v___x_2304_)) as u8;
                        if v_isSharedCheck_2315_ == 0 {
                            v___x_2307_ = v___x_2304_;
                            v_isShared_2308_ = v_isSharedCheck_2315_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2305_);
                            leanh::lean_dec(v___x_2304_);
                            v___x_2307_ = leanh::lean_box(0);
                            v_isShared_2308_ = v_isSharedCheck_2315_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_vs_2316_ = leanh::lean_ctor_get(v_n_2297_, 0);
                    v___x_2317_ = leanh::lean_box(0);
                    v___x_2318_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2318_, 0, v___x_2317_);
                    leanh::lean_ctor_set(v___x_2318_, 1, v_b_2298_);
                    v_sz_2319_ = lean_array_size(v_vs_2316_);
                    v___x_2320_ = 0usize;
                    v___x_2321_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(v_ctx_x3f_2291_, v_i_2292_, v_kind_2293_, v_tgtRange_2294_, v_f_2295_, v_canonicalOnly_2296_, v_vs_2316_, v_sz_2319_, v___x_2320_, v___x_2318_);
                    if leanh::lean_obj_tag(v___x_2321_) == 0 {
                        return v___x_2317_;
                    } else {
                        v_val_2322_ = leanh::lean_ctor_get(v___x_2321_, 0);
                        v_isSharedCheck_2332_ =
                            (!leanh::lean_is_exclusive(v___x_2321_)) as u8;
                        if v_isSharedCheck_2332_ == 0 {
                            v___x_2324_ = v___x_2321_;
                            v_isShared_2325_ = v_isSharedCheck_2332_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2322_);
                            leanh::lean_dec(v___x_2321_);
                            v___x_2324_ = leanh::lean_box(0);
                            v_isShared_2325_ = v_isSharedCheck_2332_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_2309_ = leanh::lean_ctor_get(v_val_2305_, 0);
                if leanh::lean_obj_tag(v_fst_2309_) == 0 {
                    v_snd_2310_ = leanh::lean_ctor_get(v_val_2305_, 1);
                    leanh::lean_inc(v_snd_2310_);
                    leanh::lean_dec(v_val_2305_);
                    v___x_2311_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2311_, 0, v_snd_2310_);
                    if v_isShared_2308_ == 0 {
                        leanh::lean_ctor_set(v___x_2307_, 0, v___x_2311_);
                        v___x_2313_ = v___x_2307_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2314_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2311_);
                        v___x_2313_ = v_reuseFailAlloc_2314_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_2309_);
                    leanh::lean_del_object(v___x_2307_);
                    leanh::lean_dec(v_val_2305_);
                    return v_fst_2309_;
                }
            }
            2 => {
                return v___x_2313_;
            }
            3 => {
                v_fst_2326_ = leanh::lean_ctor_get(v_val_2322_, 0);
                if leanh::lean_obj_tag(v_fst_2326_) == 0 {
                    v_snd_2327_ = leanh::lean_ctor_get(v_val_2322_, 1);
                    leanh::lean_inc(v_snd_2327_);
                    leanh::lean_dec(v_val_2322_);
                    v___x_2328_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2328_, 0, v_snd_2327_);
                    if v_isShared_2325_ == 0 {
                        leanh::lean_ctor_set(v___x_2324_, 0, v___x_2328_);
                        v___x_2330_ = v___x_2324_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2331_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2328_);
                        v___x_2330_ = v_reuseFailAlloc_2331_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_2326_);
                    leanh::lean_del_object(v___x_2324_);
                    leanh::lean_dec(v_val_2322_);
                    return v_fst_2326_;
                }
            }
            4 => {
                return v___x_2330_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(
    mut v_init_2333_: *mut leanh::LeanObject,
    mut v_ctx_x3f_2334_: *mut leanh::LeanObject,
    mut v_i_2335_: *mut leanh::LeanObject,
    mut v_kind_2336_: *mut leanh::LeanObject,
    mut v_tgtRange_2337_: *mut leanh::LeanObject,
    mut v_f_2338_: *mut leanh::LeanObject,
    mut v_canonicalOnly_2339_: u8,
    mut v_as_2340_: *mut leanh::LeanObject,
    mut v_sz_2341_: usize,
    mut v_i_2342_: usize,
    mut v_b_2343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2344_: u8 = 0;
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2349_: u8 = 0;
    let mut v_a_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2356_: u8 = 0;
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2363_: u8 = 0;
    let mut v_unused_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: usize = 0;
    let mut v___x_2370_: usize = 0;
    let mut v_reuseFailAlloc_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2373_: u8 = 0;
    let mut v_unused_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2344_ = lean_usize_dec_lt(v_i_2342_, v_sz_2341_);
                if v___x_2344_ == 0 {
                    leanh::lean_dec_ref(v_f_2338_);
                    leanh::lean_dec(v_ctx_x3f_2334_);
                    v___x_2345_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2345_, 0, v_b_2343_);
                    return v___x_2345_;
                } else {
                    v_snd_2346_ = leanh::lean_ctor_get(v_b_2343_, 1);
                    v_isSharedCheck_2373_ = (!leanh::lean_is_exclusive(v_b_2343_)) as u8;
                    if v_isSharedCheck_2373_ == 0 {
                        v_unused_2374_ = leanh::lean_ctor_get(v_b_2343_, 0);
                        leanh::lean_dec(v_unused_2374_);
                        v___x_2348_ = v_b_2343_;
                        v_isShared_2349_ = v_isSharedCheck_2373_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2346_);
                        leanh::lean_dec(v_b_2343_);
                        v___x_2348_ = leanh::lean_box(0);
                        v_isShared_2349_ = v_isSharedCheck_2373_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2350_ = lean_array_uget_borrowed(v_as_2340_, v_i_2342_);
                leanh::lean_inc(v_snd_2346_);
                leanh::lean_inc_ref(v_f_2338_);
                leanh::lean_inc(v_ctx_x3f_2334_);
                v___x_2351_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(v_init_2333_, v_ctx_x3f_2334_, v_i_2335_, v_kind_2336_, v_tgtRange_2337_, v_f_2338_, v_canonicalOnly_2339_, v_a_2350_, v_snd_2346_);
                if leanh::lean_obj_tag(v___x_2351_) == 0 {
                    leanh::lean_del_object(v___x_2348_);
                    leanh::lean_dec(v_snd_2346_);
                    leanh::lean_dec_ref(v_f_2338_);
                    leanh::lean_dec(v_ctx_x3f_2334_);
                    v___x_2352_ = leanh::lean_box(0);
                    return v___x_2352_;
                } else {
                    v_val_2353_ = leanh::lean_ctor_get(v___x_2351_, 0);
                    leanh::lean_inc(v_val_2353_);
                    if leanh::lean_obj_tag(v_val_2353_) == 0 {
                        leanh::lean_dec_ref(v_f_2338_);
                        leanh::lean_dec(v_ctx_x3f_2334_);
                        v_isSharedCheck_2363_ =
                            (!leanh::lean_is_exclusive(v_val_2353_)) as u8;
                        if v_isSharedCheck_2363_ == 0 {
                            v_unused_2364_ = leanh::lean_ctor_get(v_val_2353_, 0);
                            leanh::lean_dec(v_unused_2364_);
                            v___x_2355_ = v_val_2353_;
                            v_isShared_2356_ = v_isSharedCheck_2363_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v_val_2353_);
                            v___x_2355_ = leanh::lean_box(0);
                            v_isShared_2356_ = v_isSharedCheck_2363_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_2351_, 1);
                        leanh::lean_dec(v_snd_2346_);
                        v_a_2365_ = leanh::lean_ctor_get(v_val_2353_, 0);
                        leanh::lean_inc(v_a_2365_);
                        leanh::lean_dec_ref_known(v_val_2353_, 1);
                        v___x_2366_ = leanh::lean_box(0);
                        if v_isShared_2349_ == 0 {
                            leanh::lean_ctor_set(v___x_2348_, 1, v_a_2365_);
                            leanh::lean_ctor_set(v___x_2348_, 0, v___x_2366_);
                            v___x_2368_ = v___x_2348_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_2372_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2366_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2372_, 1, v_a_2365_);
                            v___x_2368_ = v_reuseFailAlloc_2372_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_2349_ == 0 {
                    leanh::lean_ctor_set(v___x_2348_, 0, v___x_2351_);
                    v___x_2358_ = v___x_2348_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2362_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2351_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2362_, 1, v_snd_2346_);
                    v___x_2358_ = v_reuseFailAlloc_2362_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2356_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2355_, 1);
                    leanh::lean_ctor_set(v___x_2355_, 0, v___x_2358_);
                    v___x_2360_ = v___x_2355_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2361_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2358_);
                    v___x_2360_ = v_reuseFailAlloc_2361_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2360_;
            }
            5 => {
                v___x_2369_ = 1usize;
                v___x_2370_ = lean_usize_add(v_i_2342_, v___x_2369_);
                v_i_2342_ = v___x_2370_;
                v_b_2343_ = v___x_2368_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_init_2375_: *mut leanh::LeanObject,
    mut v_ctx_x3f_2376_: *mut leanh::LeanObject,
    mut v_i_2377_: *mut leanh::LeanObject,
    mut v_kind_2378_: *mut leanh::LeanObject,
    mut v_tgtRange_2379_: *mut leanh::LeanObject,
    mut v_f_2380_: *mut leanh::LeanObject,
    mut v_canonicalOnly_2381_: *mut leanh::LeanObject,
    mut v_as_2382_: *mut leanh::LeanObject,
    mut v_sz_2383_: *mut leanh::LeanObject,
    mut v_i_2384_: *mut leanh::LeanObject,
    mut v_b_2385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_canonicalOnly_boxed_2386_: u8 = 0;
    let mut v_sz_boxed_2387_: usize = 0;
    let mut v_i_boxed_2388_: usize = 0;
    let mut v_res_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_2386_ = (leanh::lean_unbox(v_canonicalOnly_2381_) as u8);
    v_sz_boxed_2387_ = leanh::lean_unbox_usize(v_sz_2383_);
    leanh::lean_dec(v_sz_2383_);
    v_i_boxed_2388_ = leanh::lean_unbox_usize(v_i_2384_);
    leanh::lean_dec(v_i_2384_);
    v_res_2389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(v_init_2375_, v_ctx_x3f_2376_, v_i_2377_, v_kind_2378_, v_tgtRange_2379_, v_f_2380_, v_canonicalOnly_boxed_2386_, v_as_2382_, v_sz_boxed_2387_, v_i_boxed_2388_, v_b_2385_);
    leanh::lean_dec_ref(v_as_2382_);
    leanh::lean_dec_ref(v_tgtRange_2379_);
    leanh::lean_dec(v_kind_2378_);
    leanh::lean_dec_ref(v_i_2377_);
    leanh::lean_dec_ref(v_init_2375_);
    return v_res_2389_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0___boxed(
    mut v_ctx_x3f_2390_: *mut leanh::LeanObject,
    mut v_i_2391_: *mut leanh::LeanObject,
    mut v_kind_2392_: *mut leanh::LeanObject,
    mut v_tgtRange_2393_: *mut leanh::LeanObject,
    mut v_f_2394_: *mut leanh::LeanObject,
    mut v_canonicalOnly_2395_: *mut leanh::LeanObject,
    mut v_t_2396_: *mut leanh::LeanObject,
    mut v_init_2397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_canonicalOnly_boxed_2398_: u8 = 0;
    let mut v_res_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_2398_ = (leanh::lean_unbox(v_canonicalOnly_2395_) as u8);
    v_res_2399_ = l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(
        v_ctx_x3f_2390_,
        v_i_2391_,
        v_kind_2392_,
        v_tgtRange_2393_,
        v_f_2394_,
        v_canonicalOnly_boxed_2398_,
        v_t_2396_,
        v_init_2397_,
    );
    leanh::lean_dec_ref(v_t_2396_);
    leanh::lean_dec_ref(v_tgtRange_2393_);
    leanh::lean_dec(v_kind_2392_);
    leanh::lean_dec_ref(v_i_2391_);
    return v_res_2399_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___boxed(
    mut v_ctx_x3f_2400_: *mut leanh::LeanObject,
    mut v_i_2401_: *mut leanh::LeanObject,
    mut v_kind_2402_: *mut leanh::LeanObject,
    mut v_tgtRange_2403_: *mut leanh::LeanObject,
    mut v_f_2404_: *mut leanh::LeanObject,
    mut v_canonicalOnly_2405_: *mut leanh::LeanObject,
    mut v_as_2406_: *mut leanh::LeanObject,
    mut v_sz_2407_: *mut leanh::LeanObject,
    mut v_i_2408_: *mut leanh::LeanObject,
    mut v_b_2409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_canonicalOnly_boxed_2410_: u8 = 0;
    let mut v_sz_boxed_2411_: usize = 0;
    let mut v_i_boxed_2412_: usize = 0;
    let mut v_res_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_2410_ = (leanh::lean_unbox(v_canonicalOnly_2405_) as u8);
    v_sz_boxed_2411_ = leanh::lean_unbox_usize(v_sz_2407_);
    leanh::lean_dec(v_sz_2407_);
    v_i_boxed_2412_ = leanh::lean_unbox_usize(v_i_2408_);
    leanh::lean_dec(v_i_2408_);
    v_res_2413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(v_ctx_x3f_2400_, v_i_2401_, v_kind_2402_, v_tgtRange_2403_, v_f_2404_, v_canonicalOnly_boxed_2410_, v_as_2406_, v_sz_boxed_2411_, v_i_boxed_2412_, v_b_2409_);
    leanh::lean_dec_ref(v_as_2406_);
    leanh::lean_dec_ref(v_tgtRange_2403_);
    leanh::lean_dec(v_kind_2402_);
    leanh::lean_dec_ref(v_i_2401_);
    return v_res_2413_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___boxed(
    mut v_ctx_x3f_2414_: *mut leanh::LeanObject,
    mut v_i_2415_: *mut leanh::LeanObject,
    mut v_kind_2416_: *mut leanh::LeanObject,
    mut v_tgtRange_2417_: *mut leanh::LeanObject,
    mut v_f_2418_: *mut leanh::LeanObject,
    mut v_canonicalOnly_2419_: *mut leanh::LeanObject,
    mut v_as_2420_: *mut leanh::LeanObject,
    mut v_sz_2421_: *mut leanh::LeanObject,
    mut v_i_2422_: *mut leanh::LeanObject,
    mut v_b_2423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_canonicalOnly_boxed_2424_: u8 = 0;
    let mut v_sz_boxed_2425_: usize = 0;
    let mut v_i_boxed_2426_: usize = 0;
    let mut v_res_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_2424_ = (leanh::lean_unbox(v_canonicalOnly_2419_) as u8);
    v_sz_boxed_2425_ = leanh::lean_unbox_usize(v_sz_2421_);
    leanh::lean_dec(v_sz_2421_);
    v_i_boxed_2426_ = leanh::lean_unbox_usize(v_i_2422_);
    leanh::lean_dec(v_i_2422_);
    v_res_2427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(v_ctx_x3f_2414_, v_i_2415_, v_kind_2416_, v_tgtRange_2417_, v_f_2418_, v_canonicalOnly_boxed_2424_, v_as_2420_, v_sz_boxed_2425_, v_i_boxed_2426_, v_b_2423_);
    leanh::lean_dec_ref(v_as_2420_);
    leanh::lean_dec_ref(v_tgtRange_2417_);
    leanh::lean_dec(v_kind_2416_);
    leanh::lean_dec_ref(v_i_2415_);
    return v_res_2427_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___boxed(
    mut v_ctx_x3f_2428_: *mut leanh::LeanObject,
    mut v_i_2429_: *mut leanh::LeanObject,
    mut v_kind_2430_: *mut leanh::LeanObject,
    mut v_tgtRange_2431_: *mut leanh::LeanObject,
    mut v_f_2432_: *mut leanh::LeanObject,
    mut v_canonicalOnly_2433_: *mut leanh::LeanObject,
    mut v_as_2434_: *mut leanh::LeanObject,
    mut v_sz_2435_: *mut leanh::LeanObject,
    mut v_i_2436_: *mut leanh::LeanObject,
    mut v_b_2437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_canonicalOnly_boxed_2438_: u8 = 0;
    let mut v_sz_boxed_2439_: usize = 0;
    let mut v_i_boxed_2440_: usize = 0;
    let mut v_res_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_2438_ = (leanh::lean_unbox(v_canonicalOnly_2433_) as u8);
    v_sz_boxed_2439_ = leanh::lean_unbox_usize(v_sz_2435_);
    leanh::lean_dec(v_sz_2435_);
    v_i_boxed_2440_ = leanh::lean_unbox_usize(v_i_2436_);
    leanh::lean_dec(v_i_2436_);
    v_res_2441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(v_ctx_x3f_2428_, v_i_2429_, v_kind_2430_, v_tgtRange_2431_, v_f_2432_, v_canonicalOnly_boxed_2438_, v_as_2434_, v_sz_boxed_2439_, v_i_boxed_2440_, v_b_2437_);
    leanh::lean_dec_ref(v_as_2434_);
    leanh::lean_dec_ref(v_tgtRange_2431_);
    leanh::lean_dec(v_kind_2430_);
    leanh::lean_dec_ref(v_i_2429_);
    return v_res_2441_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___boxed(
    mut v_ctx_x3f_2442_: *mut leanh::LeanObject,
    mut v_i_2443_: *mut leanh::LeanObject,
    mut v_kind_2444_: *mut leanh::LeanObject,
    mut v_tgtRange_2445_: *mut leanh::LeanObject,
    mut v_f_2446_: *mut leanh::LeanObject,
    mut v_canonicalOnly_2447_: *mut leanh::LeanObject,
    mut v_as_2448_: *mut leanh::LeanObject,
    mut v_sz_2449_: *mut leanh::LeanObject,
    mut v_i_2450_: *mut leanh::LeanObject,
    mut v_b_2451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_canonicalOnly_boxed_2452_: u8 = 0;
    let mut v_sz_boxed_2453_: usize = 0;
    let mut v_i_boxed_2454_: usize = 0;
    let mut v_res_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_2452_ = (leanh::lean_unbox(v_canonicalOnly_2447_) as u8);
    v_sz_boxed_2453_ = leanh::lean_unbox_usize(v_sz_2449_);
    leanh::lean_dec(v_sz_2449_);
    v_i_boxed_2454_ = leanh::lean_unbox_usize(v_i_2450_);
    leanh::lean_dec(v_i_2450_);
    v_res_2455_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(v_ctx_x3f_2442_, v_i_2443_, v_kind_2444_, v_tgtRange_2445_, v_f_2446_, v_canonicalOnly_boxed_2452_, v_as_2448_, v_sz_boxed_2453_, v_i_boxed_2454_, v_b_2451_);
    leanh::lean_dec_ref(v_as_2448_);
    leanh::lean_dec_ref(v_tgtRange_2445_);
    leanh::lean_dec(v_kind_2444_);
    leanh::lean_dec_ref(v_i_2443_);
    return v_res_2455_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0___boxed(
    mut v_init_2456_: *mut leanh::LeanObject,
    mut v_ctx_x3f_2457_: *mut leanh::LeanObject,
    mut v_i_2458_: *mut leanh::LeanObject,
    mut v_kind_2459_: *mut leanh::LeanObject,
    mut v_tgtRange_2460_: *mut leanh::LeanObject,
    mut v_f_2461_: *mut leanh::LeanObject,
    mut v_canonicalOnly_2462_: *mut leanh::LeanObject,
    mut v_n_2463_: *mut leanh::LeanObject,
    mut v_b_2464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_canonicalOnly_boxed_2465_: u8 = 0;
    let mut v_res_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_2465_ = (leanh::lean_unbox(v_canonicalOnly_2462_) as u8);
    v_res_2466_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(v_init_2456_, v_ctx_x3f_2457_, v_i_2458_, v_kind_2459_, v_tgtRange_2460_, v_f_2461_, v_canonicalOnly_boxed_2465_, v_n_2463_, v_b_2464_);
    leanh::lean_dec_ref(v_n_2463_);
    leanh::lean_dec_ref(v_tgtRange_2460_);
    leanh::lean_dec(v_kind_2459_);
    leanh::lean_dec_ref(v_i_2458_);
    leanh::lean_dec_ref(v_init_2456_);
    return v_res_2466_;
}
pub unsafe fn l_Lean_CodeAction_findInfoTree_x3f___boxed(
    mut v_kind_2467_: *mut leanh::LeanObject,
    mut v_tgtRange_2468_: *mut leanh::LeanObject,
    mut v_ctx_x3f_2469_: *mut leanh::LeanObject,
    mut v_t_2470_: *mut leanh::LeanObject,
    mut v_f_2471_: *mut leanh::LeanObject,
    mut v_canonicalOnly_2472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_canonicalOnly_boxed_2473_: u8 = 0;
    let mut v_res_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_2473_ = (leanh::lean_unbox(v_canonicalOnly_2472_) as u8);
    v_res_2474_ = l_Lean_CodeAction_findInfoTree_x3f(
        v_kind_2467_,
        v_tgtRange_2468_,
        v_ctx_x3f_2469_,
        v_t_2470_,
        v_f_2471_,
        v_canonicalOnly_boxed_2473_,
    );
    leanh::lean_dec_ref(v_tgtRange_2468_);
    leanh::lean_dec(v_kind_2467_);
    return v_res_2474_;
}
pub unsafe fn _init_l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2475_ = l_Lean_Server_instInhabitedRequestError_default;
    v___x_2476_ = leanh::lean_alloc_closure(
        l_instInhabitedEIO___aux__1___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___x_2476_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2476_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2476_, 2, v___x_2475_);
    return v___x_2476_;
}
pub unsafe fn l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(
    mut v_msg_2477_: *mut leanh::LeanObject,
    mut v___y_2478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028__overap_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2480_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0_once
        ),
        _init_l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0,
    );
    v___f_2481_ = leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2481_, 0, v___x_2480_);
    v___x_4028__overap_2482_ = lean_panic_fn_borrowed(v___f_2481_, v_msg_2477_);
    leanh::lean_dec_ref(v___f_2481_);
    leanh::lean_inc_ref(v___y_2478_);
    v___x_2483_ = leanh::lean_apply_2(
        v___x_4028__overap_2482_,
        v___y_2478_,
        leanh::lean_box(0),
    );
    return v___x_2483_;
}
pub unsafe fn l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___boxed(
    mut v_msg_2484_: *mut leanh::LeanObject,
    mut v___y_2485_: *mut leanh::LeanObject,
    mut v___y_2486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2487_ =
        l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(v_msg_2484_, v___y_2485_);
    leanh::lean_dec_ref(v___y_2485_);
    return v_res_2487_;
}
pub unsafe fn l_Lean_CodeAction_cmdCodeActionProvider___lam__0(
    mut v___x_2488_: *mut leanh::LeanObject,
    mut v___x_2489_: *mut leanh::LeanObject,
    mut v_ctx_2490_: *mut leanh::LeanObject,
    mut v_node_2491_: *mut leanh::LeanObject,
    mut v_result_2492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2494_: u8 = 0;
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: u8 = 0;
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: u8 = 0;
    let mut v___x_2506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_node_2491_) == 1 {
                    v_i_2497_ = leanh::lean_ctor_get(v_node_2491_, 0);
                    if leanh::lean_obj_tag(v_i_2497_) == 3 {
                        v_i_2498_ = leanh::lean_ctor_get(v_i_2497_, 0);
                        v_stx_2499_ = leanh::lean_ctor_get(v_i_2498_, 1);
                        v___x_2500_ = 1;
                        v___x_2501_ = l_Lean_Syntax_getPos_x3f(v_stx_2499_, v___x_2500_);
                        if leanh::lean_obj_tag(v___x_2501_) == 1 {
                            v_val_2502_ = leanh::lean_ctor_get(v___x_2501_, 0);
                            leanh::lean_inc(v_val_2502_);
                            leanh::lean_dec_ref_known(v___x_2501_, 1);
                            v___x_2503_ = l_Lean_Syntax_getTailPos_x3f(v_stx_2499_, v___x_2500_);
                            if leanh::lean_obj_tag(v___x_2503_) == 1 {
                                v_val_2504_ = leanh::lean_ctor_get(v___x_2503_, 0);
                                leanh::lean_inc(v_val_2504_);
                                leanh::lean_dec_ref_known(v___x_2503_, 1);
                                v___x_2505_ = lean_nat_dec_le(v_val_2502_, v___x_2488_);
                                leanh::lean_dec(v_val_2502_);
                                if v___x_2505_ == 0 {
                                    leanh::lean_dec(v_val_2504_);
                                    v___y_2494_ = v___x_2505_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_2506_ = lean_nat_dec_le(v___x_2489_, v_val_2504_);
                                    leanh::lean_dec(v_val_2504_);
                                    v___y_2494_ = v___x_2506_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v___x_2503_);
                                leanh::lean_dec(v_val_2502_);
                                leanh::lean_dec_ref_known(v_node_2491_, 2);
                                leanh::lean_dec_ref(v_ctx_2490_);
                                return v_result_2492_;
                            }
                        } else {
                            leanh::lean_dec(v___x_2501_);
                            leanh::lean_dec_ref_known(v_node_2491_, 2);
                            leanh::lean_dec_ref(v_ctx_2490_);
                            return v_result_2492_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_node_2491_, 2);
                        leanh::lean_dec_ref(v_ctx_2490_);
                        return v_result_2492_;
                    }
                } else {
                    leanh::lean_dec_ref(v_node_2491_);
                    leanh::lean_dec_ref(v_ctx_2490_);
                    return v_result_2492_;
                }
            }
            1 => {
                if v___y_2494_ == 0 {
                    leanh::lean_dec_ref(v_node_2491_);
                    leanh::lean_dec_ref(v_ctx_2490_);
                    return v_result_2492_;
                } else {
                    v___x_2495_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2495_, 0, v_ctx_2490_);
                    leanh::lean_ctor_set(v___x_2495_, 1, v_node_2491_);
                    v___x_2496_ = lean_array_push(v_result_2492_, v___x_2495_);
                    return v___x_2496_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_CodeAction_cmdCodeActionProvider___lam__0___boxed(
    mut v___x_2507_: *mut leanh::LeanObject,
    mut v___x_2508_: *mut leanh::LeanObject,
    mut v_ctx_2509_: *mut leanh::LeanObject,
    mut v_node_2510_: *mut leanh::LeanObject,
    mut v_result_2511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2512_ = l_Lean_CodeAction_cmdCodeActionProvider___lam__0(
        v___x_2507_,
        v___x_2508_,
        v_ctx_2509_,
        v_node_2510_,
        v_result_2511_,
    );
    leanh::lean_dec(v___x_2508_);
    leanh::lean_dec(v___x_2507_);
    return v_res_2512_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(
    mut v_params_2513_: *mut leanh::LeanObject,
    mut v_snap_2514_: *mut leanh::LeanObject,
    mut v_fst_2515_: *mut leanh::LeanObject,
    mut v_snd_2516_: *mut leanh::LeanObject,
    mut v_as_2517_: *mut leanh::LeanObject,
    mut v_sz_2518_: usize,
    mut v_i_2519_: usize,
    mut v_b_2520_: *mut leanh::LeanObject,
    mut v___y_2521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: usize = 0;
    let mut v___x_2526_: usize = 0;
    let mut v___x_2528_: u8 = 0;
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662__overap_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2528_ = lean_usize_dec_lt(v_i_2519_, v_sz_2518_);
                if v___x_2528_ == 0 {
                    leanh::lean_dec_ref(v_snd_2516_);
                    leanh::lean_dec_ref(v_fst_2515_);
                    leanh::lean_dec_ref(v_snap_2514_);
                    leanh::lean_dec_ref(v_params_2513_);
                    v___x_2529_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2529_, 0, v_b_2520_);
                    return v___x_2529_;
                } else {
                    v___x_4662__overap_2530_ = lean_array_uget_borrowed(v_as_2517_, v_i_2519_);
                    leanh::lean_inc(v___x_4662__overap_2530_);
                    leanh::lean_inc_ref(v___y_2521_);
                    leanh::lean_inc_ref(v_snd_2516_);
                    leanh::lean_inc_ref(v_fst_2515_);
                    leanh::lean_inc_ref(v_snap_2514_);
                    leanh::lean_inc_ref(v_params_2513_);
                    v___x_2531_ = leanh::lean_apply_6(
                        v___x_4662__overap_2530_,
                        v_params_2513_,
                        v_snap_2514_,
                        v_fst_2515_,
                        v_snd_2516_,
                        v___y_2521_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_2531_) == 0 {
                        v_a_2532_ = leanh::lean_ctor_get(v___x_2531_, 0);
                        leanh::lean_inc(v_a_2532_);
                        leanh::lean_dec_ref_known(v___x_2531_, 1);
                        v___x_2533_ = l_Array_append___redArg(v_b_2520_, v_a_2532_);
                        leanh::lean_dec(v_a_2532_);
                        v_snd_2524_ = v___x_2533_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref_known(v___x_2531_, 1);
                        v_snd_2524_ = v_b_2520_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2525_ = 1usize;
                v___x_2526_ = lean_usize_add(v_i_2519_, v___x_2525_);
                v_i_2519_ = v___x_2526_;
                v_b_2520_ = v_snd_2524_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1___boxed(
    mut v_params_2534_: *mut leanh::LeanObject,
    mut v_snap_2535_: *mut leanh::LeanObject,
    mut v_fst_2536_: *mut leanh::LeanObject,
    mut v_snd_2537_: *mut leanh::LeanObject,
    mut v_as_2538_: *mut leanh::LeanObject,
    mut v_sz_2539_: *mut leanh::LeanObject,
    mut v_i_2540_: *mut leanh::LeanObject,
    mut v_b_2541_: *mut leanh::LeanObject,
    mut v___y_2542_: *mut leanh::LeanObject,
    mut v___y_2543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2544_: usize = 0;
    let mut v_i_boxed_2545_: usize = 0;
    let mut v_res_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2544_ = leanh::lean_unbox_usize(v_sz_2539_);
    leanh::lean_dec(v_sz_2539_);
    v_i_boxed_2545_ = leanh::lean_unbox_usize(v_i_2540_);
    leanh::lean_dec(v_i_2540_);
    v_res_2546_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_2534_, v_snap_2535_, v_fst_2536_, v_snd_2537_, v_as_2538_, v_sz_boxed_2544_, v_i_boxed_2545_, v_b_2541_, v___y_2542_);
    leanh::lean_dec_ref(v___y_2542_);
    leanh::lean_dec_ref(v_as_2538_);
    return v_res_2546_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__2;
    v___x_2551_ = leanh::lean_unsigned_to_nat(48);
    v___x_2552_ = leanh::lean_unsigned_to_nat(185);
    v___x_2553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__1;
    v___x_2554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__0;
    v___x_2555_ = l_mkPanicMessageWithDecl(
        v___x_2554_,
        v___x_2553_,
        v___x_2552_,
        v___x_2551_,
        v___x_2550_,
    );
    return v___x_2555_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(
    mut v___x_2556_: *mut leanh::LeanObject,
    mut v_params_2557_: *mut leanh::LeanObject,
    mut v_snap_2558_: *mut leanh::LeanObject,
    mut v_as_2559_: *mut leanh::LeanObject,
    mut v_sz_2560_: usize,
    mut v_i_2561_: usize,
    mut v_b_2562_: *mut leanh::LeanObject,
    mut v___y_2563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: usize = 0;
    let mut v___x_2568_: usize = 0;
    let mut v___y_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2577_: u8 = 0;
    let mut v___x_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2581_: u8 = 0;
    let mut v___x_2582_: u8 = 0;
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_onAnyCmd_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_onCmd_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2594_: usize = 0;
    let mut v___x_2595_: usize = 0;
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2602_: usize = 0;
    let mut v___x_2603_: usize = 0;
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2582_ = lean_usize_dec_lt(v_i_2561_, v_sz_2560_);
                if v___x_2582_ == 0 {
                    leanh::lean_dec_ref(v_snap_2558_);
                    leanh::lean_dec_ref(v_params_2557_);
                    v___x_2583_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2583_, 0, v_b_2562_);
                    return v___x_2583_;
                } else {
                    v_a_2584_ = lean_array_uget_borrowed(v_as_2559_, v_i_2561_);
                    v_snd_2585_ = leanh::lean_ctor_get(v_a_2584_, 1);
                    if leanh::lean_obj_tag(v_snd_2585_) == 1 {
                        v_i_2586_ = leanh::lean_ctor_get(v_snd_2585_, 0);
                        if leanh::lean_obj_tag(v_i_2586_) == 3 {
                            v_fst_2587_ = leanh::lean_ctor_get(v_a_2584_, 0);
                            v_i_2588_ = leanh::lean_ctor_get(v_i_2586_, 0);
                            v_onAnyCmd_2589_ = leanh::lean_ctor_get(v___x_2556_, 0);
                            v_onCmd_2590_ = leanh::lean_ctor_get(v___x_2556_, 1);
                            v_stx_2598_ = leanh::lean_ctor_get(v_i_2588_, 1);
                            leanh::lean_inc(v_stx_2598_);
                            v___x_2599_ = l_Lean_Syntax_getKind(v_stx_2598_);
                            v___x_2600_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_onCmd_2590_, v___x_2599_);
                            leanh::lean_dec(v___x_2599_);
                            if leanh::lean_obj_tag(v___x_2600_) == 1 {
                                v_val_2601_ = leanh::lean_ctor_get(v___x_2600_, 0);
                                leanh::lean_inc(v_val_2601_);
                                leanh::lean_dec_ref_known(v___x_2600_, 1);
                                v_sz_2602_ = lean_array_size(v_val_2601_);
                                v___x_2603_ = 0usize;
                                leanh::lean_inc_ref(v_snd_2585_);
                                leanh::lean_inc(v_fst_2587_);
                                leanh::lean_inc_ref(v_snap_2558_);
                                leanh::lean_inc_ref(v_params_2557_);
                                v___x_2604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_2557_, v_snap_2558_, v_fst_2587_, v_snd_2585_, v_val_2601_, v_sz_2602_, v___x_2603_, v_b_2562_, v___y_2563_);
                                leanh::lean_dec(v_val_2601_);
                                if leanh::lean_obj_tag(v___x_2604_) == 0 {
                                    v_a_2605_ = leanh::lean_ctor_get(v___x_2604_, 0);
                                    leanh::lean_inc(v_a_2605_);
                                    leanh::lean_dec_ref_known(v___x_2604_, 1);
                                    v_out_2592_ = v_a_2605_;
                                    v___y_2593_ = v___y_2563_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v_snap_2558_);
                                    leanh::lean_dec_ref(v_params_2557_);
                                    return v___x_2604_;
                                }
                            } else {
                                leanh::lean_dec(v___x_2600_);
                                v_out_2592_ = v_b_2562_;
                                v___y_2593_ = v___y_2563_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v___y_2571_ = v___y_2563_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_2571_ = v___y_2563_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2567_ = 1usize;
                v___x_2568_ = lean_usize_add(v_i_2561_, v___x_2567_);
                v_i_2561_ = v___x_2568_;
                v_b_2562_ = v_a_2566_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2572_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3);
                v___x_2573_ = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(
                    v___x_2572_,
                    v___y_2571_,
                );
                if leanh::lean_obj_tag(v___x_2573_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2573_, 1);
                    v_a_2566_ = v_b_2562_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_b_2562_);
                    leanh::lean_dec_ref(v_snap_2558_);
                    leanh::lean_dec_ref(v_params_2557_);
                    v_a_2574_ = leanh::lean_ctor_get(v___x_2573_, 0);
                    v_isSharedCheck_2581_ = (!leanh::lean_is_exclusive(v___x_2573_)) as u8;
                    if v_isSharedCheck_2581_ == 0 {
                        v___x_2576_ = v___x_2573_;
                        v_isShared_2577_ = v_isSharedCheck_2581_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2574_);
                        leanh::lean_dec(v___x_2573_);
                        v___x_2576_ = leanh::lean_box(0);
                        v_isShared_2577_ = v_isSharedCheck_2581_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2577_ == 0 {
                    v___x_2579_ = v___x_2576_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2580_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
                    v___x_2579_ = v_reuseFailAlloc_2580_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2579_;
            }
            5 => {
                v_sz_2594_ = lean_array_size(v_onAnyCmd_2589_);
                v___x_2595_ = 0usize;
                leanh::lean_inc_ref(v_snd_2585_);
                leanh::lean_inc(v_fst_2587_);
                leanh::lean_inc_ref(v_snap_2558_);
                leanh::lean_inc_ref(v_params_2557_);
                v___x_2596_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_2557_, v_snap_2558_, v_fst_2587_, v_snd_2585_, v_onAnyCmd_2589_, v_sz_2594_, v___x_2595_, v_out_2592_, v___y_2593_);
                if leanh::lean_obj_tag(v___x_2596_) == 0 {
                    v_a_2597_ = leanh::lean_ctor_get(v___x_2596_, 0);
                    leanh::lean_inc(v_a_2597_);
                    leanh::lean_dec_ref_known(v___x_2596_, 1);
                    v_a_2566_ = v_a_2597_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_snap_2558_);
                    leanh::lean_dec_ref(v_params_2557_);
                    return v___x_2596_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___boxed(
    mut v___x_2606_: *mut leanh::LeanObject,
    mut v_params_2607_: *mut leanh::LeanObject,
    mut v_snap_2608_: *mut leanh::LeanObject,
    mut v_as_2609_: *mut leanh::LeanObject,
    mut v_sz_2610_: *mut leanh::LeanObject,
    mut v_i_2611_: *mut leanh::LeanObject,
    mut v_b_2612_: *mut leanh::LeanObject,
    mut v___y_2613_: *mut leanh::LeanObject,
    mut v___y_2614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2615_: usize = 0;
    let mut v_i_boxed_2616_: usize = 0;
    let mut v_res_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2615_ = leanh::lean_unbox_usize(v_sz_2610_);
    leanh::lean_dec(v_sz_2610_);
    v_i_boxed_2616_ = leanh::lean_unbox_usize(v_i_2611_);
    leanh::lean_dec(v_i_2611_);
    v_res_2617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(v___x_2606_, v_params_2607_, v_snap_2608_, v_as_2609_, v_sz_boxed_2615_, v_i_boxed_2616_, v_b_2612_, v___y_2613_);
    leanh::lean_dec_ref(v___y_2613_);
    leanh::lean_dec_ref(v_as_2609_);
    leanh::lean_dec_ref(v___x_2606_);
    return v_res_2617_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(
    mut v_params_2618_: *mut leanh::LeanObject,
    mut v_snap_2619_: *mut leanh::LeanObject,
    mut v___x_2620_: *mut leanh::LeanObject,
    mut v_as_2621_: *mut leanh::LeanObject,
    mut v_sz_2622_: usize,
    mut v_i_2623_: usize,
    mut v_b_2624_: *mut leanh::LeanObject,
    mut v___y_2625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: usize = 0;
    let mut v___x_2630_: usize = 0;
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2639_: u8 = 0;
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2643_: u8 = 0;
    let mut v___x_2644_: u8 = 0;
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_onAnyCmd_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_onCmd_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2656_: usize = 0;
    let mut v___x_2657_: usize = 0;
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2664_: usize = 0;
    let mut v___x_2665_: usize = 0;
    let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2644_ = lean_usize_dec_lt(v_i_2623_, v_sz_2622_);
                if v___x_2644_ == 0 {
                    leanh::lean_dec_ref(v_snap_2619_);
                    leanh::lean_dec_ref(v_params_2618_);
                    v___x_2645_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2645_, 0, v_b_2624_);
                    return v___x_2645_;
                } else {
                    v_a_2646_ = lean_array_uget_borrowed(v_as_2621_, v_i_2623_);
                    v_snd_2647_ = leanh::lean_ctor_get(v_a_2646_, 1);
                    if leanh::lean_obj_tag(v_snd_2647_) == 1 {
                        v_i_2648_ = leanh::lean_ctor_get(v_snd_2647_, 0);
                        if leanh::lean_obj_tag(v_i_2648_) == 3 {
                            v_fst_2649_ = leanh::lean_ctor_get(v_a_2646_, 0);
                            v_i_2650_ = leanh::lean_ctor_get(v_i_2648_, 0);
                            v_onAnyCmd_2651_ = leanh::lean_ctor_get(v___x_2620_, 0);
                            v_onCmd_2652_ = leanh::lean_ctor_get(v___x_2620_, 1);
                            v_stx_2660_ = leanh::lean_ctor_get(v_i_2650_, 1);
                            leanh::lean_inc(v_stx_2660_);
                            v___x_2661_ = l_Lean_Syntax_getKind(v_stx_2660_);
                            v___x_2662_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_onCmd_2652_, v___x_2661_);
                            leanh::lean_dec(v___x_2661_);
                            if leanh::lean_obj_tag(v___x_2662_) == 1 {
                                v_val_2663_ = leanh::lean_ctor_get(v___x_2662_, 0);
                                leanh::lean_inc(v_val_2663_);
                                leanh::lean_dec_ref_known(v___x_2662_, 1);
                                v_sz_2664_ = lean_array_size(v_val_2663_);
                                v___x_2665_ = 0usize;
                                leanh::lean_inc_ref(v_snd_2647_);
                                leanh::lean_inc(v_fst_2649_);
                                leanh::lean_inc_ref(v_snap_2619_);
                                leanh::lean_inc_ref(v_params_2618_);
                                v___x_2666_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_2618_, v_snap_2619_, v_fst_2649_, v_snd_2647_, v_val_2663_, v_sz_2664_, v___x_2665_, v_b_2624_, v___y_2625_);
                                leanh::lean_dec(v_val_2663_);
                                if leanh::lean_obj_tag(v___x_2666_) == 0 {
                                    v_a_2667_ = leanh::lean_ctor_get(v___x_2666_, 0);
                                    leanh::lean_inc(v_a_2667_);
                                    leanh::lean_dec_ref_known(v___x_2666_, 1);
                                    v_out_2654_ = v_a_2667_;
                                    v___y_2655_ = v___y_2625_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v_snap_2619_);
                                    leanh::lean_dec_ref(v_params_2618_);
                                    return v___x_2666_;
                                }
                            } else {
                                leanh::lean_dec(v___x_2662_);
                                v_out_2654_ = v_b_2624_;
                                v___y_2655_ = v___y_2625_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v___y_2633_ = v___y_2625_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_2633_ = v___y_2625_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2629_ = 1usize;
                v___x_2630_ = lean_usize_add(v_i_2623_, v___x_2629_);
                v___x_2631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(v___x_2620_, v_params_2618_, v_snap_2619_, v_as_2621_, v_sz_2622_, v___x_2630_, v_a_2628_, v___y_2625_);
                return v___x_2631_;
            }
            2 => {
                v___x_2634_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3);
                v___x_2635_ = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(
                    v___x_2634_,
                    v___y_2633_,
                );
                if leanh::lean_obj_tag(v___x_2635_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2635_, 1);
                    v_a_2628_ = v_b_2624_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_b_2624_);
                    leanh::lean_dec_ref(v_snap_2619_);
                    leanh::lean_dec_ref(v_params_2618_);
                    v_a_2636_ = leanh::lean_ctor_get(v___x_2635_, 0);
                    v_isSharedCheck_2643_ = (!leanh::lean_is_exclusive(v___x_2635_)) as u8;
                    if v_isSharedCheck_2643_ == 0 {
                        v___x_2638_ = v___x_2635_;
                        v_isShared_2639_ = v_isSharedCheck_2643_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2636_);
                        leanh::lean_dec(v___x_2635_);
                        v___x_2638_ = leanh::lean_box(0);
                        v_isShared_2639_ = v_isSharedCheck_2643_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2639_ == 0 {
                    v___x_2641_ = v___x_2638_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2642_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
                    v___x_2641_ = v_reuseFailAlloc_2642_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2641_;
            }
            5 => {
                v_sz_2656_ = lean_array_size(v_onAnyCmd_2651_);
                v___x_2657_ = 0usize;
                leanh::lean_inc_ref(v_snd_2647_);
                leanh::lean_inc(v_fst_2649_);
                leanh::lean_inc_ref(v_snap_2619_);
                leanh::lean_inc_ref(v_params_2618_);
                v___x_2658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_2618_, v_snap_2619_, v_fst_2649_, v_snd_2647_, v_onAnyCmd_2651_, v_sz_2656_, v___x_2657_, v_out_2654_, v___y_2655_);
                if leanh::lean_obj_tag(v___x_2658_) == 0 {
                    v_a_2659_ = leanh::lean_ctor_get(v___x_2658_, 0);
                    leanh::lean_inc(v_a_2659_);
                    leanh::lean_dec_ref_known(v___x_2658_, 1);
                    v_a_2628_ = v_a_2659_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_snap_2619_);
                    leanh::lean_dec_ref(v_params_2618_);
                    return v___x_2658_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2___boxed(
    mut v_params_2668_: *mut leanh::LeanObject,
    mut v_snap_2669_: *mut leanh::LeanObject,
    mut v___x_2670_: *mut leanh::LeanObject,
    mut v_as_2671_: *mut leanh::LeanObject,
    mut v_sz_2672_: *mut leanh::LeanObject,
    mut v_i_2673_: *mut leanh::LeanObject,
    mut v_b_2674_: *mut leanh::LeanObject,
    mut v___y_2675_: *mut leanh::LeanObject,
    mut v___y_2676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2677_: usize = 0;
    let mut v_i_boxed_2678_: usize = 0;
    let mut v_res_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2677_ = leanh::lean_unbox_usize(v_sz_2672_);
    leanh::lean_dec(v_sz_2672_);
    v_i_boxed_2678_ = leanh::lean_unbox_usize(v_i_2673_);
    leanh::lean_dec(v_i_2673_);
    v_res_2679_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(v_params_2668_, v_snap_2669_, v___x_2670_, v_as_2671_, v_sz_boxed_2677_, v_i_boxed_2678_, v_b_2674_, v___y_2675_);
    leanh::lean_dec_ref(v___y_2675_);
    leanh::lean_dec_ref(v_as_2671_);
    leanh::lean_dec_ref(v___x_2670_);
    return v_res_2679_;
}
pub unsafe fn _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2680_ = l_Array_instInhabited(leanh::lean_box(0));
    return v___x_2680_;
}
pub unsafe fn _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2681_ = l_Lean_CodeAction_instInhabitedCommandCodeActions_default;
    v___x_2682_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_CodeAction_cmdCodeActionProvider___closed__0),
        core::ptr::addr_of_mut!(l_Lean_CodeAction_cmdCodeActionProvider___closed__0_once),
        _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__0,
    );
    v___x_2683_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2683_, 0, v___x_2682_);
    leanh::lean_ctor_set(v___x_2683_, 1, v___x_2681_);
    return v___x_2683_;
}
pub unsafe fn l_Lean_CodeAction_cmdCodeActionProvider(
    mut v_params_2686_: *mut leanh::LeanObject,
    mut v_snap_2687_: *mut leanh::LeanObject,
    mut v_a_2688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEditableDocumentCore_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_meta_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_end_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2712_: usize = 0;
    let mut v___x_2713_: usize = 0;
    let mut v___x_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2690_ =
        l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(
            v_a_2688_,
        );
    v_a_2691_ = leanh::lean_ctor_get(v___x_2690_, 0);
    leanh::lean_inc(v_a_2691_);
    leanh::lean_dec_ref(v___x_2690_);
    v_toEditableDocumentCore_2692_ = leanh::lean_ctor_get(v_a_2691_, 0);
    leanh::lean_inc_ref(v_toEditableDocumentCore_2692_);
    leanh::lean_dec(v_a_2691_);
    v_meta_2693_ = leanh::lean_ctor_get(v_toEditableDocumentCore_2692_, 0);
    leanh::lean_inc_ref(v_meta_2693_);
    leanh::lean_dec_ref(v_toEditableDocumentCore_2692_);
    v_range_2694_ = leanh::lean_ctor_get(v_params_2686_, 3);
    v_text_2695_ = leanh::lean_ctor_get(v_meta_2693_, 3);
    leanh::lean_inc_ref(v_text_2695_);
    leanh::lean_dec_ref(v_meta_2693_);
    v_start_2696_ = leanh::lean_ctor_get(v_range_2694_, 0);
    v_end_2697_ = leanh::lean_ctor_get(v_range_2694_, 1);
    v___x_2698_ = l_Lean_CodeAction_cmdCodeActionExt;
    v_toEnvExtension_2699_ = leanh::lean_ctor_get(v___x_2698_, 0);
    v_asyncMode_2700_ = leanh::lean_ctor_get(v_toEnvExtension_2699_, 2);
    v___x_2701_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_CodeAction_cmdCodeActionProvider___closed__1),
        core::ptr::addr_of_mut!(l_Lean_CodeAction_cmdCodeActionProvider___closed__1_once),
        _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__1,
    );
    v___x_2702_ = l_Lean_Server_Snapshots_Snapshot_env(v_snap_2687_);
    v___x_2703_ = leanh::lean_box(0);
    v___x_2704_ = l_Lean_PersistentEnvExtension_getState___redArg(
        v___x_2701_,
        v___x_2698_,
        v___x_2702_,
        v_asyncMode_2700_,
        v___x_2703_,
    );
    v_snd_2705_ = leanh::lean_ctor_get(v___x_2704_, 1);
    leanh::lean_inc(v_snd_2705_);
    leanh::lean_dec(v___x_2704_);
    leanh::lean_inc_ref(v_start_2696_);
    v___x_2706_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_2695_, v_start_2696_);
    leanh::lean_inc_ref(v_end_2697_);
    v___x_2707_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_2695_, v_end_2697_);
    leanh::lean_dec_ref(v_text_2695_);
    v___f_2708_ = leanh::lean_alloc_closure(
        l_Lean_CodeAction_cmdCodeActionProvider___lam__0___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_2708_, 0, v___x_2707_);
    leanh::lean_closure_set(v___f_2708_, 1, v___x_2706_);
    v___x_2709_ = l_Lean_CodeAction_cmdCodeActionProvider___closed__2;
    leanh::lean_inc_ref(v_snap_2687_);
    v___x_2710_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_snap_2687_);
    v___x_2711_ = l_Lean_Elab_InfoTree_foldInfoTree___redArg(v___x_2709_, v___f_2708_, v___x_2710_);
    v_sz_2712_ = lean_array_size(v___x_2711_);
    v___x_2713_ = 0usize;
    v___x_2714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(v_params_2686_, v_snap_2687_, v_snd_2705_, v___x_2711_, v_sz_2712_, v___x_2713_, v___x_2709_, v_a_2688_);
    leanh::lean_dec(v___x_2711_);
    leanh::lean_dec(v_snd_2705_);
    return v___x_2714_;
}
pub unsafe fn l_Lean_CodeAction_cmdCodeActionProvider___boxed(
    mut v_params_2715_: *mut leanh::LeanObject,
    mut v_snap_2716_: *mut leanh::LeanObject,
    mut v_a_2717_: *mut leanh::LeanObject,
    mut v_a_2718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2719_ = l_Lean_CodeAction_cmdCodeActionProvider(v_params_2715_, v_snap_2716_, v_a_2717_);
    leanh::lean_dec_ref(v_a_2717_);
    return v_res_2719_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1()
-> *mut leanh::LeanObject {
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2726_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1;
    v___x_2727_ = leanh::lean_alloc_closure(
        l_Lean_CodeAction_cmdCodeActionProvider___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_2728_ = l_Lean_Server_addBuiltinCodeActionProvider(v___x_2726_, v___x_2727_);
    return v___x_2728_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___boxed(
    mut v_a_2729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2730_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1();
    return v_res_2730_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_CodeActions_Provider(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Producers_Range(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators_StepSize(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinTerm(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinNotation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_CodeActions_Attr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_CodeActions_Provider(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_CodeActions_Provider(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Producers_Range(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Combinators_StepSize(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_BuiltinTerm(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_BuiltinNotation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Server_CodeActions_Attr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_CodeActions_Provider(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_CodeActions_Provider(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Server_CodeActions_Provider(builtin);
}
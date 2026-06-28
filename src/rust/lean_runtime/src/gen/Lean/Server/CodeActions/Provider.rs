// Lean compiler output
// Module: Lean.Server.CodeActions.Provider
// Imports: Std.Data.Iterators.Producers.Range Std.Data.Iterators.Combinators.StepSize Lean.Elab.BuiltinTerm Lean.Elab.BuiltinNotation Lean.Server.CodeActions.Attr
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_instInhabited};
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_getTailInfo;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Syntax_getArg, l_Lean_Syntax_getKind,
    l_Lean_Syntax_getNumArgs, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul,
    lean_nat_sub, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value:
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
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__1_value:
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
    m_data: [69, 108, 97, 98, 0],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__2_value:
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
    m_data: [84, 101, 114, 109, 0],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__3_value:
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
    m_data: [101, 108, 97, 98, 72, 111, 108, 101, 0],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value_aux_1:
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
            l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        11510100434945111860 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value_aux_2:
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
            l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        7892421401833366012 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value:
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
            l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__3_value)
            as *mut crate::leanh::LeanObject,
        11340967426965104390 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__5_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value_aux_1:
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
            l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        11510100434945111860 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value_aux_2:
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
            l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        7892421401833366012 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value:
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
            l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__5_value)
            as *mut crate::leanh::LeanObject,
        8403575154271798838 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__7_value:
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
    m_data: [101, 108, 97, 98, 83, 111, 114, 114, 121, 0],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value_aux_1:
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
            l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        11510100434945111860 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value_aux_2:
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
            l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        7892421401833366012 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value:
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
            l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__7_value)
            as *mut crate::leanh::LeanObject,
        6267058134344042428 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__9_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__10_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__9_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__11_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_CodeAction_holeCodeActionProvider___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_CodeAction_holeCodeActionProvider___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_CodeAction_holeCodeActionProvider___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_CodeAction_holeCodeActionProvider___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_CodeAction_holeCodeActionProvider___closed__3_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__1_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [104, 111, 108, 101, 67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 80, 114, 111, 118, 105, 100, 101, 114, 0]};
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__0_value) as *mut crate::leanh::LeanObject,1630946840184265901 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__1_value) as *mut crate::leanh::LeanObject,2550652980631965832 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__2_value) as *mut crate::leanh::LeanObject,8504843326314613972 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__4_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__5_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 66, 114, 97, 99, 107, 101, 116, 101, 100, 0]};
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__5_value) as *mut crate::leanh::LeanObject,10468396288943149198 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__0_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 115, 46, 80, 114, 111, 118, 105, 100, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__1_value: crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [76, 101, 97, 110, 46, 67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 46, 99, 109, 100, 67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 80, 114, 111, 118, 105, 100, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__2_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_CodeAction_cmdCodeActionProvider___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_CodeAction_cmdCodeActionProvider___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_CodeAction_cmdCodeActionProvider___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_CodeAction_cmdCodeActionProvider___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_CodeAction_cmdCodeActionProvider___closed__2_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_CodeAction_cmdCodeActionProvider___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_cmdCodeActionProvider___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__0_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [99, 109, 100, 67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 80, 114, 111, 118, 105, 100, 101, 114, 0]};
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__0_value) as *mut crate::leanh::LeanObject,1630946840184265901 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__0_value) as *mut crate::leanh::LeanObject,890343562233056736 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(
    mut v___y_1366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_doc_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_doc_1368_ = crate::leanh::lean_ctor_get(v___y_1366_, 1);
    crate::leanh::lean_inc_ref(v_doc_1368_);
    v___x_1369_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1369_, 0, v_doc_1368_);
    return v___x_1369_;
}
pub unsafe fn l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0___boxed(
    mut v___y_1370_: *mut crate::leanh::LeanObject,
    mut v___y_1371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1372_ =
        l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(
            v___y_1370_,
        );
    crate::leanh::lean_dec_ref(v___y_1370_);
    return v_res_1372_;
}
pub unsafe fn l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1(
    mut v_a_1373_: *mut crate::leanh::LeanObject,
    mut v_x_1374_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1375_: u8 = 0;
    let mut v_head_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1374_) == 0 {
                    v___x_1375_ = 0;
                    return v___x_1375_;
                } else {
                    v_head_1376_ = crate::leanh::lean_ctor_get(v_x_1374_, 0);
                    v_tail_1377_ = crate::leanh::lean_ctor_get(v_x_1374_, 1);
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
    mut v_a_1380_: *mut crate::leanh::LeanObject,
    mut v_x_1381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1382_: u8 = 0;
    let mut v_r_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1382_ =
        l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1(v_a_1380_, v_x_1381_);
    crate::leanh::lean_dec(v_x_1381_);
    crate::leanh::lean_dec(v_a_1380_);
    v_r_1383_ = crate::leanh::lean_box((v_res_1382_) as usize);
    return v_r_1383_;
}
pub unsafe fn l_Lean_CodeAction_holeCodeActionProvider___lam__0(
    mut v___x_1414_: *mut crate::leanh::LeanObject,
    mut v___x_1415_: *mut crate::leanh::LeanObject,
    mut v_ctx_1416_: *mut crate::leanh::LeanObject,
    mut v_info_1417_: *mut crate::leanh::LeanObject,
    mut v_result_1418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1421_: u8 = 0;
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toElabInfo_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elaborator_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: u8 = 0;
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: u8 = 0;
    let mut v___x_1434_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_info_1417_) == 1 {
                    v_i_1419_ = crate::leanh::lean_ctor_get(v_info_1417_, 0);
                    v_toElabInfo_1424_ = crate::leanh::lean_ctor_get(v_i_1419_, 0);
                    v_elaborator_1425_ = crate::leanh::lean_ctor_get(v_toElabInfo_1424_, 0);
                    v_stx_1426_ = crate::leanh::lean_ctor_get(v_toElabInfo_1424_, 1);
                    v___x_1427_ = l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__11;
                    v___x_1428_ =
                        l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1(
                            v_elaborator_1425_,
                            v___x_1427_,
                        );
                    if v___x_1428_ == 0 {
                        crate::leanh::lean_dec_ref(v_ctx_1416_);
                        return v_result_1418_;
                    } else {
                        v___x_1429_ = l_Lean_Syntax_getPos_x3f(v_stx_1426_, v___x_1428_);
                        if crate::leanh::lean_obj_tag(v___x_1429_) == 1 {
                            v_val_1430_ = crate::leanh::lean_ctor_get(v___x_1429_, 0);
                            crate::leanh::lean_inc(v_val_1430_);
                            crate::leanh::lean_dec_ref_known(v___x_1429_, 1);
                            v___x_1431_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1426_, v___x_1428_);
                            if crate::leanh::lean_obj_tag(v___x_1431_) == 1 {
                                v_val_1432_ = crate::leanh::lean_ctor_get(v___x_1431_, 0);
                                crate::leanh::lean_inc(v_val_1432_);
                                crate::leanh::lean_dec_ref_known(v___x_1431_, 1);
                                v___x_1433_ = lean_nat_dec_le(v_val_1430_, v___x_1414_);
                                crate::leanh::lean_dec(v_val_1430_);
                                if v___x_1433_ == 0 {
                                    crate::leanh::lean_dec(v_val_1432_);
                                    v___y_1421_ = v___x_1433_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_1434_ = lean_nat_dec_le(v___x_1415_, v_val_1432_);
                                    crate::leanh::lean_dec(v_val_1432_);
                                    v___y_1421_ = v___x_1434_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_1431_);
                                crate::leanh::lean_dec(v_val_1430_);
                                crate::leanh::lean_dec_ref(v_ctx_1416_);
                                return v_result_1418_;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_1429_);
                            crate::leanh::lean_dec_ref(v_ctx_1416_);
                            return v_result_1418_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_ctx_1416_);
                    return v_result_1418_;
                }
            }
            1 => {
                if v___y_1421_ == 0 {
                    crate::leanh::lean_dec_ref(v_ctx_1416_);
                    return v_result_1418_;
                } else {
                    crate::leanh::lean_inc_ref(v_i_1419_);
                    v___x_1422_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1422_, 0, v_ctx_1416_);
                    crate::leanh::lean_ctor_set(v___x_1422_, 1, v_i_1419_);
                    v___x_1423_ = lean_array_push(v_result_1418_, v___x_1422_);
                    return v___x_1423_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_CodeAction_holeCodeActionProvider___lam__0___boxed(
    mut v___x_1435_: *mut crate::leanh::LeanObject,
    mut v___x_1436_: *mut crate::leanh::LeanObject,
    mut v_ctx_1437_: *mut crate::leanh::LeanObject,
    mut v_info_1438_: *mut crate::leanh::LeanObject,
    mut v_result_1439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1440_ = l_Lean_CodeAction_holeCodeActionProvider___lam__0(
        v___x_1435_,
        v___x_1436_,
        v_ctx_1437_,
        v_info_1438_,
        v_result_1439_,
    );
    crate::leanh::lean_dec_ref(v_info_1438_);
    crate::leanh::lean_dec(v___x_1436_);
    crate::leanh::lean_dec(v___x_1435_);
    return v_res_1440_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(
    mut v_params_1441_: *mut crate::leanh::LeanObject,
    mut v_snap_1442_: *mut crate::leanh::LeanObject,
    mut v_fst_1443_: *mut crate::leanh::LeanObject,
    mut v_snd_1444_: *mut crate::leanh::LeanObject,
    mut v_as_1445_: *mut crate::leanh::LeanObject,
    mut v_i_1446_: usize,
    mut v_stop_1447_: usize,
    mut v_b_1448_: *mut crate::leanh::LeanObject,
    mut v___y_1449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: usize = 0;
    let mut v___x_1454_: usize = 0;
    let mut v___x_1456_: u8 = 0;
    let mut v___x_1833__overap_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1456_ = lean_usize_dec_eq(v_i_1446_, v_stop_1447_);
                if v___x_1456_ == 0 {
                    v___x_1833__overap_1457_ = lean_array_uget_borrowed(v_as_1445_, v_i_1446_);
                    crate::leanh::lean_inc(v___x_1833__overap_1457_);
                    crate::leanh::lean_inc_ref(v___y_1449_);
                    crate::leanh::lean_inc_ref(v_snd_1444_);
                    crate::leanh::lean_inc_ref(v_fst_1443_);
                    crate::leanh::lean_inc_ref(v_snap_1442_);
                    crate::leanh::lean_inc_ref(v_params_1441_);
                    v___x_1458_ = crate::leanh::lean_apply_6(
                        v___x_1833__overap_1457_,
                        v_params_1441_,
                        v_snap_1442_,
                        v_fst_1443_,
                        v_snd_1444_,
                        v___y_1449_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_1458_) == 0 {
                        v_a_1459_ = crate::leanh::lean_ctor_get(v___x_1458_, 0);
                        crate::leanh::lean_inc(v_a_1459_);
                        crate::leanh::lean_dec_ref_known(v___x_1458_, 1);
                        v___x_1460_ = l_Array_append___redArg(v_b_1448_, v_a_1459_);
                        crate::leanh::lean_dec(v_a_1459_);
                        v_a_1452_ = v___x_1460_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_1448_);
                        if crate::leanh::lean_obj_tag(v___x_1458_) == 0 {
                            v_a_1461_ = crate::leanh::lean_ctor_get(v___x_1458_, 0);
                            crate::leanh::lean_inc(v_a_1461_);
                            crate::leanh::lean_dec_ref_known(v___x_1458_, 1);
                            v_a_1452_ = v_a_1461_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_snd_1444_);
                            crate::leanh::lean_dec_ref(v_fst_1443_);
                            crate::leanh::lean_dec_ref(v_snap_1442_);
                            crate::leanh::lean_dec_ref(v_params_1441_);
                            return v___x_1458_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_snd_1444_);
                    crate::leanh::lean_dec_ref(v_fst_1443_);
                    crate::leanh::lean_dec_ref(v_snap_1442_);
                    crate::leanh::lean_dec_ref(v_params_1441_);
                    v___x_1462_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1462_, 0, v_b_1448_);
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
    mut v_params_1463_: *mut crate::leanh::LeanObject,
    mut v_snap_1464_: *mut crate::leanh::LeanObject,
    mut v_fst_1465_: *mut crate::leanh::LeanObject,
    mut v_snd_1466_: *mut crate::leanh::LeanObject,
    mut v_as_1467_: *mut crate::leanh::LeanObject,
    mut v_i_1468_: *mut crate::leanh::LeanObject,
    mut v_stop_1469_: *mut crate::leanh::LeanObject,
    mut v_b_1470_: *mut crate::leanh::LeanObject,
    mut v___y_1471_: *mut crate::leanh::LeanObject,
    mut v___y_1472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1473_: usize = 0;
    let mut v_stop_boxed_1474_: usize = 0;
    let mut v_res_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1473_ = crate::leanh::lean_unbox_usize(v_i_1468_);
    crate::leanh::lean_dec(v_i_1468_);
    v_stop_boxed_1474_ = crate::leanh::lean_unbox_usize(v_stop_1469_);
    crate::leanh::lean_dec(v_stop_1469_);
    v_res_1475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(v_params_1463_, v_snap_1464_, v_fst_1465_, v_snd_1466_, v_as_1467_, v_i_boxed_1473_, v_stop_boxed_1474_, v_b_1470_, v___y_1471_);
    crate::leanh::lean_dec_ref(v___y_1471_);
    crate::leanh::lean_dec_ref(v_as_1467_);
    return v_res_1475_;
}
pub unsafe fn _init_l_Lean_CodeAction_holeCodeActionProvider___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1478_ = l_Array_instInhabited(crate::leanh::lean_box(0));
    return v___x_1478_;
}
pub unsafe fn _init_l_Lean_CodeAction_holeCodeActionProvider___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1479_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_CodeAction_holeCodeActionProvider___closed__1),
        core::ptr::addr_of_mut!(l_Lean_CodeAction_holeCodeActionProvider___closed__1_once),
        _init_l_Lean_CodeAction_holeCodeActionProvider___closed__1,
    );
    v___x_1480_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1480_, 0, v___x_1479_);
    crate::leanh::lean_ctor_set(v___x_1480_, 1, v___x_1479_);
    return v___x_1480_;
}
pub unsafe fn l_Lean_CodeAction_holeCodeActionProvider(
    mut v_params_1483_: *mut crate::leanh::LeanObject,
    mut v_snap_1484_: *mut crate::leanh::LeanObject,
    mut v_a_1485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1491_: u8 = 0;
    let mut v_toEditableDocumentCore_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_meta_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_end_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: u8 = 0;
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: u8 = 0;
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: u8 = 0;
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: usize = 0;
    let mut v___x_1533_: usize = 0;
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: usize = 0;
    let mut v___x_1536_: usize = 0;
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1538_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1487_ = l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(v_a_1485_);
                v_a_1488_ = crate::leanh::lean_ctor_get(v___x_1487_, 0);
                v_isSharedCheck_1538_ = (!crate::leanh::lean_is_exclusive(v___x_1487_)) as u8;
                if v_isSharedCheck_1538_ == 0 {
                    v___x_1490_ = v___x_1487_;
                    v_isShared_1491_ = v_isSharedCheck_1538_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1488_);
                    crate::leanh::lean_dec(v___x_1487_);
                    v___x_1490_ = crate::leanh::lean_box(0);
                    v_isShared_1491_ = v_isSharedCheck_1538_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toEditableDocumentCore_1492_ = crate::leanh::lean_ctor_get(v_a_1488_, 0);
                crate::leanh::lean_inc_ref(v_toEditableDocumentCore_1492_);
                crate::leanh::lean_dec(v_a_1488_);
                v_meta_1493_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_1492_, 0);
                crate::leanh::lean_inc_ref(v_meta_1493_);
                crate::leanh::lean_dec_ref(v_toEditableDocumentCore_1492_);
                v_range_1494_ = crate::leanh::lean_ctor_get(v_params_1483_, 3);
                v_text_1495_ = crate::leanh::lean_ctor_get(v_meta_1493_, 3);
                crate::leanh::lean_inc_ref(v_text_1495_);
                crate::leanh::lean_dec_ref(v_meta_1493_);
                v_start_1496_ = crate::leanh::lean_ctor_get(v_range_1494_, 0);
                v_end_1497_ = crate::leanh::lean_ctor_get(v_range_1494_, 1);
                crate::leanh::lean_inc_ref(v_start_1496_);
                v___x_1498_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1495_, v_start_1496_);
                crate::leanh::lean_inc_ref(v_end_1497_);
                v___x_1499_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1495_, v_end_1497_);
                crate::leanh::lean_dec_ref(v_text_1495_);
                v___f_1500_ = crate::leanh::lean_alloc_closure(
                    l_Lean_CodeAction_holeCodeActionProvider___lam__0___boxed
                        as *mut core::ffi::c_void,
                    5,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_1500_, 0, v___x_1499_);
                crate::leanh::lean_closure_set(v___f_1500_, 1, v___x_1498_);
                v___x_1501_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1502_ = l_Lean_CodeAction_holeCodeActionProvider___closed__0;
                crate::leanh::lean_inc_ref(v_snap_1484_);
                v___x_1503_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_snap_1484_);
                v___x_1504_ =
                    l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_1500_, v___x_1502_, v___x_1503_);
                v___x_1505_ = lean_array_get_size(v___x_1504_);
                v___x_1506_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1507_ = lean_nat_dec_eq(v___x_1505_, v___x_1506_);
                if v___x_1507_ == 0 {
                    crate::leanh::lean_dec(v___x_1504_);
                    crate::leanh::lean_dec_ref(v_snap_1484_);
                    crate::leanh::lean_dec_ref(v_params_1483_);
                    if v_isShared_1491_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1490_, 0, v___x_1502_);
                        v___x_1509_ = v___x_1490_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1510_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1502_);
                        v___x_1509_ = v_reuseFailAlloc_1510_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1511_ = lean_array_fget(v___x_1504_, v___x_1501_);
                    crate::leanh::lean_dec(v___x_1504_);
                    v_fst_1512_ = crate::leanh::lean_ctor_get(v___x_1511_, 0);
                    crate::leanh::lean_inc(v_fst_1512_);
                    v_snd_1513_ = crate::leanh::lean_ctor_get(v___x_1511_, 1);
                    crate::leanh::lean_inc(v_snd_1513_);
                    crate::leanh::lean_dec(v___x_1511_);
                    v___x_1514_ = l_Lean_CodeAction_holeCodeActionExt;
                    v_toEnvExtension_1515_ = crate::leanh::lean_ctor_get(v___x_1514_, 0);
                    v_asyncMode_1516_ = crate::leanh::lean_ctor_get(v_toEnvExtension_1515_, 2);
                    v___x_1517_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_CodeAction_holeCodeActionProvider___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_CodeAction_holeCodeActionProvider___closed__2_once
                        ),
                        _init_l_Lean_CodeAction_holeCodeActionProvider___closed__2,
                    );
                    v___x_1518_ = l_Lean_Server_Snapshots_Snapshot_env(v_snap_1484_);
                    v___x_1519_ = crate::leanh::lean_box(0);
                    v___x_1520_ = l_Lean_PersistentEnvExtension_getState___redArg(
                        v___x_1517_,
                        v___x_1514_,
                        v___x_1518_,
                        v_asyncMode_1516_,
                        v___x_1519_,
                    );
                    v_snd_1521_ = crate::leanh::lean_ctor_get(v___x_1520_, 1);
                    crate::leanh::lean_inc(v_snd_1521_);
                    crate::leanh::lean_dec(v___x_1520_);
                    v___x_1522_ = l_Lean_CodeAction_holeCodeActionProvider___closed__3;
                    v___x_1523_ = lean_array_get_size(v_snd_1521_);
                    v___x_1524_ = lean_nat_dec_lt(v___x_1501_, v___x_1523_);
                    if v___x_1524_ == 0 {
                        crate::leanh::lean_dec(v_snd_1521_);
                        crate::leanh::lean_dec(v_snd_1513_);
                        crate::leanh::lean_dec(v_fst_1512_);
                        crate::leanh::lean_dec_ref(v_snap_1484_);
                        crate::leanh::lean_dec_ref(v_params_1483_);
                        if v_isShared_1491_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1490_, 0, v___x_1522_);
                            v___x_1526_ = v___x_1490_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1527_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1522_);
                            v___x_1526_ = v_reuseFailAlloc_1527_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1528_ = lean_nat_dec_le(v___x_1523_, v___x_1523_);
                        if v___x_1528_ == 0 {
                            if v___x_1524_ == 0 {
                                crate::leanh::lean_dec(v_snd_1521_);
                                crate::leanh::lean_dec(v_snd_1513_);
                                crate::leanh::lean_dec(v_fst_1512_);
                                crate::leanh::lean_dec_ref(v_snap_1484_);
                                crate::leanh::lean_dec_ref(v_params_1483_);
                                if v_isShared_1491_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1490_, 0, v___x_1522_);
                                    v___x_1530_ = v___x_1490_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1531_ =
                                        crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1531_,
                                        0,
                                        v___x_1522_,
                                    );
                                    v___x_1530_ = v_reuseFailAlloc_1531_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_1490_);
                                v___x_1532_ = 0usize;
                                v___x_1533_ = lean_usize_of_nat(v___x_1523_);
                                v___x_1534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(v_params_1483_, v_snap_1484_, v_fst_1512_, v_snd_1513_, v_snd_1521_, v___x_1532_, v___x_1533_, v___x_1522_, v_a_1485_);
                                crate::leanh::lean_dec(v_snd_1521_);
                                return v___x_1534_;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1490_);
                            v___x_1535_ = 0usize;
                            v___x_1536_ = lean_usize_of_nat(v___x_1523_);
                            v___x_1537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(v_params_1483_, v_snap_1484_, v_fst_1512_, v_snd_1513_, v_snd_1521_, v___x_1535_, v___x_1536_, v___x_1522_, v_a_1485_);
                            crate::leanh::lean_dec(v_snd_1521_);
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
    mut v_params_1539_: *mut crate::leanh::LeanObject,
    mut v_snap_1540_: *mut crate::leanh::LeanObject,
    mut v_a_1541_: *mut crate::leanh::LeanObject,
    mut v_a_1542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1543_ = l_Lean_CodeAction_holeCodeActionProvider(v_params_1539_, v_snap_1540_, v_a_1541_);
    crate::leanh::lean_dec_ref(v_a_1541_);
    return v_res_1543_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1551_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2;
    v___x_1552_ = crate::leanh::lean_alloc_closure(
        l_Lean_CodeAction_holeCodeActionProvider___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_1553_ = l_Lean_Server_addBuiltinCodeActionProvider(v___x_1551_, v___x_1552_);
    return v___x_1553_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___boxed(
    mut v_a_1554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1555_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1();
    return v_res_1555_;
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_ctorIdx(
    mut v_x_1556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1556_) == 0 {
        let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1557_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_1557_;
    } else {
        let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1558_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_1558_;
    }
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_ctorIdx___boxed(
    mut v_x_1559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1560_ = l_Lean_CodeAction_FindTacticResult_ctorIdx(v_x_1559_);
    crate::leanh::lean_dec_ref(v_x_1559_);
    return v_res_1560_;
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(
    mut v_t_1561_: *mut crate::leanh::LeanObject,
    mut v_k_1562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_1561_) == 0 {
        let mut v_a_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1563_ = crate::leanh::lean_ctor_get(v_t_1561_, 0);
        crate::leanh::lean_inc(v_a_1563_);
        crate::leanh::lean_dec_ref_known(v_t_1561_, 1);
        v___x_1564_ = crate::leanh::lean_apply_1(v_k_1562_, v_a_1563_);
        return v___x_1564_;
    } else {
        let mut v_preferred_1565_: u8 = 0;
        let mut v_insertIdx_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_preferred_1565_ = crate::leanh::lean_ctor_get_uint8(
            v_t_1561_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        );
        v_insertIdx_1566_ = crate::leanh::lean_ctor_get(v_t_1561_, 0);
        crate::leanh::lean_inc(v_insertIdx_1566_);
        v_a_1567_ = crate::leanh::lean_ctor_get(v_t_1561_, 1);
        crate::leanh::lean_inc(v_a_1567_);
        crate::leanh::lean_dec_ref_known(v_t_1561_, 2);
        v___x_1568_ = crate::leanh::lean_box((v_preferred_1565_) as usize);
        v___x_1569_ =
            crate::leanh::lean_apply_3(v_k_1562_, v___x_1568_, v_insertIdx_1566_, v_a_1567_);
        return v___x_1569_;
    }
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_ctorElim(
    mut v_motive_1570_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1571_: *mut crate::leanh::LeanObject,
    mut v_t_1572_: *mut crate::leanh::LeanObject,
    mut v_h_1573_: *mut crate::leanh::LeanObject,
    mut v_k_1574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1575_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_1572_, v_k_1574_);
    return v___x_1575_;
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_ctorElim___boxed(
    mut v_motive_1576_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1577_: *mut crate::leanh::LeanObject,
    mut v_t_1578_: *mut crate::leanh::LeanObject,
    mut v_h_1579_: *mut crate::leanh::LeanObject,
    mut v_k_1580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1581_ = l_Lean_CodeAction_FindTacticResult_ctorElim(
        v_motive_1576_,
        v_ctorIdx_1577_,
        v_t_1578_,
        v_h_1579_,
        v_k_1580_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1577_);
    return v_res_1581_;
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_tactic_elim___redArg(
    mut v_t_1582_: *mut crate::leanh::LeanObject,
    mut v_tactic_1583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1584_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_1582_, v_tactic_1583_);
    return v___x_1584_;
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_tactic_elim(
    mut v_motive_1585_: *mut crate::leanh::LeanObject,
    mut v_t_1586_: *mut crate::leanh::LeanObject,
    mut v_h_1587_: *mut crate::leanh::LeanObject,
    mut v_tactic_1588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1589_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_1586_, v_tactic_1588_);
    return v___x_1589_;
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_tacticSeq_elim___redArg(
    mut v_t_1590_: *mut crate::leanh::LeanObject,
    mut v_tacticSeq_1591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1592_ =
        l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_1590_, v_tacticSeq_1591_);
    return v___x_1592_;
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_tacticSeq_elim(
    mut v_motive_1593_: *mut crate::leanh::LeanObject,
    mut v_t_1594_: *mut crate::leanh::LeanObject,
    mut v_h_1595_: *mut crate::leanh::LeanObject,
    mut v_tacticSeq_1596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1597_ =
        l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_1594_, v_tacticSeq_1596_);
    return v___x_1597_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(
    mut v_range_1598_: *mut crate::leanh::LeanObject,
    mut v_stx_1599_: *mut crate::leanh::LeanObject,
    mut v_prev_x3f_1600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1601_: u8 = 0;
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1607_: u8 = 0;
    let mut v___y_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: u8 = 0;
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trailing_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stopPos_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: u8 = 0;
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: u8 = 0;
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: u8 = 0;
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1635_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1601_ = 1;
                v___x_1602_ = l_Lean_Syntax_getPos_x3f(v_stx_1599_, v___x_1601_);
                if crate::leanh::lean_obj_tag(v___x_1602_) == 0 {
                    crate::leanh::lean_dec(v_prev_x3f_1600_);
                    v___x_1603_ = crate::leanh::lean_box(0);
                    return v___x_1603_;
                } else {
                    v_val_1604_ = crate::leanh::lean_ctor_get(v___x_1602_, 0);
                    v_isSharedCheck_1635_ = (!crate::leanh::lean_is_exclusive(v___x_1602_)) as u8;
                    if v_isSharedCheck_1635_ == 0 {
                        v___x_1606_ = v___x_1602_;
                        v_isShared_1607_ = v_isSharedCheck_1635_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1604_);
                        crate::leanh::lean_dec(v___x_1602_);
                        v___x_1606_ = crate::leanh::lean_box(0);
                        v_isShared_1607_ = v_isSharedCheck_1635_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_prev_x3f_1600_) == 0 {
                    crate::leanh::lean_inc(v_val_1604_);
                    v___y_1609_ = v_val_1604_;
                    state = 2;
                    continue;
                } else {
                    v_val_1634_ = crate::leanh::lean_ctor_get(v_prev_x3f_1600_, 0);
                    crate::leanh::lean_inc(v_val_1634_);
                    crate::leanh::lean_dec_ref_known(v_prev_x3f_1600_, 1);
                    v___y_1609_ = v_val_1634_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_start_1610_ = crate::leanh::lean_ctor_get(v_range_1598_, 0);
                v_stop_1611_ = crate::leanh::lean_ctor_get(v_range_1598_, 1);
                v___x_1612_ = lean_nat_dec_le(v___y_1609_, v_start_1610_);
                crate::leanh::lean_dec(v___y_1609_);
                if v___x_1612_ == 0 {
                    crate::leanh::lean_del_object(v___x_1606_);
                    crate::leanh::lean_dec(v_val_1604_);
                    v___x_1613_ = crate::leanh::lean_box(0);
                    return v___x_1613_;
                } else {
                    v___x_1614_ = l_Lean_Syntax_getTailInfo(v_stx_1599_);
                    if crate::leanh::lean_obj_tag(v___x_1614_) == 0 {
                        v_trailing_1615_ = crate::leanh::lean_ctor_get(v___x_1614_, 2);
                        crate::leanh::lean_inc_ref(v_trailing_1615_);
                        v_endPos_1616_ = crate::leanh::lean_ctor_get(v___x_1614_, 3);
                        crate::leanh::lean_inc(v_endPos_1616_);
                        crate::leanh::lean_dec_ref_known(v___x_1614_, 4);
                        v_startPos_1617_ = crate::leanh::lean_ctor_get(v_trailing_1615_, 1);
                        crate::leanh::lean_inc(v_startPos_1617_);
                        v_stopPos_1618_ = crate::leanh::lean_ctor_get(v_trailing_1615_, 2);
                        crate::leanh::lean_inc(v_stopPos_1618_);
                        crate::leanh::lean_dec_ref(v_trailing_1615_);
                        v___x_1619_ = lean_nat_sub(v_stopPos_1618_, v_startPos_1617_);
                        crate::leanh::lean_dec(v_startPos_1617_);
                        crate::leanh::lean_dec(v_stopPos_1618_);
                        v___x_1620_ = lean_nat_add(v_endPos_1616_, v___x_1619_);
                        crate::leanh::lean_dec(v___x_1619_);
                        v___x_1621_ = lean_nat_dec_le(v_stop_1611_, v___x_1620_);
                        crate::leanh::lean_dec(v___x_1620_);
                        if v___x_1621_ == 0 {
                            crate::leanh::lean_dec(v_endPos_1616_);
                            crate::leanh::lean_del_object(v___x_1606_);
                            crate::leanh::lean_dec(v_val_1604_);
                            v___x_1622_ = crate::leanh::lean_box(0);
                            return v___x_1622_;
                        } else {
                            v___x_1623_ = lean_nat_dec_le(v_val_1604_, v_start_1610_);
                            crate::leanh::lean_dec(v_val_1604_);
                            if v___x_1623_ == 0 {
                                crate::leanh::lean_dec(v_endPos_1616_);
                                v___x_1624_ = crate::leanh::lean_box((v___x_1623_) as usize);
                                if v_isShared_1607_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1606_, 0, v___x_1624_);
                                    v___x_1626_ = v___x_1606_;
                                    state = 3;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1627_ =
                                        crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
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
                                crate::leanh::lean_dec(v_endPos_1616_);
                                v___x_1629_ = crate::leanh::lean_box((v___x_1628_) as usize);
                                if v_isShared_1607_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1606_, 0, v___x_1629_);
                                    v___x_1631_ = v___x_1606_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1632_ =
                                        crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
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
                        crate::leanh::lean_dec(v___x_1614_);
                        crate::leanh::lean_del_object(v___x_1606_);
                        crate::leanh::lean_dec(v_val_1604_);
                        v___x_1633_ = crate::leanh::lean_box(0);
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
    mut v_range_1636_: *mut crate::leanh::LeanObject,
    mut v_stx_1637_: *mut crate::leanh::LeanObject,
    mut v_prev_x3f_1638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1639_ =
        l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(
            v_range_1636_,
            v_stx_1637_,
            v_prev_x3f_1638_,
        );
    crate::leanh::lean_dec(v_stx_1637_);
    crate::leanh::lean_dec_ref(v_range_1636_);
    return v_res_1639_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(
    mut v_r_u2081_1640_: *mut crate::leanh::LeanObject,
    mut v_r_u2082_1641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_u2081_1640_) == 1 {
        let mut v_val_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1642_ = crate::leanh::lean_ctor_get(v_r_u2081_1640_, 0);
        if crate::leanh::lean_obj_tag(v_val_1642_) == 1 {
            let mut v_preferred_1643_: u8 = 0;
            v_preferred_1643_ = crate::leanh::lean_ctor_get_uint8(
                v_val_1642_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
            );
            if v_preferred_1643_ == 1 {
                if crate::leanh::lean_obj_tag(v_r_u2082_1641_) == 1 {
                    let mut v_preferred_1644_: u8 = 0;
                    v_preferred_1644_ = crate::leanh::lean_ctor_get_uint8(
                        v_r_u2082_1641_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    if v_preferred_1644_ == 0 {
                        crate::leanh::lean_inc_ref(v_val_1642_);
                        return v_val_1642_;
                    } else {
                        crate::leanh::lean_inc_ref(v_r_u2082_1641_);
                        return v_r_u2082_1641_;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_r_u2082_1641_);
                    return v_r_u2082_1641_;
                }
            } else {
                crate::leanh::lean_inc_ref(v_r_u2082_1641_);
                return v_r_u2082_1641_;
            }
        } else {
            crate::leanh::lean_inc_ref(v_r_u2082_1641_);
            return v_r_u2082_1641_;
        }
    } else {
        crate::leanh::lean_inc_ref(v_r_u2082_1641_);
        return v_r_u2082_1641_;
    }
}
pub unsafe fn l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge___boxed(
    mut v_r_u2081_1645_: *mut crate::leanh::LeanObject,
    mut v_r_u2082_1646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1647_ =
        l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(
            v_r_u2081_1645_,
            v_r_u2082_1646_,
        );
    crate::leanh::lean_dec_ref(v_r_u2082_1646_);
    crate::leanh::lean_dec(v_r_u2081_1645_);
    return v_res_1647_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(
    mut v_upperBound_1651_: *mut crate::leanh::LeanObject,
    mut v___x_1652_: *mut crate::leanh::LeanObject,
    mut v_range_1653_: *mut crate::leanh::LeanObject,
    mut v_a_1654_: *mut crate::leanh::LeanObject,
    mut v_b_1655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: u8 = 0;
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: u8 = 0;
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1672_: u8 = 0;
    let mut v_stop_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: u8 = 0;
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1677_: u8 = 0;
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1684_: u8 = 0;
    let mut v_unused_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1687_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1661_ = lean_nat_dec_lt(v_a_1654_, v_upperBound_1651_);
                if v___x_1661_ == 0 {
                    crate::leanh::lean_dec(v_a_1654_);
                    crate::leanh::lean_dec_ref(v_range_1653_);
                    crate::leanh::lean_inc_ref(v_b_1655_);
                    return v_b_1655_;
                } else {
                    v___x_1662_ = crate::leanh::lean_box(0);
                    v___x_1663_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0;
                    v___x_1664_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_1665_ = lean_nat_mul(v___x_1664_, v_a_1654_);
                    v___x_1666_ = l_Lean_Syntax_getArg(v___x_1652_, v___x_1665_);
                    crate::leanh::lean_dec(v___x_1665_);
                    v___x_1667_ = 0;
                    v___x_1668_ = l_Lean_Syntax_getPos_x3f(v___x_1666_, v___x_1667_);
                    crate::leanh::lean_dec(v___x_1666_);
                    if crate::leanh::lean_obj_tag(v___x_1668_) == 1 {
                        v_val_1669_ = crate::leanh::lean_ctor_get(v___x_1668_, 0);
                        v_isSharedCheck_1687_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1668_)) as u8;
                        if v_isSharedCheck_1687_ == 0 {
                            v___x_1671_ = v___x_1668_;
                            v_isShared_1672_ = v_isSharedCheck_1687_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1669_);
                            crate::leanh::lean_dec(v___x_1668_);
                            v___x_1671_ = crate::leanh::lean_box(0);
                            v_isShared_1672_ = v_isSharedCheck_1687_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1668_);
                        v_a_1657_ = v___x_1663_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1658_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1659_ = lean_nat_add(v_a_1654_, v___x_1658_);
                crate::leanh::lean_dec(v_a_1654_);
                v_a_1654_ = v___x_1659_;
                v_b_1655_ = v_a_1657_;
                state = 0;
                continue;
            }
            2 => {
                v_stop_1673_ = crate::leanh::lean_ctor_get(v_range_1653_, 1);
                v___x_1674_ = lean_nat_dec_lt(v_stop_1673_, v_val_1669_);
                crate::leanh::lean_dec(v_val_1669_);
                if v___x_1674_ == 0 {
                    crate::leanh::lean_del_object(v___x_1671_);
                    v_a_1657_ = v___x_1663_;
                    state = 1;
                    continue;
                } else {
                    v_isSharedCheck_1684_ = (!crate::leanh::lean_is_exclusive(v_range_1653_)) as u8;
                    if v_isSharedCheck_1684_ == 0 {
                        v_unused_1685_ = crate::leanh::lean_ctor_get(v_range_1653_, 1);
                        crate::leanh::lean_dec(v_unused_1685_);
                        v_unused_1686_ = crate::leanh::lean_ctor_get(v_range_1653_, 0);
                        crate::leanh::lean_dec(v_unused_1686_);
                        v___x_1676_ = v_range_1653_;
                        v_isShared_1677_ = v_isSharedCheck_1684_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_range_1653_);
                        v___x_1676_ = crate::leanh::lean_box(0);
                        v_isShared_1677_ = v_isSharedCheck_1684_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1672_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1671_, 0, v_a_1654_);
                    v___x_1679_ = v___x_1671_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1683_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1654_);
                    v___x_1679_ = v_reuseFailAlloc_1683_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1677_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1676_, 1, v___x_1662_);
                    crate::leanh::lean_ctor_set(v___x_1676_, 0, v___x_1679_);
                    v___x_1681_ = v___x_1676_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1682_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1682_, 1, v___x_1662_);
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
    mut v_upperBound_1688_: *mut crate::leanh::LeanObject,
    mut v___x_1689_: *mut crate::leanh::LeanObject,
    mut v_range_1690_: *mut crate::leanh::LeanObject,
    mut v_a_1691_: *mut crate::leanh::LeanObject,
    mut v_b_1692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(v_upperBound_1688_, v___x_1689_, v_range_1690_, v_a_1691_, v_b_1692_);
    crate::leanh::lean_dec_ref(v_b_1692_);
    crate::leanh::lean_dec(v___x_1689_);
    crate::leanh::lean_dec(v_upperBound_1688_);
    return v_res_1693_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(
    mut v_stx_1694_: *mut crate::leanh::LeanObject,
    mut v_a_1695_: *mut crate::leanh::LeanObject,
    mut v___x_1696_: u8,
    mut v_snd_1697_: *mut crate::leanh::LeanObject,
    mut v_____r_1698_: *mut crate::leanh::LeanObject,
    mut v_childRes_1699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1705_ = l_Lean_Syntax_getArg(v_stx_1694_, v_a_1695_);
                v___x_1706_ = l_Lean_Syntax_getTailPos_x3f(v___x_1705_, v___x_1696_);
                crate::leanh::lean_dec(v___x_1705_);
                if crate::leanh::lean_obj_tag(v___x_1706_) == 0 {
                    v___y_1701_ = v_snd_1697_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_1697_);
                    v___y_1701_ = v___x_1706_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1702_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1702_, 0, v_childRes_1699_);
                crate::leanh::lean_ctor_set(v___x_1702_, 1, v___y_1701_);
                v___x_1703_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1703_, 0, v___x_1702_);
                v___x_1704_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1704_, 0, v___x_1703_);
                return v___x_1704_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0___boxed(
    mut v_stx_1707_: *mut crate::leanh::LeanObject,
    mut v_a_1708_: *mut crate::leanh::LeanObject,
    mut v___x_1709_: *mut crate::leanh::LeanObject,
    mut v_snd_1710_: *mut crate::leanh::LeanObject,
    mut v_____r_1711_: *mut crate::leanh::LeanObject,
    mut v_childRes_1712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4623__boxed_1713_: u8 = 0;
    let mut v_res_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4623__boxed_1713_ = (crate::leanh::lean_unbox(v___x_1709_) as u8);
    v_res_1714_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_1707_, v_a_1708_, v___x_4623__boxed_1713_, v_snd_1710_, v_____r_1711_, v_childRes_1712_);
    crate::leanh::lean_dec(v_a_1708_);
    crate::leanh::lean_dec(v_stx_1707_);
    return v_res_1714_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(
    mut v___y_1725_: *mut crate::leanh::LeanObject,
    mut v___x_1726_: u8,
    mut v___x_1727_: *mut crate::leanh::LeanObject,
    mut v_range_1728_: *mut crate::leanh::LeanObject,
    mut v___x_1729_: *mut crate::leanh::LeanObject,
    mut v_preferred_1730_: *mut crate::leanh::LeanObject,
    mut v_a_1731_: *mut crate::leanh::LeanObject,
    mut v_b_1732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inner_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1740_: u8 = 0;
    let mut v_upperBound_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1744_: u8 = 0;
    let mut v_val_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1748_: u8 = 0;
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: u8 = 0;
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1780_: u8 = 0;
    let mut v___x_1781_: u8 = 0;
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1790_: u8 = 0;
    let mut v_reuseFailAlloc_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1795_: u8 = 0;
    let mut v_isSharedCheck_1796_: u8 = 0;
    let mut v_unused_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1798_: u8 = 0;
    let mut v_unused_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_inner_1733_ = crate::leanh::lean_ctor_get(v_a_1731_, 2);
                crate::leanh::lean_inc(v_inner_1733_);
                v_next_1734_ = crate::leanh::lean_ctor_get(v_inner_1733_, 0);
                crate::leanh::lean_inc(v_next_1734_);
                if crate::leanh::lean_obj_tag(v_next_1734_) == 0 {
                    crate::leanh::lean_dec(v_inner_1733_);
                    crate::leanh::lean_dec_ref(v_a_1731_);
                    crate::leanh::lean_dec_ref(v_preferred_1730_);
                    crate::leanh::lean_dec(v___x_1729_);
                    crate::leanh::lean_dec_ref(v_range_1728_);
                    crate::leanh::lean_dec(v___x_1727_);
                    v___x_1735_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1735_, 0, v_b_1732_);
                    return v___x_1735_;
                } else {
                    v_nextIdx_1736_ = crate::leanh::lean_ctor_get(v_a_1731_, 0);
                    v_n_1737_ = crate::leanh::lean_ctor_get(v_a_1731_, 1);
                    v_isSharedCheck_1798_ = (!crate::leanh::lean_is_exclusive(v_a_1731_)) as u8;
                    if v_isSharedCheck_1798_ == 0 {
                        v_unused_1799_ = crate::leanh::lean_ctor_get(v_a_1731_, 2);
                        crate::leanh::lean_dec(v_unused_1799_);
                        v___x_1739_ = v_a_1731_;
                        v_isShared_1740_ = v_isSharedCheck_1798_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_n_1737_);
                        crate::leanh::lean_inc(v_nextIdx_1736_);
                        crate::leanh::lean_dec(v_a_1731_);
                        v___x_1739_ = crate::leanh::lean_box(0);
                        v_isShared_1740_ = v_isSharedCheck_1798_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_upperBound_1741_ = crate::leanh::lean_ctor_get(v_inner_1733_, 1);
                v_isSharedCheck_1796_ = (!crate::leanh::lean_is_exclusive(v_inner_1733_)) as u8;
                if v_isSharedCheck_1796_ == 0 {
                    v_unused_1797_ = crate::leanh::lean_ctor_get(v_inner_1733_, 0);
                    crate::leanh::lean_dec(v_unused_1797_);
                    v___x_1743_ = v_inner_1733_;
                    v_isShared_1744_ = v_isSharedCheck_1796_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upperBound_1741_);
                    crate::leanh::lean_dec(v_inner_1733_);
                    v___x_1743_ = crate::leanh::lean_box(0);
                    v_isShared_1744_ = v_isSharedCheck_1796_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_val_1745_ = crate::leanh::lean_ctor_get(v_next_1734_, 0);
                v_isSharedCheck_1795_ = (!crate::leanh::lean_is_exclusive(v_next_1734_)) as u8;
                if v_isSharedCheck_1795_ == 0 {
                    v___x_1747_ = v_next_1734_;
                    v_isShared_1748_ = v_isSharedCheck_1795_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_1745_);
                    crate::leanh::lean_dec(v_next_1734_);
                    v___x_1747_ = crate::leanh::lean_box(0);
                    v_isShared_1748_ = v_isSharedCheck_1795_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1749_ = lean_nat_add(v_val_1745_, v_nextIdx_1736_);
                crate::leanh::lean_dec(v_nextIdx_1736_);
                crate::leanh::lean_dec(v_val_1745_);
                v___x_1750_ = lean_nat_dec_lt(v___x_1749_, v_upperBound_1741_);
                if v___x_1750_ == 0 {
                    crate::leanh::lean_dec(v___x_1749_);
                    crate::leanh::lean_del_object(v___x_1743_);
                    crate::leanh::lean_dec(v_upperBound_1741_);
                    crate::leanh::lean_del_object(v___x_1739_);
                    crate::leanh::lean_dec(v_n_1737_);
                    crate::leanh::lean_dec_ref(v_preferred_1730_);
                    crate::leanh::lean_dec(v___x_1729_);
                    crate::leanh::lean_dec_ref(v_range_1728_);
                    crate::leanh::lean_dec(v___x_1727_);
                    if v_isShared_1748_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1747_, 0, v_b_1732_);
                        v___x_1752_ = v___x_1747_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1753_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_b_1732_);
                        v___x_1752_ = v_reuseFailAlloc_1753_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_1754_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1755_ = lean_nat_add(v___x_1749_, v___x_1754_);
                    if v_isShared_1748_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1747_, 0, v___x_1755_);
                        v___x_1757_ = v___x_1747_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1794_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1755_);
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
                    crate::leanh::lean_ctor_set(v___x_1743_, 0, v___x_1757_);
                    v___x_1759_ = v___x_1743_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1793_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1757_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_upperBound_1741_);
                    v___x_1759_ = v_reuseFailAlloc_1793_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_inc(v_n_1737_);
                if v_isShared_1740_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1739_, 2, v___x_1759_);
                    crate::leanh::lean_ctor_set(v___x_1739_, 0, v_n_1737_);
                    v___x_1761_ = v___x_1739_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1792_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_n_1737_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_n_1737_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1792_, 2, v___x_1759_);
                    v___x_1761_ = v_reuseFailAlloc_1792_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1770_ = l_Lean_Syntax_getArg(v___x_1727_, v___x_1749_);
                v___x_1771_ = crate::leanh::lean_box(0);
                v___x_1772_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(v_range_1728_, v___x_1770_, v___x_1771_);
                if crate::leanh::lean_obj_tag(v___x_1772_) == 1 {
                    v_val_1773_ = crate::leanh::lean_ctor_get(v___x_1772_, 0);
                    crate::leanh::lean_inc(v_val_1773_);
                    crate::leanh::lean_dec_ref_known(v___x_1772_, 1);
                    crate::leanh::lean_inc(v___x_1727_);
                    v___x_1774_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1774_, 0, v___x_1727_);
                    crate::leanh::lean_ctor_set(v___x_1774_, 1, v___x_1749_);
                    crate::leanh::lean_inc(v___x_1729_);
                    v___x_1775_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1775_, 0, v___x_1774_);
                    crate::leanh::lean_ctor_set(v___x_1775_, 1, v___x_1729_);
                    crate::leanh::lean_inc(v___x_1770_);
                    crate::leanh::lean_inc_ref(v___x_1775_);
                    crate::leanh::lean_inc_ref(v_range_1728_);
                    crate::leanh::lean_inc_ref(v_preferred_1730_);
                    v___x_1776_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(v_preferred_1730_, v_range_1728_, v___x_1775_, v___x_1770_, v___x_1771_);
                    if crate::leanh::lean_obj_tag(v___x_1776_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1775_, 2);
                        crate::leanh::lean_dec(v_val_1773_);
                        crate::leanh::lean_dec(v___x_1770_);
                        crate::leanh::lean_dec_ref(v___x_1761_);
                        crate::leanh::lean_dec(v_b_1732_);
                        crate::leanh::lean_dec_ref(v_preferred_1730_);
                        crate::leanh::lean_dec(v___x_1729_);
                        crate::leanh::lean_dec_ref(v_range_1728_);
                        crate::leanh::lean_dec(v___x_1727_);
                        return v___x_1776_;
                    } else {
                        v_val_1777_ = crate::leanh::lean_ctor_get(v___x_1776_, 0);
                        v_isSharedCheck_1790_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1776_)) as u8;
                        if v_isSharedCheck_1790_ == 0 {
                            v___x_1779_ = v___x_1776_;
                            v_isShared_1780_ = v_isSharedCheck_1790_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1777_);
                            crate::leanh::lean_dec(v___x_1776_);
                            v___x_1779_ = crate::leanh::lean_box(0);
                            v_isShared_1780_ = v_isSharedCheck_1790_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1772_);
                    crate::leanh::lean_dec(v___x_1770_);
                    crate::leanh::lean_dec(v___x_1749_);
                    v_a_1731_ = v___x_1761_;
                    state = 0;
                    continue;
                }
            }
            8 => {
                v___x_1764_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(v___y_1725_, v___y_1763_);
                crate::leanh::lean_dec_ref(v___y_1763_);
                v___x_1765_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1765_, 0, v___x_1764_);
                v_a_1731_ = v___x_1761_;
                v_b_1732_ = v___x_1765_;
                state = 0;
                continue;
            }
            9 => {
                if crate::leanh::lean_obj_tag(v_b_1732_) == 0 {
                    v___y_1763_ = v_val_1768_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_b_1732_, 1);
                    if v___x_1726_ == 0 {
                        v___y_1763_ = v_val_1768_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_val_1768_);
                        crate::leanh::lean_dec_ref(v___x_1761_);
                        crate::leanh::lean_dec_ref(v_preferred_1730_);
                        crate::leanh::lean_dec(v___x_1729_);
                        crate::leanh::lean_dec_ref(v_range_1728_);
                        crate::leanh::lean_dec(v___x_1727_);
                        v___x_1769_ = crate::leanh::lean_box(0);
                        return v___x_1769_;
                    }
                }
            }
            10 => {
                if crate::leanh::lean_obj_tag(v_val_1777_) == 0 {
                    v___x_1781_ = (crate::leanh::lean_unbox(v_val_1773_) as u8);
                    crate::leanh::lean_dec(v_val_1773_);
                    if v___x_1781_ == 0 {
                        crate::leanh::lean_del_object(v___x_1779_);
                        crate::leanh::lean_dec_ref_known(v___x_1775_, 2);
                        crate::leanh::lean_dec(v___x_1770_);
                        v_a_1731_ = v___x_1761_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1783_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1784_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1784_, 0, v___x_1770_);
                        crate::leanh::lean_ctor_set(v___x_1784_, 1, v___x_1783_);
                        v___x_1785_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1785_, 0, v___x_1784_);
                        crate::leanh::lean_ctor_set(v___x_1785_, 1, v___x_1775_);
                        if v_isShared_1780_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_1779_, 0);
                            crate::leanh::lean_ctor_set(v___x_1779_, 0, v___x_1785_);
                            v___x_1787_ = v___x_1779_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_1788_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
                            v___x_1787_ = v_reuseFailAlloc_1788_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1779_);
                    crate::leanh::lean_dec_ref_known(v___x_1775_, 2);
                    crate::leanh::lean_dec(v_val_1773_);
                    crate::leanh::lean_dec(v___x_1770_);
                    v_val_1789_ = crate::leanh::lean_ctor_get(v_val_1777_, 0);
                    crate::leanh::lean_inc(v_val_1789_);
                    crate::leanh::lean_dec_ref_known(v_val_1777_, 1);
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
    mut v_preferred_1806_: *mut crate::leanh::LeanObject,
    mut v_range_1807_: *mut crate::leanh::LeanObject,
    mut v_stack_1808_: *mut crate::leanh::LeanObject,
    mut v_stx_1809_: *mut crate::leanh::LeanObject,
    mut v_prev_x3f_1810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: u8 = 0;
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_childRes_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1822_: u8 = 0;
    let mut v_fst_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1827_: u8 = 0;
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_childRes_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1843_: u8 = 0;
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1847_: u8 = 0;
    let mut v_unused_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1853_: u8 = 0;
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bracket_1861_: u8 = 0;
    let mut v___y_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: u8 = 0;
    let mut v___y_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: u8 = 0;
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_stx_1809_);
                v___x_1811_ = l_Lean_Syntax_getKind(v_stx_1809_);
                v___x_1812_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3;
                v___x_1813_ = lean_name_eq(v___x_1811_, v___x_1812_);
                crate::leanh::lean_dec(v___x_1811_);
                if v___x_1813_ == 0 {
                    v___x_1814_ = l_Lean_Syntax_getNumArgs(v_stx_1809_);
                    v___x_1815_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_childRes_1816_ = crate::leanh::lean_box(0);
                    v___x_1817_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1817_, 0, v_childRes_1816_);
                    crate::leanh::lean_ctor_set(v___x_1817_, 1, v_prev_x3f_1810_);
                    v___x_1818_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(v___x_1814_, v_stx_1809_, v_range_1807_, v_stack_1808_, v_preferred_1806_, v___x_1813_, v___x_1815_, v___x_1817_);
                    crate::leanh::lean_dec(v___x_1814_);
                    if crate::leanh::lean_obj_tag(v___x_1818_) == 0 {
                        return v_childRes_1816_;
                    } else {
                        v_val_1819_ = crate::leanh::lean_ctor_get(v___x_1818_, 0);
                        v_isSharedCheck_1827_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1818_)) as u8;
                        if v_isSharedCheck_1827_ == 0 {
                            v___x_1821_ = v___x_1818_;
                            v_isShared_1822_ = v_isSharedCheck_1827_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1819_);
                            crate::leanh::lean_dec(v___x_1818_);
                            v___x_1821_ = crate::leanh::lean_box(0);
                            v_isShared_1822_ = v_isSharedCheck_1827_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_prev_x3f_1810_);
                    v___x_1828_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1858_ = l_Lean_Syntax_getArg(v_stx_1809_, v___x_1828_);
                    crate::leanh::lean_inc(v___x_1858_);
                    v___x_1859_ = l_Lean_Syntax_getKind(v___x_1858_);
                    v___x_1860_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6;
                    v_bracket_1861_ = lean_name_eq(v___x_1859_, v___x_1860_);
                    crate::leanh::lean_dec(v___x_1859_);
                    if v_bracket_1861_ == 0 {
                        v___y_1870_ = v___x_1828_;
                        state = 8;
                        continue;
                    } else {
                        v___x_1889_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___y_1870_ = v___x_1889_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1823_ = crate::leanh::lean_ctor_get(v_val_1819_, 0);
                crate::leanh::lean_inc(v_fst_1823_);
                crate::leanh::lean_dec(v_val_1819_);
                if v_isShared_1822_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1821_, 0, v_fst_1823_);
                    v___x_1825_ = v___x_1821_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1826_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_fst_1823_);
                    v___x_1825_ = v_reuseFailAlloc_1826_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1825_;
            }
            3 => {
                v_childRes_1833_ = crate::leanh::lean_box(0);
                v___x_1834_ = l_Lean_Syntax_getNumArgs(v___y_1830_);
                v___x_1835_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__4;
                v___x_1836_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1836_, 0, v___x_1835_);
                crate::leanh::lean_ctor_set(v___x_1836_, 1, v___x_1834_);
                v___x_1837_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1838_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1838_, 0, v___x_1828_);
                crate::leanh::lean_ctor_set(v___x_1838_, 1, v___x_1837_);
                crate::leanh::lean_ctor_set(v___x_1838_, 2, v___x_1836_);
                v___x_1839_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(v___y_1832_, v___x_1813_, v___y_1830_, v_range_1807_, v___y_1831_, v_preferred_1806_, v___x_1838_, v_childRes_1833_);
                if crate::leanh::lean_obj_tag(v___x_1839_) == 0 {
                    crate::leanh::lean_dec(v___y_1832_);
                    return v___x_1839_;
                } else {
                    v_val_1840_ = crate::leanh::lean_ctor_get(v___x_1839_, 0);
                    crate::leanh::lean_inc(v_val_1840_);
                    if crate::leanh::lean_obj_tag(v_val_1840_) == 0 {
                        v_isSharedCheck_1847_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1839_)) as u8;
                        if v_isSharedCheck_1847_ == 0 {
                            v_unused_1848_ = crate::leanh::lean_ctor_get(v___x_1839_, 0);
                            crate::leanh::lean_dec(v_unused_1848_);
                            v___x_1842_ = v___x_1839_;
                            v_isShared_1843_ = v_isSharedCheck_1847_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1839_);
                            v___x_1842_ = crate::leanh::lean_box(0);
                            v_isShared_1843_ = v_isSharedCheck_1847_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_val_1840_, 1);
                        crate::leanh::lean_dec(v___y_1832_);
                        return v___x_1839_;
                    }
                }
            }
            4 => {
                if v_isShared_1843_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1842_, 0, v___y_1832_);
                    v___x_1845_ = v___x_1842_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1846_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___y_1832_);
                    v___x_1845_ = v_reuseFailAlloc_1846_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1845_;
            }
            6 => {
                crate::leanh::lean_inc(v___y_1850_);
                v___x_1854_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1854_, 0, v___y_1850_);
                crate::leanh::lean_ctor_set(v___x_1854_, 1, v___x_1828_);
                crate::leanh::lean_inc(v___y_1852_);
                v___x_1855_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1855_, 0, v___x_1854_);
                crate::leanh::lean_ctor_set(v___x_1855_, 1, v___y_1852_);
                v___x_1856_ = crate::leanh::lean_alloc_ctor(1, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1856_, 0, v___y_1851_);
                crate::leanh::lean_ctor_set(v___x_1856_, 1, v___x_1855_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1856_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___y_1853_,
                );
                v___x_1857_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1857_, 0, v___x_1856_);
                v___y_1830_ = v___y_1850_;
                v___y_1831_ = v___y_1852_;
                v___y_1832_ = v___x_1857_;
                state = 3;
                continue;
            }
            7 => {
                if v_bracket_1861_ == 0 {
                    crate::leanh::lean_inc_ref(v_preferred_1806_);
                    v___x_1867_ = crate::leanh::lean_apply_1(v_preferred_1806_, v___y_1864_);
                    v___x_1868_ = (crate::leanh::lean_unbox(v___x_1867_) as u8);
                    v___y_1850_ = v___y_1863_;
                    v___y_1851_ = v___y_1866_;
                    v___y_1852_ = v___y_1865_;
                    v___y_1853_ = v___x_1868_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_1864_);
                    v___y_1850_ = v___y_1863_;
                    v___y_1851_ = v___y_1866_;
                    v___y_1852_ = v___y_1865_;
                    v___y_1853_ = v___x_1813_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_inc(v___y_1870_);
                crate::leanh::lean_inc(v___x_1858_);
                v___x_1871_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1871_, 0, v___x_1858_);
                crate::leanh::lean_ctor_set(v___x_1871_, 1, v___y_1870_);
                v___x_1872_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1872_, 0, v_stx_1809_);
                crate::leanh::lean_ctor_set(v___x_1872_, 1, v___x_1828_);
                v___x_1873_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1873_, 0, v___x_1872_);
                crate::leanh::lean_ctor_set(v___x_1873_, 1, v_stack_1808_);
                v___x_1874_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1874_, 0, v___x_1871_);
                crate::leanh::lean_ctor_set(v___x_1874_, 1, v___x_1873_);
                v___x_1875_ = l_Lean_Syntax_getArg(v___x_1858_, v___y_1870_);
                crate::leanh::lean_dec(v___y_1870_);
                crate::leanh::lean_dec(v___x_1858_);
                v___x_1876_ = l_Lean_Syntax_getArg(v___x_1875_, v___x_1828_);
                v___x_1877_ = 0;
                v___x_1878_ = l_Lean_Syntax_getPos_x3f(v___x_1876_, v___x_1877_);
                crate::leanh::lean_dec(v___x_1876_);
                if crate::leanh::lean_obj_tag(v___x_1878_) == 0 {
                    v___x_1879_ = crate::leanh::lean_box(0);
                    v___y_1830_ = v___x_1875_;
                    v___y_1831_ = v___x_1874_;
                    v___y_1832_ = v___x_1879_;
                    state = 3;
                    continue;
                } else {
                    v_val_1880_ = crate::leanh::lean_ctor_get(v___x_1878_, 0);
                    crate::leanh::lean_inc(v_val_1880_);
                    crate::leanh::lean_dec_ref_known(v___x_1878_, 1);
                    v___x_1881_ = l_Lean_Syntax_getNumArgs(v___x_1875_);
                    v___x_1882_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0;
                    crate::leanh::lean_inc_ref(v_range_1807_);
                    v___x_1883_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(v___x_1881_, v___x_1875_, v_range_1807_, v___x_1828_, v___x_1882_);
                    v_fst_1884_ = crate::leanh::lean_ctor_get(v___x_1883_, 0);
                    crate::leanh::lean_inc(v_fst_1884_);
                    crate::leanh::lean_dec_ref(v___x_1883_);
                    if crate::leanh::lean_obj_tag(v_fst_1884_) == 0 {
                        v___x_1885_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1886_ = lean_nat_add(v___x_1881_, v___x_1885_);
                        crate::leanh::lean_dec(v___x_1881_);
                        v___x_1887_ = lean_nat_shiftr(v___x_1886_, v___x_1885_);
                        crate::leanh::lean_dec(v___x_1886_);
                        v___y_1863_ = v___x_1875_;
                        v___y_1864_ = v_val_1880_;
                        v___y_1865_ = v___x_1874_;
                        v___y_1866_ = v___x_1887_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1881_);
                        v_val_1888_ = crate::leanh::lean_ctor_get(v_fst_1884_, 0);
                        crate::leanh::lean_inc(v_val_1888_);
                        crate::leanh::lean_dec_ref_known(v_fst_1884_, 1);
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
    mut v_upperBound_1890_: *mut crate::leanh::LeanObject,
    mut v_stx_1891_: *mut crate::leanh::LeanObject,
    mut v_range_1892_: *mut crate::leanh::LeanObject,
    mut v_stack_1893_: *mut crate::leanh::LeanObject,
    mut v_preferred_1894_: *mut crate::leanh::LeanObject,
    mut v___x_1895_: u8,
    mut v_a_1896_: *mut crate::leanh::LeanObject,
    mut v_b_1897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1904_: u8 = 0;
    let mut v_a_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1913_: u8 = 0;
    let mut v___x_1914_: u8 = 0;
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1920_: u8 = 0;
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1938_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1914_ = lean_nat_dec_lt(v_a_1896_, v_upperBound_1890_);
                if v___x_1914_ == 0 {
                    crate::leanh::lean_dec(v_a_1896_);
                    crate::leanh::lean_dec_ref(v_preferred_1894_);
                    crate::leanh::lean_dec(v_stack_1893_);
                    crate::leanh::lean_dec_ref(v_range_1892_);
                    crate::leanh::lean_dec(v_stx_1891_);
                    v___x_1915_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1915_, 0, v_b_1897_);
                    return v___x_1915_;
                } else {
                    v_fst_1916_ = crate::leanh::lean_ctor_get(v_b_1897_, 0);
                    v_snd_1917_ = crate::leanh::lean_ctor_get(v_b_1897_, 1);
                    v_isSharedCheck_1938_ = (!crate::leanh::lean_is_exclusive(v_b_1897_)) as u8;
                    if v_isSharedCheck_1938_ == 0 {
                        v___x_1919_ = v_b_1897_;
                        v_isShared_1920_ = v_isSharedCheck_1938_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1917_);
                        crate::leanh::lean_inc(v_fst_1916_);
                        crate::leanh::lean_dec(v_b_1897_);
                        v___x_1919_ = crate::leanh::lean_box(0);
                        v_isShared_1920_ = v_isSharedCheck_1938_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_1899_) == 0 {
                    crate::leanh::lean_dec(v_a_1896_);
                    crate::leanh::lean_dec_ref(v_preferred_1894_);
                    crate::leanh::lean_dec(v_stack_1893_);
                    crate::leanh::lean_dec_ref(v_range_1892_);
                    crate::leanh::lean_dec(v_stx_1891_);
                    v___x_1900_ = crate::leanh::lean_box(0);
                    return v___x_1900_;
                } else {
                    v_val_1901_ = crate::leanh::lean_ctor_get(v___y_1899_, 0);
                    v_isSharedCheck_1913_ = (!crate::leanh::lean_is_exclusive(v___y_1899_)) as u8;
                    if v_isSharedCheck_1913_ == 0 {
                        v___x_1903_ = v___y_1899_;
                        v_isShared_1904_ = v_isSharedCheck_1913_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1901_);
                        crate::leanh::lean_dec(v___y_1899_);
                        v___x_1903_ = crate::leanh::lean_box(0);
                        v_isShared_1904_ = v_isSharedCheck_1913_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_val_1901_) == 0 {
                    crate::leanh::lean_dec(v_a_1896_);
                    crate::leanh::lean_dec_ref(v_preferred_1894_);
                    crate::leanh::lean_dec(v_stack_1893_);
                    crate::leanh::lean_dec_ref(v_range_1892_);
                    crate::leanh::lean_dec(v_stx_1891_);
                    v_a_1905_ = crate::leanh::lean_ctor_get(v_val_1901_, 0);
                    crate::leanh::lean_inc(v_a_1905_);
                    crate::leanh::lean_dec_ref_known(v_val_1901_, 1);
                    if v_isShared_1904_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1903_, 0, v_a_1905_);
                        v___x_1907_ = v___x_1903_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1908_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1905_);
                        v___x_1907_ = v_reuseFailAlloc_1908_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1903_);
                    v_a_1909_ = crate::leanh::lean_ctor_get(v_val_1901_, 0);
                    crate::leanh::lean_inc(v_a_1909_);
                    crate::leanh::lean_dec_ref_known(v_val_1901_, 1);
                    v___x_1910_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1911_ = lean_nat_add(v_a_1896_, v___x_1910_);
                    crate::leanh::lean_dec(v_a_1896_);
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
                crate::leanh::lean_inc(v_snd_1917_);
                v___x_1922_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(v_range_1892_, v___x_1921_, v_snd_1917_);
                if crate::leanh::lean_obj_tag(v___x_1922_) == 1 {
                    crate::leanh::lean_dec_ref_known(v___x_1922_, 1);
                    crate::leanh::lean_inc(v_a_1896_);
                    crate::leanh::lean_inc(v_stx_1891_);
                    if v_isShared_1920_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1919_, 1, v_a_1896_);
                        crate::leanh::lean_ctor_set(v___x_1919_, 0, v_stx_1891_);
                        v___x_1924_ = v___x_1919_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1935_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_stx_1891_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_a_1896_);
                        v___x_1924_ = v_reuseFailAlloc_1935_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1922_);
                    crate::leanh::lean_dec(v___x_1921_);
                    crate::leanh::lean_del_object(v___x_1919_);
                    v___x_1936_ = crate::leanh::lean_box(0);
                    v___x_1937_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_1891_, v_a_1896_, v___x_1914_, v_snd_1917_, v___x_1936_, v_fst_1916_);
                    v___y_1899_ = v___x_1937_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc(v_stack_1893_);
                v___x_1925_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1925_, 0, v___x_1924_);
                crate::leanh::lean_ctor_set(v___x_1925_, 1, v_stack_1893_);
                crate::leanh::lean_inc(v_snd_1917_);
                crate::leanh::lean_inc_ref(v_range_1892_);
                crate::leanh::lean_inc_ref(v_preferred_1894_);
                v___x_1926_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(v_preferred_1894_, v_range_1892_, v___x_1925_, v___x_1921_, v_snd_1917_);
                if crate::leanh::lean_obj_tag(v___x_1926_) == 0 {
                    crate::leanh::lean_dec(v_snd_1917_);
                    crate::leanh::lean_dec(v_fst_1916_);
                    crate::leanh::lean_dec(v_a_1896_);
                    crate::leanh::lean_dec_ref(v_preferred_1894_);
                    crate::leanh::lean_dec(v_stack_1893_);
                    crate::leanh::lean_dec_ref(v_range_1892_);
                    crate::leanh::lean_dec(v_stx_1891_);
                    v___x_1927_ = crate::leanh::lean_box(0);
                    return v___x_1927_;
                } else {
                    v_val_1928_ = crate::leanh::lean_ctor_get(v___x_1926_, 0);
                    crate::leanh::lean_inc(v_val_1928_);
                    crate::leanh::lean_dec_ref_known(v___x_1926_, 1);
                    if crate::leanh::lean_obj_tag(v_val_1928_) == 1 {
                        if crate::leanh::lean_obj_tag(v_fst_1916_) == 0 {
                            if v___x_1895_ == 0 {
                                v___x_1929_ = crate::leanh::lean_box(0);
                                v___x_1930_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_1891_, v_a_1896_, v___x_1914_, v_snd_1917_, v___x_1929_, v_val_1928_);
                                v___y_1899_ = v___x_1930_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v_val_1928_, 1);
                                crate::leanh::lean_dec(v_snd_1917_);
                                crate::leanh::lean_dec(v_a_1896_);
                                crate::leanh::lean_dec_ref(v_preferred_1894_);
                                crate::leanh::lean_dec(v_stack_1893_);
                                crate::leanh::lean_dec_ref(v_range_1892_);
                                crate::leanh::lean_dec(v_stx_1891_);
                                v___x_1931_ = crate::leanh::lean_box(0);
                                return v___x_1931_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_fst_1916_, 1);
                            crate::leanh::lean_dec_ref_known(v_val_1928_, 1);
                            crate::leanh::lean_dec(v_snd_1917_);
                            crate::leanh::lean_dec(v_a_1896_);
                            crate::leanh::lean_dec_ref(v_preferred_1894_);
                            crate::leanh::lean_dec(v_stack_1893_);
                            crate::leanh::lean_dec_ref(v_range_1892_);
                            crate::leanh::lean_dec(v_stx_1891_);
                            v___x_1932_ = crate::leanh::lean_box(0);
                            return v___x_1932_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_1928_);
                        v___x_1933_ = crate::leanh::lean_box(0);
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
    mut v_upperBound_1939_: *mut crate::leanh::LeanObject,
    mut v_stx_1940_: *mut crate::leanh::LeanObject,
    mut v_range_1941_: *mut crate::leanh::LeanObject,
    mut v_stack_1942_: *mut crate::leanh::LeanObject,
    mut v_preferred_1943_: *mut crate::leanh::LeanObject,
    mut v___x_1944_: *mut crate::leanh::LeanObject,
    mut v_a_1945_: *mut crate::leanh::LeanObject,
    mut v_b_1946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4665__boxed_1947_: u8 = 0;
    let mut v_res_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4665__boxed_1947_ = (crate::leanh::lean_unbox(v___x_1944_) as u8);
    v_res_1948_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(v_upperBound_1939_, v_stx_1940_, v_range_1941_, v_stack_1942_, v_preferred_1943_, v___x_4665__boxed_1947_, v_a_1945_, v_b_1946_);
    crate::leanh::lean_dec(v_upperBound_1939_);
    return v_res_1948_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg___boxed(
    mut v___y_1949_: *mut crate::leanh::LeanObject,
    mut v___x_1950_: *mut crate::leanh::LeanObject,
    mut v___x_1951_: *mut crate::leanh::LeanObject,
    mut v_range_1952_: *mut crate::leanh::LeanObject,
    mut v___x_1953_: *mut crate::leanh::LeanObject,
    mut v_preferred_1954_: *mut crate::leanh::LeanObject,
    mut v_a_1955_: *mut crate::leanh::LeanObject,
    mut v_b_1956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4696__boxed_1957_: u8 = 0;
    let mut v_res_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4696__boxed_1957_ = (crate::leanh::lean_unbox(v___x_1950_) as u8);
    v_res_1958_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(v___y_1949_, v___x_4696__boxed_1957_, v___x_1951_, v_range_1952_, v___x_1953_, v_preferred_1954_, v_a_1955_, v_b_1956_);
    crate::leanh::lean_dec(v___y_1949_);
    return v_res_1958_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0(
    mut v_upperBound_1959_: *mut crate::leanh::LeanObject,
    mut v_stx_1960_: *mut crate::leanh::LeanObject,
    mut v_range_1961_: *mut crate::leanh::LeanObject,
    mut v_stack_1962_: *mut crate::leanh::LeanObject,
    mut v_preferred_1963_: *mut crate::leanh::LeanObject,
    mut v___x_1964_: u8,
    mut v_inst_1965_: *mut crate::leanh::LeanObject,
    mut v_R_1966_: *mut crate::leanh::LeanObject,
    mut v_a_1967_: *mut crate::leanh::LeanObject,
    mut v_b_1968_: *mut crate::leanh::LeanObject,
    mut v_c_1969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1970_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(v_upperBound_1959_, v_stx_1960_, v_range_1961_, v_stack_1962_, v_preferred_1963_, v___x_1964_, v_a_1967_, v_b_1968_);
    return v___x_1970_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___boxed(
    mut v_upperBound_1971_: *mut crate::leanh::LeanObject,
    mut v_stx_1972_: *mut crate::leanh::LeanObject,
    mut v_range_1973_: *mut crate::leanh::LeanObject,
    mut v_stack_1974_: *mut crate::leanh::LeanObject,
    mut v_preferred_1975_: *mut crate::leanh::LeanObject,
    mut v___x_1976_: *mut crate::leanh::LeanObject,
    mut v_inst_1977_: *mut crate::leanh::LeanObject,
    mut v_R_1978_: *mut crate::leanh::LeanObject,
    mut v_a_1979_: *mut crate::leanh::LeanObject,
    mut v_b_1980_: *mut crate::leanh::LeanObject,
    mut v_c_1981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5068__boxed_1982_: u8 = 0;
    let mut v_res_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5068__boxed_1982_ = (crate::leanh::lean_unbox(v___x_1976_) as u8);
    v_res_1983_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0(v_upperBound_1971_, v_stx_1972_, v_range_1973_, v_stack_1974_, v_preferred_1975_, v___x_5068__boxed_1982_, v_inst_1977_, v_R_1978_, v_a_1979_, v_b_1980_, v_c_1981_);
    crate::leanh::lean_dec(v_upperBound_1971_);
    return v_res_1983_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1(
    mut v___y_1984_: *mut crate::leanh::LeanObject,
    mut v___x_1985_: u8,
    mut v___x_1986_: *mut crate::leanh::LeanObject,
    mut v_range_1987_: *mut crate::leanh::LeanObject,
    mut v___x_1988_: *mut crate::leanh::LeanObject,
    mut v_preferred_1989_: *mut crate::leanh::LeanObject,
    mut v_inst_1990_: *mut crate::leanh::LeanObject,
    mut v_R_1991_: *mut crate::leanh::LeanObject,
    mut v_a_1992_: *mut crate::leanh::LeanObject,
    mut v_b_1993_: *mut crate::leanh::LeanObject,
    mut v_c_1994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1995_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(v___y_1984_, v___x_1985_, v___x_1986_, v_range_1987_, v___x_1988_, v_preferred_1989_, v_a_1992_, v_b_1993_);
    return v___x_1995_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___boxed(
    mut v___y_1996_: *mut crate::leanh::LeanObject,
    mut v___x_1997_: *mut crate::leanh::LeanObject,
    mut v___x_1998_: *mut crate::leanh::LeanObject,
    mut v_range_1999_: *mut crate::leanh::LeanObject,
    mut v___x_2000_: *mut crate::leanh::LeanObject,
    mut v_preferred_2001_: *mut crate::leanh::LeanObject,
    mut v_inst_2002_: *mut crate::leanh::LeanObject,
    mut v_R_2003_: *mut crate::leanh::LeanObject,
    mut v_a_2004_: *mut crate::leanh::LeanObject,
    mut v_b_2005_: *mut crate::leanh::LeanObject,
    mut v_c_2006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5079__boxed_2007_: u8 = 0;
    let mut v_res_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5079__boxed_2007_ = (crate::leanh::lean_unbox(v___x_1997_) as u8);
    v_res_2008_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1(v___y_1996_, v___x_5079__boxed_2007_, v___x_1998_, v_range_1999_, v___x_2000_, v_preferred_2001_, v_inst_2002_, v_R_2003_, v_a_2004_, v_b_2005_, v_c_2006_);
    crate::leanh::lean_dec(v___y_1996_);
    return v_res_2008_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2(
    mut v_upperBound_2009_: *mut crate::leanh::LeanObject,
    mut v___x_2010_: *mut crate::leanh::LeanObject,
    mut v_range_2011_: *mut crate::leanh::LeanObject,
    mut v_inst_2012_: *mut crate::leanh::LeanObject,
    mut v_R_2013_: *mut crate::leanh::LeanObject,
    mut v_a_2014_: *mut crate::leanh::LeanObject,
    mut v_b_2015_: *mut crate::leanh::LeanObject,
    mut v_c_2016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2017_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(v_upperBound_2009_, v___x_2010_, v_range_2011_, v_a_2014_, v_b_2015_);
    return v___x_2017_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___boxed(
    mut v_upperBound_2018_: *mut crate::leanh::LeanObject,
    mut v___x_2019_: *mut crate::leanh::LeanObject,
    mut v_range_2020_: *mut crate::leanh::LeanObject,
    mut v_inst_2021_: *mut crate::leanh::LeanObject,
    mut v_R_2022_: *mut crate::leanh::LeanObject,
    mut v_a_2023_: *mut crate::leanh::LeanObject,
    mut v_b_2024_: *mut crate::leanh::LeanObject,
    mut v_c_2025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2026_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2(v_upperBound_2018_, v___x_2019_, v_range_2020_, v_inst_2021_, v_R_2022_, v_a_2023_, v_b_2024_, v_c_2025_);
    crate::leanh::lean_dec_ref(v_b_2024_);
    crate::leanh::lean_dec(v___x_2019_);
    crate::leanh::lean_dec(v_upperBound_2018_);
    return v_res_2026_;
}
pub unsafe fn l_Lean_CodeAction_findTactic_x3f(
    mut v_preferred_2027_: *mut crate::leanh::LeanObject,
    mut v_range_2028_: *mut crate::leanh::LeanObject,
    mut v_root_2029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2030_ = crate::leanh::lean_box(0);
    v___x_2031_ =
        l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(
            v_range_2028_,
            v_root_2029_,
            v___x_2030_,
        );
    if crate::leanh::lean_obj_tag(v___x_2031_) == 0 {
        crate::leanh::lean_dec(v_root_2029_);
        crate::leanh::lean_dec_ref(v_range_2028_);
        crate::leanh::lean_dec_ref(v_preferred_2027_);
        return v___x_2030_;
    } else {
        let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_2031_, 1);
        v___x_2032_ = crate::leanh::lean_box(0);
        v___x_2033_ =
            l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(
                v_preferred_2027_,
                v_range_2028_,
                v___x_2032_,
                v_root_2029_,
                v___x_2030_,
            );
        if crate::leanh::lean_obj_tag(v___x_2033_) == 0 {
            return v___x_2030_;
        } else {
            let mut v_val_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_val_2034_ = crate::leanh::lean_ctor_get(v___x_2033_, 0);
            crate::leanh::lean_inc(v_val_2034_);
            crate::leanh::lean_dec_ref_known(v___x_2033_, 1);
            return v_val_2034_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(
    mut v_ctx_x3f_2047_: *mut crate::leanh::LeanObject,
    mut v_i_2048_: *mut crate::leanh::LeanObject,
    mut v_kind_2049_: *mut crate::leanh::LeanObject,
    mut v_tgtRange_2050_: *mut crate::leanh::LeanObject,
    mut v_f_2051_: *mut crate::leanh::LeanObject,
    mut v_canonicalOnly_2052_: u8,
    mut v_as_2053_: *mut crate::leanh::LeanObject,
    mut v_sz_2054_: usize,
    mut v_i_2055_: usize,
    mut v_b_2056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2057_: u8 = 0;
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2062_: u8 = 0;
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2071_: u8 = 0;
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2077_: u8 = 0;
    let mut v_unused_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: usize = 0;
    let mut v___x_2082_: usize = 0;
    let mut v_isSharedCheck_2084_: u8 = 0;
    let mut v_unused_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2057_ = lean_usize_dec_lt(v_i_2055_, v_sz_2054_);
                if v___x_2057_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_2051_);
                    crate::leanh::lean_dec(v_ctx_x3f_2047_);
                    v___x_2058_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2058_, 0, v_b_2056_);
                    return v___x_2058_;
                } else {
                    v_snd_2059_ = crate::leanh::lean_ctor_get(v_b_2056_, 1);
                    v_isSharedCheck_2084_ = (!crate::leanh::lean_is_exclusive(v_b_2056_)) as u8;
                    if v_isSharedCheck_2084_ == 0 {
                        v_unused_2085_ = crate::leanh::lean_ctor_get(v_b_2056_, 0);
                        crate::leanh::lean_dec(v_unused_2085_);
                        v___x_2061_ = v_b_2056_;
                        v_isShared_2062_ = v_isSharedCheck_2084_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2059_);
                        crate::leanh::lean_dec(v_b_2056_);
                        v___x_2061_ = crate::leanh::lean_box(0);
                        v_isShared_2062_ = v_isSharedCheck_2084_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2063_ = crate::leanh::lean_box(0);
                v_a_2064_ = lean_array_uget_borrowed(v_as_2053_, v_i_2055_);
                crate::leanh::lean_inc(v_ctx_x3f_2047_);
                v___x_2065_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_2047_, v_i_2048_);
                crate::leanh::lean_inc_ref(v_f_2051_);
                crate::leanh::lean_inc(v_a_2064_);
                v___x_2066_ = l_Lean_CodeAction_findInfoTree_x3f(
                    v_kind_2049_,
                    v_tgtRange_2050_,
                    v___x_2065_,
                    v_a_2064_,
                    v_f_2051_,
                    v_canonicalOnly_2052_,
                );
                if crate::leanh::lean_obj_tag(v___x_2066_) == 1 {
                    crate::leanh::lean_dec_ref(v_f_2051_);
                    crate::leanh::lean_dec(v_ctx_x3f_2047_);
                    crate::leanh::lean_inc_ref(v___x_2066_);
                    if v_isShared_2062_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2061_, 1, v___x_2063_);
                        crate::leanh::lean_ctor_set(v___x_2061_, 0, v___x_2066_);
                        v___x_2068_ = v___x_2061_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2079_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2066_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 1, v___x_2063_);
                        v___x_2068_ = v_reuseFailAlloc_2079_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2066_);
                    crate::leanh::lean_del_object(v___x_2061_);
                    crate::leanh::lean_dec(v_snd_2059_);
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
                v_isSharedCheck_2077_ = (!crate::leanh::lean_is_exclusive(v___x_2066_)) as u8;
                if v_isSharedCheck_2077_ == 0 {
                    v_unused_2078_ = crate::leanh::lean_ctor_get(v___x_2066_, 0);
                    crate::leanh::lean_dec(v_unused_2078_);
                    v___x_2070_ = v___x_2066_;
                    v_isShared_2071_ = v_isSharedCheck_2077_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2066_);
                    v___x_2070_ = crate::leanh::lean_box(0);
                    v_isShared_2071_ = v_isSharedCheck_2077_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2071_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2070_, 0, v___x_2068_);
                    v___x_2073_ = v___x_2070_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2076_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2068_);
                    v___x_2073_ = v_reuseFailAlloc_2076_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2074_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2074_, 0, v___x_2073_);
                crate::leanh::lean_ctor_set(v___x_2074_, 1, v_snd_2059_);
                v___x_2075_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2075_, 0, v___x_2074_);
                return v___x_2075_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(
    mut v_ctx_x3f_2086_: *mut crate::leanh::LeanObject,
    mut v_i_2087_: *mut crate::leanh::LeanObject,
    mut v_kind_2088_: *mut crate::leanh::LeanObject,
    mut v_tgtRange_2089_: *mut crate::leanh::LeanObject,
    mut v_f_2090_: *mut crate::leanh::LeanObject,
    mut v_canonicalOnly_2091_: u8,
    mut v_as_2092_: *mut crate::leanh::LeanObject,
    mut v_sz_2093_: usize,
    mut v_i_2094_: usize,
    mut v_b_2095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2096_: u8 = 0;
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2101_: u8 = 0;
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2110_: u8 = 0;
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2116_: u8 = 0;
    let mut v_unused_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: usize = 0;
    let mut v___x_2121_: usize = 0;
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2123_: u8 = 0;
    let mut v_unused_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2096_ = lean_usize_dec_lt(v_i_2094_, v_sz_2093_);
                if v___x_2096_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_2090_);
                    crate::leanh::lean_dec(v_ctx_x3f_2086_);
                    v___x_2097_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2097_, 0, v_b_2095_);
                    return v___x_2097_;
                } else {
                    v_snd_2098_ = crate::leanh::lean_ctor_get(v_b_2095_, 1);
                    v_isSharedCheck_2123_ = (!crate::leanh::lean_is_exclusive(v_b_2095_)) as u8;
                    if v_isSharedCheck_2123_ == 0 {
                        v_unused_2124_ = crate::leanh::lean_ctor_get(v_b_2095_, 0);
                        crate::leanh::lean_dec(v_unused_2124_);
                        v___x_2100_ = v_b_2095_;
                        v_isShared_2101_ = v_isSharedCheck_2123_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2098_);
                        crate::leanh::lean_dec(v_b_2095_);
                        v___x_2100_ = crate::leanh::lean_box(0);
                        v_isShared_2101_ = v_isSharedCheck_2123_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2102_ = crate::leanh::lean_box(0);
                v_a_2103_ = lean_array_uget_borrowed(v_as_2092_, v_i_2094_);
                crate::leanh::lean_inc(v_ctx_x3f_2086_);
                v___x_2104_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_2086_, v_i_2087_);
                crate::leanh::lean_inc_ref(v_f_2090_);
                crate::leanh::lean_inc(v_a_2103_);
                v___x_2105_ = l_Lean_CodeAction_findInfoTree_x3f(
                    v_kind_2088_,
                    v_tgtRange_2089_,
                    v___x_2104_,
                    v_a_2103_,
                    v_f_2090_,
                    v_canonicalOnly_2091_,
                );
                if crate::leanh::lean_obj_tag(v___x_2105_) == 1 {
                    crate::leanh::lean_dec_ref(v_f_2090_);
                    crate::leanh::lean_dec(v_ctx_x3f_2086_);
                    crate::leanh::lean_inc_ref(v___x_2105_);
                    if v_isShared_2101_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2100_, 1, v___x_2102_);
                        crate::leanh::lean_ctor_set(v___x_2100_, 0, v___x_2105_);
                        v___x_2107_ = v___x_2100_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2118_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2105_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2118_, 1, v___x_2102_);
                        v___x_2107_ = v_reuseFailAlloc_2118_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2105_);
                    crate::leanh::lean_del_object(v___x_2100_);
                    crate::leanh::lean_dec(v_snd_2098_);
                    v___x_2119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__1;
                    v___x_2120_ = 1usize;
                    v___x_2121_ = lean_usize_add(v_i_2094_, v___x_2120_);
                    v___x_2122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(v_ctx_x3f_2086_, v_i_2087_, v_kind_2088_, v_tgtRange_2089_, v_f_2090_, v_canonicalOnly_2091_, v_as_2092_, v_sz_2093_, v___x_2121_, v___x_2119_);
                    return v___x_2122_;
                }
            }
            2 => {
                v_isSharedCheck_2116_ = (!crate::leanh::lean_is_exclusive(v___x_2105_)) as u8;
                if v_isSharedCheck_2116_ == 0 {
                    v_unused_2117_ = crate::leanh::lean_ctor_get(v___x_2105_, 0);
                    crate::leanh::lean_dec(v_unused_2117_);
                    v___x_2109_ = v___x_2105_;
                    v_isShared_2110_ = v_isSharedCheck_2116_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2105_);
                    v___x_2109_ = crate::leanh::lean_box(0);
                    v_isShared_2110_ = v_isSharedCheck_2116_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2110_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2109_, 0, v___x_2107_);
                    v___x_2112_ = v___x_2109_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2115_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2107_);
                    v___x_2112_ = v_reuseFailAlloc_2115_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2113_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2113_, 0, v___x_2112_);
                crate::leanh::lean_ctor_set(v___x_2113_, 1, v_snd_2098_);
                v___x_2114_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2114_, 0, v___x_2113_);
                return v___x_2114_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(
    mut v_ctx_x3f_2125_: *mut crate::leanh::LeanObject,
    mut v_i_2126_: *mut crate::leanh::LeanObject,
    mut v_kind_2127_: *mut crate::leanh::LeanObject,
    mut v_tgtRange_2128_: *mut crate::leanh::LeanObject,
    mut v_f_2129_: *mut crate::leanh::LeanObject,
    mut v_canonicalOnly_2130_: u8,
    mut v_t_2131_: *mut crate::leanh::LeanObject,
    mut v_init_2132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2140_: u8 = 0;
    let mut v_a_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2148_: usize = 0;
    let mut v___x_2149_: usize = 0;
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2154_: u8 = 0;
    let mut v_fst_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2160_: u8 = 0;
    let mut v_isSharedCheck_2161_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_2133_ = crate::leanh::lean_ctor_get(v_t_2131_, 0);
                v_tail_2134_ = crate::leanh::lean_ctor_get(v_t_2131_, 1);
                crate::leanh::lean_inc_ref(v_f_2129_);
                crate::leanh::lean_inc(v_ctx_x3f_2125_);
                crate::leanh::lean_inc_ref(v_init_2132_);
                v___x_2135_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(v_init_2132_, v_ctx_x3f_2125_, v_i_2126_, v_kind_2127_, v_tgtRange_2128_, v_f_2129_, v_canonicalOnly_2130_, v_root_2133_, v_init_2132_);
                crate::leanh::lean_dec_ref(v_init_2132_);
                if crate::leanh::lean_obj_tag(v___x_2135_) == 0 {
                    crate::leanh::lean_dec_ref(v_f_2129_);
                    crate::leanh::lean_dec(v_ctx_x3f_2125_);
                    v___x_2136_ = crate::leanh::lean_box(0);
                    return v___x_2136_;
                } else {
                    v_val_2137_ = crate::leanh::lean_ctor_get(v___x_2135_, 0);
                    v_isSharedCheck_2161_ = (!crate::leanh::lean_is_exclusive(v___x_2135_)) as u8;
                    if v_isSharedCheck_2161_ == 0 {
                        v___x_2139_ = v___x_2135_;
                        v_isShared_2140_ = v_isSharedCheck_2161_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2137_);
                        crate::leanh::lean_dec(v___x_2135_);
                        v___x_2139_ = crate::leanh::lean_box(0);
                        v_isShared_2140_ = v_isSharedCheck_2161_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_val_2137_) == 0 {
                    crate::leanh::lean_dec_ref(v_f_2129_);
                    crate::leanh::lean_dec(v_ctx_x3f_2125_);
                    v_a_2141_ = crate::leanh::lean_ctor_get(v_val_2137_, 0);
                    crate::leanh::lean_inc(v_a_2141_);
                    crate::leanh::lean_dec_ref_known(v_val_2137_, 1);
                    if v_isShared_2140_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2139_, 0, v_a_2141_);
                        v___x_2143_ = v___x_2139_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2144_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2141_);
                        v___x_2143_ = v_reuseFailAlloc_2144_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2139_);
                    v_a_2145_ = crate::leanh::lean_ctor_get(v_val_2137_, 0);
                    crate::leanh::lean_inc(v_a_2145_);
                    crate::leanh::lean_dec_ref_known(v_val_2137_, 1);
                    v___x_2146_ = crate::leanh::lean_box(0);
                    v___x_2147_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2147_, 0, v___x_2146_);
                    crate::leanh::lean_ctor_set(v___x_2147_, 1, v_a_2145_);
                    v_sz_2148_ = lean_array_size(v_tail_2134_);
                    v___x_2149_ = 0usize;
                    v___x_2150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(v_ctx_x3f_2125_, v_i_2126_, v_kind_2127_, v_tgtRange_2128_, v_f_2129_, v_canonicalOnly_2130_, v_tail_2134_, v_sz_2148_, v___x_2149_, v___x_2147_);
                    if crate::leanh::lean_obj_tag(v___x_2150_) == 0 {
                        return v___x_2146_;
                    } else {
                        v_val_2151_ = crate::leanh::lean_ctor_get(v___x_2150_, 0);
                        v_isSharedCheck_2160_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2150_)) as u8;
                        if v_isSharedCheck_2160_ == 0 {
                            v___x_2153_ = v___x_2150_;
                            v_isShared_2154_ = v_isSharedCheck_2160_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2151_);
                            crate::leanh::lean_dec(v___x_2150_);
                            v___x_2153_ = crate::leanh::lean_box(0);
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
                v_fst_2155_ = crate::leanh::lean_ctor_get(v_val_2151_, 0);
                if crate::leanh::lean_obj_tag(v_fst_2155_) == 0 {
                    v_snd_2156_ = crate::leanh::lean_ctor_get(v_val_2151_, 1);
                    crate::leanh::lean_inc(v_snd_2156_);
                    crate::leanh::lean_dec(v_val_2151_);
                    if v_isShared_2154_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2153_, 0, v_snd_2156_);
                        v___x_2158_ = v___x_2153_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2159_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_snd_2156_);
                        v___x_2158_ = v_reuseFailAlloc_2159_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_2155_);
                    crate::leanh::lean_del_object(v___x_2153_);
                    crate::leanh::lean_dec(v_val_2151_);
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
    mut v_kind_2162_: *mut crate::leanh::LeanObject,
    mut v_tgtRange_2163_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2164_: *mut crate::leanh::LeanObject,
    mut v_t_2165_: *mut crate::leanh::LeanObject,
    mut v_f_2166_: *mut crate::leanh::LeanObject,
    mut v_canonicalOnly_2167_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2182_: u8 = 0;
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: u8 = 0;
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2187_: u8 = 0;
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2192_: u8 = 0;
    let mut v_unused_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: u8 = 0;
    let mut v___x_2199_: u8 = 0;
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_t_2165_) {
                0 => {
                    v_i_2168_ = crate::leanh::lean_ctor_get(v_t_2165_, 0);
                    crate::leanh::lean_inc_ref(v_i_2168_);
                    v_t_2169_ = crate::leanh::lean_ctor_get(v_t_2165_, 1);
                    crate::leanh::lean_inc_ref(v_t_2169_);
                    crate::leanh::lean_dec_ref_known(v_t_2165_, 2);
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
                    v_i_2172_ = crate::leanh::lean_ctor_get(v_t_2165_, 0);
                    v_children_2173_ = crate::leanh::lean_ctor_get(v_t_2165_, 1);
                    if crate::leanh::lean_obj_tag(v_ctx_x3f_2164_) == 1 {
                        v_val_2180_ = crate::leanh::lean_ctor_get(v_ctx_x3f_2164_, 0);
                        v___x_2194_ = l_Lean_Elab_Info_stx(v_i_2172_);
                        v___x_2195_ =
                            l_Lean_Syntax_getRange_x3f(v___x_2194_, v_canonicalOnly_2167_);
                        if crate::leanh::lean_obj_tag(v___x_2195_) == 1 {
                            v_val_2196_ = crate::leanh::lean_ctor_get(v___x_2195_, 0);
                            crate::leanh::lean_inc(v_val_2196_);
                            crate::leanh::lean_dec_ref_known(v___x_2195_, 1);
                            v___x_2197_ = l_Lean_Syntax_getKind(v___x_2194_);
                            v___x_2198_ = lean_name_eq(v___x_2197_, v_kind_2162_);
                            crate::leanh::lean_dec(v___x_2197_);
                            if v___x_2198_ == 0 {
                                crate::leanh::lean_dec(v_val_2196_);
                                v___y_2182_ = v___x_2198_;
                                state = 2;
                                continue;
                            } else {
                                v___x_2199_ =
                                    l_Lean_Syntax_instBEqRange_beq(v_val_2196_, v_tgtRange_2163_);
                                crate::leanh::lean_dec(v_val_2196_);
                                v___y_2182_ = v___x_2199_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_inc_ref(v_children_2173_);
                            crate::leanh::lean_inc_ref(v_i_2172_);
                            crate::leanh::lean_dec(v___x_2195_);
                            crate::leanh::lean_dec(v___x_2194_);
                            crate::leanh::lean_dec_ref_known(v_t_2165_, 2);
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc_ref(v_children_2173_);
                        crate::leanh::lean_inc_ref(v_i_2172_);
                        crate::leanh::lean_dec_ref_known(v_t_2165_, 2);
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_f_2166_);
                    crate::leanh::lean_dec_ref(v_t_2165_);
                    crate::leanh::lean_dec(v_ctx_x3f_2164_);
                    v___x_2200_ = crate::leanh::lean_box(0);
                    return v___x_2200_;
                }
            },
            1 => {
                v___x_2175_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_dec_ref(v_children_2173_);
                crate::leanh::lean_dec_ref(v_i_2172_);
                if crate::leanh::lean_obj_tag(v___x_2177_) == 0 {
                    return v___x_2175_;
                } else {
                    v_val_2178_ = crate::leanh::lean_ctor_get(v___x_2177_, 0);
                    crate::leanh::lean_inc(v_val_2178_);
                    crate::leanh::lean_dec_ref_known(v___x_2177_, 1);
                    v_fst_2179_ = crate::leanh::lean_ctor_get(v_val_2178_, 0);
                    crate::leanh::lean_inc(v_fst_2179_);
                    crate::leanh::lean_dec(v_val_2178_);
                    if crate::leanh::lean_obj_tag(v_fst_2179_) == 0 {
                        return v___x_2175_;
                    } else {
                        return v_fst_2179_;
                    }
                }
            }
            2 => {
                if v___y_2182_ == 0 {
                    crate::leanh::lean_inc_ref(v_children_2173_);
                    crate::leanh::lean_inc_ref(v_i_2172_);
                    crate::leanh::lean_dec_ref_known(v_t_2165_, 2);
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_f_2166_);
                    crate::leanh::lean_inc_ref(v_i_2172_);
                    crate::leanh::lean_inc(v_val_2180_);
                    v___x_2183_ = crate::leanh::lean_apply_2(v_f_2166_, v_val_2180_, v_i_2172_);
                    v___x_2184_ = (crate::leanh::lean_unbox(v___x_2183_) as u8);
                    if v___x_2184_ == 0 {
                        crate::leanh::lean_inc_ref(v_children_2173_);
                        crate::leanh::lean_inc_ref(v_i_2172_);
                        crate::leanh::lean_dec_ref_known(v_t_2165_, 2);
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2180_);
                        crate::leanh::lean_dec_ref(v_f_2166_);
                        v_isSharedCheck_2192_ =
                            (!crate::leanh::lean_is_exclusive(v_ctx_x3f_2164_)) as u8;
                        if v_isSharedCheck_2192_ == 0 {
                            v_unused_2193_ = crate::leanh::lean_ctor_get(v_ctx_x3f_2164_, 0);
                            crate::leanh::lean_dec(v_unused_2193_);
                            v___x_2186_ = v_ctx_x3f_2164_;
                            v_isShared_2187_ = v_isSharedCheck_2192_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_ctx_x3f_2164_);
                            v___x_2186_ = crate::leanh::lean_box(0);
                            v_isShared_2187_ = v_isSharedCheck_2192_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_2188_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2188_, 0, v_val_2180_);
                crate::leanh::lean_ctor_set(v___x_2188_, 1, v_t_2165_);
                if v_isShared_2187_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2186_, 0, v___x_2188_);
                    v___x_2190_ = v___x_2186_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2191_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2188_);
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
    mut v_ctx_x3f_2210_: *mut crate::leanh::LeanObject,
    mut v_i_2211_: *mut crate::leanh::LeanObject,
    mut v_kind_2212_: *mut crate::leanh::LeanObject,
    mut v_tgtRange_2213_: *mut crate::leanh::LeanObject,
    mut v_f_2214_: *mut crate::leanh::LeanObject,
    mut v_canonicalOnly_2215_: u8,
    mut v_as_2216_: *mut crate::leanh::LeanObject,
    mut v_sz_2217_: usize,
    mut v_i_2218_: usize,
    mut v_b_2219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2220_: u8 = 0;
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2225_: u8 = 0;
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2234_: u8 = 0;
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2241_: u8 = 0;
    let mut v_unused_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: usize = 0;
    let mut v___x_2246_: usize = 0;
    let mut v_isSharedCheck_2248_: u8 = 0;
    let mut v_unused_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2220_ = lean_usize_dec_lt(v_i_2218_, v_sz_2217_);
                if v___x_2220_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_2214_);
                    crate::leanh::lean_dec(v_ctx_x3f_2210_);
                    v___x_2221_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2221_, 0, v_b_2219_);
                    return v___x_2221_;
                } else {
                    v_snd_2222_ = crate::leanh::lean_ctor_get(v_b_2219_, 1);
                    v_isSharedCheck_2248_ = (!crate::leanh::lean_is_exclusive(v_b_2219_)) as u8;
                    if v_isSharedCheck_2248_ == 0 {
                        v_unused_2249_ = crate::leanh::lean_ctor_get(v_b_2219_, 0);
                        crate::leanh::lean_dec(v_unused_2249_);
                        v___x_2224_ = v_b_2219_;
                        v_isShared_2225_ = v_isSharedCheck_2248_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2222_);
                        crate::leanh::lean_dec(v_b_2219_);
                        v___x_2224_ = crate::leanh::lean_box(0);
                        v_isShared_2225_ = v_isSharedCheck_2248_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2226_ = crate::leanh::lean_box(0);
                v_a_2227_ = lean_array_uget_borrowed(v_as_2216_, v_i_2218_);
                crate::leanh::lean_inc(v_ctx_x3f_2210_);
                v___x_2228_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_2210_, v_i_2211_);
                crate::leanh::lean_inc_ref(v_f_2214_);
                crate::leanh::lean_inc(v_a_2227_);
                v___x_2229_ = l_Lean_CodeAction_findInfoTree_x3f(
                    v_kind_2212_,
                    v_tgtRange_2213_,
                    v___x_2228_,
                    v_a_2227_,
                    v_f_2214_,
                    v_canonicalOnly_2215_,
                );
                if crate::leanh::lean_obj_tag(v___x_2229_) == 1 {
                    crate::leanh::lean_dec_ref(v_f_2214_);
                    crate::leanh::lean_dec(v_ctx_x3f_2210_);
                    crate::leanh::lean_inc_ref(v___x_2229_);
                    if v_isShared_2225_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2224_, 1, v___x_2226_);
                        crate::leanh::lean_ctor_set(v___x_2224_, 0, v___x_2229_);
                        v___x_2231_ = v___x_2224_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2243_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2229_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 1, v___x_2226_);
                        v___x_2231_ = v_reuseFailAlloc_2243_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2229_);
                    crate::leanh::lean_del_object(v___x_2224_);
                    crate::leanh::lean_dec(v_snd_2222_);
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
                v_isSharedCheck_2241_ = (!crate::leanh::lean_is_exclusive(v___x_2229_)) as u8;
                if v_isSharedCheck_2241_ == 0 {
                    v_unused_2242_ = crate::leanh::lean_ctor_get(v___x_2229_, 0);
                    crate::leanh::lean_dec(v_unused_2242_);
                    v___x_2233_ = v___x_2229_;
                    v_isShared_2234_ = v_isSharedCheck_2241_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2229_);
                    v___x_2233_ = crate::leanh::lean_box(0);
                    v_isShared_2234_ = v_isSharedCheck_2241_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2234_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2233_, 0);
                    crate::leanh::lean_ctor_set(v___x_2233_, 0, v___x_2231_);
                    v___x_2236_ = v___x_2233_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2240_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2231_);
                    v___x_2236_ = v_reuseFailAlloc_2240_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2237_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2237_, 0, v___x_2236_);
                v___x_2238_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2238_, 0, v___x_2237_);
                crate::leanh::lean_ctor_set(v___x_2238_, 1, v_snd_2222_);
                v___x_2239_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2239_, 0, v___x_2238_);
                return v___x_2239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(
    mut v_ctx_x3f_2250_: *mut crate::leanh::LeanObject,
    mut v_i_2251_: *mut crate::leanh::LeanObject,
    mut v_kind_2252_: *mut crate::leanh::LeanObject,
    mut v_tgtRange_2253_: *mut crate::leanh::LeanObject,
    mut v_f_2254_: *mut crate::leanh::LeanObject,
    mut v_canonicalOnly_2255_: u8,
    mut v_as_2256_: *mut crate::leanh::LeanObject,
    mut v_sz_2257_: usize,
    mut v_i_2258_: usize,
    mut v_b_2259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2260_: u8 = 0;
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2265_: u8 = 0;
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2274_: u8 = 0;
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2281_: u8 = 0;
    let mut v_unused_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: usize = 0;
    let mut v___x_2286_: usize = 0;
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2288_: u8 = 0;
    let mut v_unused_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2260_ = lean_usize_dec_lt(v_i_2258_, v_sz_2257_);
                if v___x_2260_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_2254_);
                    crate::leanh::lean_dec(v_ctx_x3f_2250_);
                    v___x_2261_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2261_, 0, v_b_2259_);
                    return v___x_2261_;
                } else {
                    v_snd_2262_ = crate::leanh::lean_ctor_get(v_b_2259_, 1);
                    v_isSharedCheck_2288_ = (!crate::leanh::lean_is_exclusive(v_b_2259_)) as u8;
                    if v_isSharedCheck_2288_ == 0 {
                        v_unused_2289_ = crate::leanh::lean_ctor_get(v_b_2259_, 0);
                        crate::leanh::lean_dec(v_unused_2289_);
                        v___x_2264_ = v_b_2259_;
                        v_isShared_2265_ = v_isSharedCheck_2288_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2262_);
                        crate::leanh::lean_dec(v_b_2259_);
                        v___x_2264_ = crate::leanh::lean_box(0);
                        v_isShared_2265_ = v_isSharedCheck_2288_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2266_ = crate::leanh::lean_box(0);
                v_a_2267_ = lean_array_uget_borrowed(v_as_2256_, v_i_2258_);
                crate::leanh::lean_inc(v_ctx_x3f_2250_);
                v___x_2268_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_2250_, v_i_2251_);
                crate::leanh::lean_inc_ref(v_f_2254_);
                crate::leanh::lean_inc(v_a_2267_);
                v___x_2269_ = l_Lean_CodeAction_findInfoTree_x3f(
                    v_kind_2252_,
                    v_tgtRange_2253_,
                    v___x_2268_,
                    v_a_2267_,
                    v_f_2254_,
                    v_canonicalOnly_2255_,
                );
                if crate::leanh::lean_obj_tag(v___x_2269_) == 1 {
                    crate::leanh::lean_dec_ref(v_f_2254_);
                    crate::leanh::lean_dec(v_ctx_x3f_2250_);
                    crate::leanh::lean_inc_ref(v___x_2269_);
                    if v_isShared_2265_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2264_, 1, v___x_2266_);
                        crate::leanh::lean_ctor_set(v___x_2264_, 0, v___x_2269_);
                        v___x_2271_ = v___x_2264_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2283_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2269_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2283_, 1, v___x_2266_);
                        v___x_2271_ = v_reuseFailAlloc_2283_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2269_);
                    crate::leanh::lean_del_object(v___x_2264_);
                    crate::leanh::lean_dec(v_snd_2262_);
                    v___x_2284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___closed__0;
                    v___x_2285_ = 1usize;
                    v___x_2286_ = lean_usize_add(v_i_2258_, v___x_2285_);
                    v___x_2287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(v_ctx_x3f_2250_, v_i_2251_, v_kind_2252_, v_tgtRange_2253_, v_f_2254_, v_canonicalOnly_2255_, v_as_2256_, v_sz_2257_, v___x_2286_, v___x_2284_);
                    return v___x_2287_;
                }
            }
            2 => {
                v_isSharedCheck_2281_ = (!crate::leanh::lean_is_exclusive(v___x_2269_)) as u8;
                if v_isSharedCheck_2281_ == 0 {
                    v_unused_2282_ = crate::leanh::lean_ctor_get(v___x_2269_, 0);
                    crate::leanh::lean_dec(v_unused_2282_);
                    v___x_2273_ = v___x_2269_;
                    v_isShared_2274_ = v_isSharedCheck_2281_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2269_);
                    v___x_2273_ = crate::leanh::lean_box(0);
                    v_isShared_2274_ = v_isSharedCheck_2281_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2274_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2273_, 0);
                    crate::leanh::lean_ctor_set(v___x_2273_, 0, v___x_2271_);
                    v___x_2276_ = v___x_2273_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2280_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2271_);
                    v___x_2276_ = v_reuseFailAlloc_2280_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2277_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2277_, 0, v___x_2276_);
                v___x_2278_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2278_, 0, v___x_2277_);
                crate::leanh::lean_ctor_set(v___x_2278_, 1, v_snd_2262_);
                v___x_2279_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2279_, 0, v___x_2278_);
                return v___x_2279_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(
    mut v_init_2290_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2291_: *mut crate::leanh::LeanObject,
    mut v_i_2292_: *mut crate::leanh::LeanObject,
    mut v_kind_2293_: *mut crate::leanh::LeanObject,
    mut v_tgtRange_2294_: *mut crate::leanh::LeanObject,
    mut v_f_2295_: *mut crate::leanh::LeanObject,
    mut v_canonicalOnly_2296_: u8,
    mut v_n_2297_: *mut crate::leanh::LeanObject,
    mut v_b_2298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2302_: usize = 0;
    let mut v___x_2303_: usize = 0;
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2308_: u8 = 0;
    let mut v_fst_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2315_: u8 = 0;
    let mut v_vs_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2319_: usize = 0;
    let mut v___x_2320_: usize = 0;
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2325_: u8 = 0;
    let mut v_fst_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2332_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_2297_) == 0 {
                    v_cs_2299_ = crate::leanh::lean_ctor_get(v_n_2297_, 0);
                    v___x_2300_ = crate::leanh::lean_box(0);
                    v___x_2301_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2301_, 0, v___x_2300_);
                    crate::leanh::lean_ctor_set(v___x_2301_, 1, v_b_2298_);
                    v_sz_2302_ = lean_array_size(v_cs_2299_);
                    v___x_2303_ = 0usize;
                    v___x_2304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(v_init_2290_, v_ctx_x3f_2291_, v_i_2292_, v_kind_2293_, v_tgtRange_2294_, v_f_2295_, v_canonicalOnly_2296_, v_cs_2299_, v_sz_2302_, v___x_2303_, v___x_2301_);
                    if crate::leanh::lean_obj_tag(v___x_2304_) == 0 {
                        return v___x_2300_;
                    } else {
                        v_val_2305_ = crate::leanh::lean_ctor_get(v___x_2304_, 0);
                        v_isSharedCheck_2315_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2304_)) as u8;
                        if v_isSharedCheck_2315_ == 0 {
                            v___x_2307_ = v___x_2304_;
                            v_isShared_2308_ = v_isSharedCheck_2315_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2305_);
                            crate::leanh::lean_dec(v___x_2304_);
                            v___x_2307_ = crate::leanh::lean_box(0);
                            v_isShared_2308_ = v_isSharedCheck_2315_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_vs_2316_ = crate::leanh::lean_ctor_get(v_n_2297_, 0);
                    v___x_2317_ = crate::leanh::lean_box(0);
                    v___x_2318_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2318_, 0, v___x_2317_);
                    crate::leanh::lean_ctor_set(v___x_2318_, 1, v_b_2298_);
                    v_sz_2319_ = lean_array_size(v_vs_2316_);
                    v___x_2320_ = 0usize;
                    v___x_2321_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(v_ctx_x3f_2291_, v_i_2292_, v_kind_2293_, v_tgtRange_2294_, v_f_2295_, v_canonicalOnly_2296_, v_vs_2316_, v_sz_2319_, v___x_2320_, v___x_2318_);
                    if crate::leanh::lean_obj_tag(v___x_2321_) == 0 {
                        return v___x_2317_;
                    } else {
                        v_val_2322_ = crate::leanh::lean_ctor_get(v___x_2321_, 0);
                        v_isSharedCheck_2332_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2321_)) as u8;
                        if v_isSharedCheck_2332_ == 0 {
                            v___x_2324_ = v___x_2321_;
                            v_isShared_2325_ = v_isSharedCheck_2332_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2322_);
                            crate::leanh::lean_dec(v___x_2321_);
                            v___x_2324_ = crate::leanh::lean_box(0);
                            v_isShared_2325_ = v_isSharedCheck_2332_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_2309_ = crate::leanh::lean_ctor_get(v_val_2305_, 0);
                if crate::leanh::lean_obj_tag(v_fst_2309_) == 0 {
                    v_snd_2310_ = crate::leanh::lean_ctor_get(v_val_2305_, 1);
                    crate::leanh::lean_inc(v_snd_2310_);
                    crate::leanh::lean_dec(v_val_2305_);
                    v___x_2311_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2311_, 0, v_snd_2310_);
                    if v_isShared_2308_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2307_, 0, v___x_2311_);
                        v___x_2313_ = v___x_2307_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2314_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2311_);
                        v___x_2313_ = v_reuseFailAlloc_2314_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_2309_);
                    crate::leanh::lean_del_object(v___x_2307_);
                    crate::leanh::lean_dec(v_val_2305_);
                    return v_fst_2309_;
                }
            }
            2 => {
                return v___x_2313_;
            }
            3 => {
                v_fst_2326_ = crate::leanh::lean_ctor_get(v_val_2322_, 0);
                if crate::leanh::lean_obj_tag(v_fst_2326_) == 0 {
                    v_snd_2327_ = crate::leanh::lean_ctor_get(v_val_2322_, 1);
                    crate::leanh::lean_inc(v_snd_2327_);
                    crate::leanh::lean_dec(v_val_2322_);
                    v___x_2328_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2328_, 0, v_snd_2327_);
                    if v_isShared_2325_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2324_, 0, v___x_2328_);
                        v___x_2330_ = v___x_2324_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2331_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2328_);
                        v___x_2330_ = v_reuseFailAlloc_2331_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_2326_);
                    crate::leanh::lean_del_object(v___x_2324_);
                    crate::leanh::lean_dec(v_val_2322_);
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
    mut v_init_2333_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2334_: *mut crate::leanh::LeanObject,
    mut v_i_2335_: *mut crate::leanh::LeanObject,
    mut v_kind_2336_: *mut crate::leanh::LeanObject,
    mut v_tgtRange_2337_: *mut crate::leanh::LeanObject,
    mut v_f_2338_: *mut crate::leanh::LeanObject,
    mut v_canonicalOnly_2339_: u8,
    mut v_as_2340_: *mut crate::leanh::LeanObject,
    mut v_sz_2341_: usize,
    mut v_i_2342_: usize,
    mut v_b_2343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2344_: u8 = 0;
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2349_: u8 = 0;
    let mut v_a_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2356_: u8 = 0;
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2363_: u8 = 0;
    let mut v_unused_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: usize = 0;
    let mut v___x_2370_: usize = 0;
    let mut v_reuseFailAlloc_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2373_: u8 = 0;
    let mut v_unused_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2344_ = lean_usize_dec_lt(v_i_2342_, v_sz_2341_);
                if v___x_2344_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_2338_);
                    crate::leanh::lean_dec(v_ctx_x3f_2334_);
                    v___x_2345_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2345_, 0, v_b_2343_);
                    return v___x_2345_;
                } else {
                    v_snd_2346_ = crate::leanh::lean_ctor_get(v_b_2343_, 1);
                    v_isSharedCheck_2373_ = (!crate::leanh::lean_is_exclusive(v_b_2343_)) as u8;
                    if v_isSharedCheck_2373_ == 0 {
                        v_unused_2374_ = crate::leanh::lean_ctor_get(v_b_2343_, 0);
                        crate::leanh::lean_dec(v_unused_2374_);
                        v___x_2348_ = v_b_2343_;
                        v_isShared_2349_ = v_isSharedCheck_2373_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2346_);
                        crate::leanh::lean_dec(v_b_2343_);
                        v___x_2348_ = crate::leanh::lean_box(0);
                        v_isShared_2349_ = v_isSharedCheck_2373_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2350_ = lean_array_uget_borrowed(v_as_2340_, v_i_2342_);
                crate::leanh::lean_inc(v_snd_2346_);
                crate::leanh::lean_inc_ref(v_f_2338_);
                crate::leanh::lean_inc(v_ctx_x3f_2334_);
                v___x_2351_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(v_init_2333_, v_ctx_x3f_2334_, v_i_2335_, v_kind_2336_, v_tgtRange_2337_, v_f_2338_, v_canonicalOnly_2339_, v_a_2350_, v_snd_2346_);
                if crate::leanh::lean_obj_tag(v___x_2351_) == 0 {
                    crate::leanh::lean_del_object(v___x_2348_);
                    crate::leanh::lean_dec(v_snd_2346_);
                    crate::leanh::lean_dec_ref(v_f_2338_);
                    crate::leanh::lean_dec(v_ctx_x3f_2334_);
                    v___x_2352_ = crate::leanh::lean_box(0);
                    return v___x_2352_;
                } else {
                    v_val_2353_ = crate::leanh::lean_ctor_get(v___x_2351_, 0);
                    crate::leanh::lean_inc(v_val_2353_);
                    if crate::leanh::lean_obj_tag(v_val_2353_) == 0 {
                        crate::leanh::lean_dec_ref(v_f_2338_);
                        crate::leanh::lean_dec(v_ctx_x3f_2334_);
                        v_isSharedCheck_2363_ =
                            (!crate::leanh::lean_is_exclusive(v_val_2353_)) as u8;
                        if v_isSharedCheck_2363_ == 0 {
                            v_unused_2364_ = crate::leanh::lean_ctor_get(v_val_2353_, 0);
                            crate::leanh::lean_dec(v_unused_2364_);
                            v___x_2355_ = v_val_2353_;
                            v_isShared_2356_ = v_isSharedCheck_2363_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_val_2353_);
                            v___x_2355_ = crate::leanh::lean_box(0);
                            v_isShared_2356_ = v_isSharedCheck_2363_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_2351_, 1);
                        crate::leanh::lean_dec(v_snd_2346_);
                        v_a_2365_ = crate::leanh::lean_ctor_get(v_val_2353_, 0);
                        crate::leanh::lean_inc(v_a_2365_);
                        crate::leanh::lean_dec_ref_known(v_val_2353_, 1);
                        v___x_2366_ = crate::leanh::lean_box(0);
                        if v_isShared_2349_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2348_, 1, v_a_2365_);
                            crate::leanh::lean_ctor_set(v___x_2348_, 0, v___x_2366_);
                            v___x_2368_ = v___x_2348_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_2372_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2366_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2372_, 1, v_a_2365_);
                            v___x_2368_ = v_reuseFailAlloc_2372_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_2349_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2348_, 0, v___x_2351_);
                    v___x_2358_ = v___x_2348_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2362_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2351_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2362_, 1, v_snd_2346_);
                    v___x_2358_ = v_reuseFailAlloc_2362_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2356_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2355_, 1);
                    crate::leanh::lean_ctor_set(v___x_2355_, 0, v___x_2358_);
                    v___x_2360_ = v___x_2355_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2361_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2358_);
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
    mut v_init_2375_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2376_: *mut crate::leanh::LeanObject,
    mut v_i_2377_: *mut crate::leanh::LeanObject,
    mut v_kind_2378_: *mut crate::leanh::LeanObject,
    mut v_tgtRange_2379_: *mut crate::leanh::LeanObject,
    mut v_f_2380_: *mut crate::leanh::LeanObject,
    mut v_canonicalOnly_2381_: *mut crate::leanh::LeanObject,
    mut v_as_2382_: *mut crate::leanh::LeanObject,
    mut v_sz_2383_: *mut crate::leanh::LeanObject,
    mut v_i_2384_: *mut crate::leanh::LeanObject,
    mut v_b_2385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonicalOnly_boxed_2386_: u8 = 0;
    let mut v_sz_boxed_2387_: usize = 0;
    let mut v_i_boxed_2388_: usize = 0;
    let mut v_res_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_2386_ = (crate::leanh::lean_unbox(v_canonicalOnly_2381_) as u8);
    v_sz_boxed_2387_ = crate::leanh::lean_unbox_usize(v_sz_2383_);
    crate::leanh::lean_dec(v_sz_2383_);
    v_i_boxed_2388_ = crate::leanh::lean_unbox_usize(v_i_2384_);
    crate::leanh::lean_dec(v_i_2384_);
    v_res_2389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(v_init_2375_, v_ctx_x3f_2376_, v_i_2377_, v_kind_2378_, v_tgtRange_2379_, v_f_2380_, v_canonicalOnly_boxed_2386_, v_as_2382_, v_sz_boxed_2387_, v_i_boxed_2388_, v_b_2385_);
    crate::leanh::lean_dec_ref(v_as_2382_);
    crate::leanh::lean_dec_ref(v_tgtRange_2379_);
    crate::leanh::lean_dec(v_kind_2378_);
    crate::leanh::lean_dec_ref(v_i_2377_);
    crate::leanh::lean_dec_ref(v_init_2375_);
    return v_res_2389_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0___boxed(
    mut v_ctx_x3f_2390_: *mut crate::leanh::LeanObject,
    mut v_i_2391_: *mut crate::leanh::LeanObject,
    mut v_kind_2392_: *mut crate::leanh::LeanObject,
    mut v_tgtRange_2393_: *mut crate::leanh::LeanObject,
    mut v_f_2394_: *mut crate::leanh::LeanObject,
    mut v_canonicalOnly_2395_: *mut crate::leanh::LeanObject,
    mut v_t_2396_: *mut crate::leanh::LeanObject,
    mut v_init_2397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonicalOnly_boxed_2398_: u8 = 0;
    let mut v_res_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_2398_ = (crate::leanh::lean_unbox(v_canonicalOnly_2395_) as u8);
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
    crate::leanh::lean_dec_ref(v_t_2396_);
    crate::leanh::lean_dec_ref(v_tgtRange_2393_);
    crate::leanh::lean_dec(v_kind_2392_);
    crate::leanh::lean_dec_ref(v_i_2391_);
    return v_res_2399_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___boxed(
    mut v_ctx_x3f_2400_: *mut crate::leanh::LeanObject,
    mut v_i_2401_: *mut crate::leanh::LeanObject,
    mut v_kind_2402_: *mut crate::leanh::LeanObject,
    mut v_tgtRange_2403_: *mut crate::leanh::LeanObject,
    mut v_f_2404_: *mut crate::leanh::LeanObject,
    mut v_canonicalOnly_2405_: *mut crate::leanh::LeanObject,
    mut v_as_2406_: *mut crate::leanh::LeanObject,
    mut v_sz_2407_: *mut crate::leanh::LeanObject,
    mut v_i_2408_: *mut crate::leanh::LeanObject,
    mut v_b_2409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonicalOnly_boxed_2410_: u8 = 0;
    let mut v_sz_boxed_2411_: usize = 0;
    let mut v_i_boxed_2412_: usize = 0;
    let mut v_res_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_2410_ = (crate::leanh::lean_unbox(v_canonicalOnly_2405_) as u8);
    v_sz_boxed_2411_ = crate::leanh::lean_unbox_usize(v_sz_2407_);
    crate::leanh::lean_dec(v_sz_2407_);
    v_i_boxed_2412_ = crate::leanh::lean_unbox_usize(v_i_2408_);
    crate::leanh::lean_dec(v_i_2408_);
    v_res_2413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(v_ctx_x3f_2400_, v_i_2401_, v_kind_2402_, v_tgtRange_2403_, v_f_2404_, v_canonicalOnly_boxed_2410_, v_as_2406_, v_sz_boxed_2411_, v_i_boxed_2412_, v_b_2409_);
    crate::leanh::lean_dec_ref(v_as_2406_);
    crate::leanh::lean_dec_ref(v_tgtRange_2403_);
    crate::leanh::lean_dec(v_kind_2402_);
    crate::leanh::lean_dec_ref(v_i_2401_);
    return v_res_2413_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___boxed(
    mut v_ctx_x3f_2414_: *mut crate::leanh::LeanObject,
    mut v_i_2415_: *mut crate::leanh::LeanObject,
    mut v_kind_2416_: *mut crate::leanh::LeanObject,
    mut v_tgtRange_2417_: *mut crate::leanh::LeanObject,
    mut v_f_2418_: *mut crate::leanh::LeanObject,
    mut v_canonicalOnly_2419_: *mut crate::leanh::LeanObject,
    mut v_as_2420_: *mut crate::leanh::LeanObject,
    mut v_sz_2421_: *mut crate::leanh::LeanObject,
    mut v_i_2422_: *mut crate::leanh::LeanObject,
    mut v_b_2423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonicalOnly_boxed_2424_: u8 = 0;
    let mut v_sz_boxed_2425_: usize = 0;
    let mut v_i_boxed_2426_: usize = 0;
    let mut v_res_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_2424_ = (crate::leanh::lean_unbox(v_canonicalOnly_2419_) as u8);
    v_sz_boxed_2425_ = crate::leanh::lean_unbox_usize(v_sz_2421_);
    crate::leanh::lean_dec(v_sz_2421_);
    v_i_boxed_2426_ = crate::leanh::lean_unbox_usize(v_i_2422_);
    crate::leanh::lean_dec(v_i_2422_);
    v_res_2427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(v_ctx_x3f_2414_, v_i_2415_, v_kind_2416_, v_tgtRange_2417_, v_f_2418_, v_canonicalOnly_boxed_2424_, v_as_2420_, v_sz_boxed_2425_, v_i_boxed_2426_, v_b_2423_);
    crate::leanh::lean_dec_ref(v_as_2420_);
    crate::leanh::lean_dec_ref(v_tgtRange_2417_);
    crate::leanh::lean_dec(v_kind_2416_);
    crate::leanh::lean_dec_ref(v_i_2415_);
    return v_res_2427_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___boxed(
    mut v_ctx_x3f_2428_: *mut crate::leanh::LeanObject,
    mut v_i_2429_: *mut crate::leanh::LeanObject,
    mut v_kind_2430_: *mut crate::leanh::LeanObject,
    mut v_tgtRange_2431_: *mut crate::leanh::LeanObject,
    mut v_f_2432_: *mut crate::leanh::LeanObject,
    mut v_canonicalOnly_2433_: *mut crate::leanh::LeanObject,
    mut v_as_2434_: *mut crate::leanh::LeanObject,
    mut v_sz_2435_: *mut crate::leanh::LeanObject,
    mut v_i_2436_: *mut crate::leanh::LeanObject,
    mut v_b_2437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonicalOnly_boxed_2438_: u8 = 0;
    let mut v_sz_boxed_2439_: usize = 0;
    let mut v_i_boxed_2440_: usize = 0;
    let mut v_res_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_2438_ = (crate::leanh::lean_unbox(v_canonicalOnly_2433_) as u8);
    v_sz_boxed_2439_ = crate::leanh::lean_unbox_usize(v_sz_2435_);
    crate::leanh::lean_dec(v_sz_2435_);
    v_i_boxed_2440_ = crate::leanh::lean_unbox_usize(v_i_2436_);
    crate::leanh::lean_dec(v_i_2436_);
    v_res_2441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(v_ctx_x3f_2428_, v_i_2429_, v_kind_2430_, v_tgtRange_2431_, v_f_2432_, v_canonicalOnly_boxed_2438_, v_as_2434_, v_sz_boxed_2439_, v_i_boxed_2440_, v_b_2437_);
    crate::leanh::lean_dec_ref(v_as_2434_);
    crate::leanh::lean_dec_ref(v_tgtRange_2431_);
    crate::leanh::lean_dec(v_kind_2430_);
    crate::leanh::lean_dec_ref(v_i_2429_);
    return v_res_2441_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___boxed(
    mut v_ctx_x3f_2442_: *mut crate::leanh::LeanObject,
    mut v_i_2443_: *mut crate::leanh::LeanObject,
    mut v_kind_2444_: *mut crate::leanh::LeanObject,
    mut v_tgtRange_2445_: *mut crate::leanh::LeanObject,
    mut v_f_2446_: *mut crate::leanh::LeanObject,
    mut v_canonicalOnly_2447_: *mut crate::leanh::LeanObject,
    mut v_as_2448_: *mut crate::leanh::LeanObject,
    mut v_sz_2449_: *mut crate::leanh::LeanObject,
    mut v_i_2450_: *mut crate::leanh::LeanObject,
    mut v_b_2451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonicalOnly_boxed_2452_: u8 = 0;
    let mut v_sz_boxed_2453_: usize = 0;
    let mut v_i_boxed_2454_: usize = 0;
    let mut v_res_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_2452_ = (crate::leanh::lean_unbox(v_canonicalOnly_2447_) as u8);
    v_sz_boxed_2453_ = crate::leanh::lean_unbox_usize(v_sz_2449_);
    crate::leanh::lean_dec(v_sz_2449_);
    v_i_boxed_2454_ = crate::leanh::lean_unbox_usize(v_i_2450_);
    crate::leanh::lean_dec(v_i_2450_);
    v_res_2455_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(v_ctx_x3f_2442_, v_i_2443_, v_kind_2444_, v_tgtRange_2445_, v_f_2446_, v_canonicalOnly_boxed_2452_, v_as_2448_, v_sz_boxed_2453_, v_i_boxed_2454_, v_b_2451_);
    crate::leanh::lean_dec_ref(v_as_2448_);
    crate::leanh::lean_dec_ref(v_tgtRange_2445_);
    crate::leanh::lean_dec(v_kind_2444_);
    crate::leanh::lean_dec_ref(v_i_2443_);
    return v_res_2455_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0___boxed(
    mut v_init_2456_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2457_: *mut crate::leanh::LeanObject,
    mut v_i_2458_: *mut crate::leanh::LeanObject,
    mut v_kind_2459_: *mut crate::leanh::LeanObject,
    mut v_tgtRange_2460_: *mut crate::leanh::LeanObject,
    mut v_f_2461_: *mut crate::leanh::LeanObject,
    mut v_canonicalOnly_2462_: *mut crate::leanh::LeanObject,
    mut v_n_2463_: *mut crate::leanh::LeanObject,
    mut v_b_2464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonicalOnly_boxed_2465_: u8 = 0;
    let mut v_res_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_2465_ = (crate::leanh::lean_unbox(v_canonicalOnly_2462_) as u8);
    v_res_2466_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(v_init_2456_, v_ctx_x3f_2457_, v_i_2458_, v_kind_2459_, v_tgtRange_2460_, v_f_2461_, v_canonicalOnly_boxed_2465_, v_n_2463_, v_b_2464_);
    crate::leanh::lean_dec_ref(v_n_2463_);
    crate::leanh::lean_dec_ref(v_tgtRange_2460_);
    crate::leanh::lean_dec(v_kind_2459_);
    crate::leanh::lean_dec_ref(v_i_2458_);
    crate::leanh::lean_dec_ref(v_init_2456_);
    return v_res_2466_;
}
pub unsafe fn l_Lean_CodeAction_findInfoTree_x3f___boxed(
    mut v_kind_2467_: *mut crate::leanh::LeanObject,
    mut v_tgtRange_2468_: *mut crate::leanh::LeanObject,
    mut v_ctx_x3f_2469_: *mut crate::leanh::LeanObject,
    mut v_t_2470_: *mut crate::leanh::LeanObject,
    mut v_f_2471_: *mut crate::leanh::LeanObject,
    mut v_canonicalOnly_2472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonicalOnly_boxed_2473_: u8 = 0;
    let mut v_res_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_2473_ = (crate::leanh::lean_unbox(v_canonicalOnly_2472_) as u8);
    v_res_2474_ = l_Lean_CodeAction_findInfoTree_x3f(
        v_kind_2467_,
        v_tgtRange_2468_,
        v_ctx_x3f_2469_,
        v_t_2470_,
        v_f_2471_,
        v_canonicalOnly_boxed_2473_,
    );
    crate::leanh::lean_dec_ref(v_tgtRange_2468_);
    crate::leanh::lean_dec(v_kind_2467_);
    return v_res_2474_;
}
pub unsafe fn _init_l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2475_ = l_Lean_Server_instInhabitedRequestError_default;
    v___x_2476_ = crate::leanh::lean_alloc_closure(
        l_instInhabitedEIO___aux__1___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___x_2476_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2476_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2476_, 2, v___x_2475_);
    return v___x_2476_;
}
pub unsafe fn l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(
    mut v_msg_2477_: *mut crate::leanh::LeanObject,
    mut v___y_2478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028__overap_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2480_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0_once
        ),
        _init_l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0,
    );
    v___f_2481_ = crate::leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2481_, 0, v___x_2480_);
    v___x_4028__overap_2482_ = lean_panic_fn_borrowed(v___f_2481_, v_msg_2477_);
    crate::leanh::lean_dec_ref(v___f_2481_);
    crate::leanh::lean_inc_ref(v___y_2478_);
    v___x_2483_ = crate::leanh::lean_apply_2(
        v___x_4028__overap_2482_,
        v___y_2478_,
        crate::leanh::lean_box(0),
    );
    return v___x_2483_;
}
pub unsafe fn l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___boxed(
    mut v_msg_2484_: *mut crate::leanh::LeanObject,
    mut v___y_2485_: *mut crate::leanh::LeanObject,
    mut v___y_2486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2487_ =
        l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(v_msg_2484_, v___y_2485_);
    crate::leanh::lean_dec_ref(v___y_2485_);
    return v_res_2487_;
}
pub unsafe fn l_Lean_CodeAction_cmdCodeActionProvider___lam__0(
    mut v___x_2488_: *mut crate::leanh::LeanObject,
    mut v___x_2489_: *mut crate::leanh::LeanObject,
    mut v_ctx_2490_: *mut crate::leanh::LeanObject,
    mut v_node_2491_: *mut crate::leanh::LeanObject,
    mut v_result_2492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2494_: u8 = 0;
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: u8 = 0;
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: u8 = 0;
    let mut v___x_2506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_node_2491_) == 1 {
                    v_i_2497_ = crate::leanh::lean_ctor_get(v_node_2491_, 0);
                    if crate::leanh::lean_obj_tag(v_i_2497_) == 3 {
                        v_i_2498_ = crate::leanh::lean_ctor_get(v_i_2497_, 0);
                        v_stx_2499_ = crate::leanh::lean_ctor_get(v_i_2498_, 1);
                        v___x_2500_ = 1;
                        v___x_2501_ = l_Lean_Syntax_getPos_x3f(v_stx_2499_, v___x_2500_);
                        if crate::leanh::lean_obj_tag(v___x_2501_) == 1 {
                            v_val_2502_ = crate::leanh::lean_ctor_get(v___x_2501_, 0);
                            crate::leanh::lean_inc(v_val_2502_);
                            crate::leanh::lean_dec_ref_known(v___x_2501_, 1);
                            v___x_2503_ = l_Lean_Syntax_getTailPos_x3f(v_stx_2499_, v___x_2500_);
                            if crate::leanh::lean_obj_tag(v___x_2503_) == 1 {
                                v_val_2504_ = crate::leanh::lean_ctor_get(v___x_2503_, 0);
                                crate::leanh::lean_inc(v_val_2504_);
                                crate::leanh::lean_dec_ref_known(v___x_2503_, 1);
                                v___x_2505_ = lean_nat_dec_le(v_val_2502_, v___x_2488_);
                                crate::leanh::lean_dec(v_val_2502_);
                                if v___x_2505_ == 0 {
                                    crate::leanh::lean_dec(v_val_2504_);
                                    v___y_2494_ = v___x_2505_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_2506_ = lean_nat_dec_le(v___x_2489_, v_val_2504_);
                                    crate::leanh::lean_dec(v_val_2504_);
                                    v___y_2494_ = v___x_2506_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_2503_);
                                crate::leanh::lean_dec(v_val_2502_);
                                crate::leanh::lean_dec_ref_known(v_node_2491_, 2);
                                crate::leanh::lean_dec_ref(v_ctx_2490_);
                                return v_result_2492_;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_2501_);
                            crate::leanh::lean_dec_ref_known(v_node_2491_, 2);
                            crate::leanh::lean_dec_ref(v_ctx_2490_);
                            return v_result_2492_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_node_2491_, 2);
                        crate::leanh::lean_dec_ref(v_ctx_2490_);
                        return v_result_2492_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_node_2491_);
                    crate::leanh::lean_dec_ref(v_ctx_2490_);
                    return v_result_2492_;
                }
            }
            1 => {
                if v___y_2494_ == 0 {
                    crate::leanh::lean_dec_ref(v_node_2491_);
                    crate::leanh::lean_dec_ref(v_ctx_2490_);
                    return v_result_2492_;
                } else {
                    v___x_2495_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2495_, 0, v_ctx_2490_);
                    crate::leanh::lean_ctor_set(v___x_2495_, 1, v_node_2491_);
                    v___x_2496_ = lean_array_push(v_result_2492_, v___x_2495_);
                    return v___x_2496_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_CodeAction_cmdCodeActionProvider___lam__0___boxed(
    mut v___x_2507_: *mut crate::leanh::LeanObject,
    mut v___x_2508_: *mut crate::leanh::LeanObject,
    mut v_ctx_2509_: *mut crate::leanh::LeanObject,
    mut v_node_2510_: *mut crate::leanh::LeanObject,
    mut v_result_2511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2512_ = l_Lean_CodeAction_cmdCodeActionProvider___lam__0(
        v___x_2507_,
        v___x_2508_,
        v_ctx_2509_,
        v_node_2510_,
        v_result_2511_,
    );
    crate::leanh::lean_dec(v___x_2508_);
    crate::leanh::lean_dec(v___x_2507_);
    return v_res_2512_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(
    mut v_params_2513_: *mut crate::leanh::LeanObject,
    mut v_snap_2514_: *mut crate::leanh::LeanObject,
    mut v_fst_2515_: *mut crate::leanh::LeanObject,
    mut v_snd_2516_: *mut crate::leanh::LeanObject,
    mut v_as_2517_: *mut crate::leanh::LeanObject,
    mut v_sz_2518_: usize,
    mut v_i_2519_: usize,
    mut v_b_2520_: *mut crate::leanh::LeanObject,
    mut v___y_2521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: usize = 0;
    let mut v___x_2526_: usize = 0;
    let mut v___x_2528_: u8 = 0;
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662__overap_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2528_ = lean_usize_dec_lt(v_i_2519_, v_sz_2518_);
                if v___x_2528_ == 0 {
                    crate::leanh::lean_dec_ref(v_snd_2516_);
                    crate::leanh::lean_dec_ref(v_fst_2515_);
                    crate::leanh::lean_dec_ref(v_snap_2514_);
                    crate::leanh::lean_dec_ref(v_params_2513_);
                    v___x_2529_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2529_, 0, v_b_2520_);
                    return v___x_2529_;
                } else {
                    v___x_4662__overap_2530_ = lean_array_uget_borrowed(v_as_2517_, v_i_2519_);
                    crate::leanh::lean_inc(v___x_4662__overap_2530_);
                    crate::leanh::lean_inc_ref(v___y_2521_);
                    crate::leanh::lean_inc_ref(v_snd_2516_);
                    crate::leanh::lean_inc_ref(v_fst_2515_);
                    crate::leanh::lean_inc_ref(v_snap_2514_);
                    crate::leanh::lean_inc_ref(v_params_2513_);
                    v___x_2531_ = crate::leanh::lean_apply_6(
                        v___x_4662__overap_2530_,
                        v_params_2513_,
                        v_snap_2514_,
                        v_fst_2515_,
                        v_snd_2516_,
                        v___y_2521_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_2531_) == 0 {
                        v_a_2532_ = crate::leanh::lean_ctor_get(v___x_2531_, 0);
                        crate::leanh::lean_inc(v_a_2532_);
                        crate::leanh::lean_dec_ref_known(v___x_2531_, 1);
                        v___x_2533_ = l_Array_append___redArg(v_b_2520_, v_a_2532_);
                        crate::leanh::lean_dec(v_a_2532_);
                        v_snd_2524_ = v___x_2533_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_2531_, 1);
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
    mut v_params_2534_: *mut crate::leanh::LeanObject,
    mut v_snap_2535_: *mut crate::leanh::LeanObject,
    mut v_fst_2536_: *mut crate::leanh::LeanObject,
    mut v_snd_2537_: *mut crate::leanh::LeanObject,
    mut v_as_2538_: *mut crate::leanh::LeanObject,
    mut v_sz_2539_: *mut crate::leanh::LeanObject,
    mut v_i_2540_: *mut crate::leanh::LeanObject,
    mut v_b_2541_: *mut crate::leanh::LeanObject,
    mut v___y_2542_: *mut crate::leanh::LeanObject,
    mut v___y_2543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2544_: usize = 0;
    let mut v_i_boxed_2545_: usize = 0;
    let mut v_res_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2544_ = crate::leanh::lean_unbox_usize(v_sz_2539_);
    crate::leanh::lean_dec(v_sz_2539_);
    v_i_boxed_2545_ = crate::leanh::lean_unbox_usize(v_i_2540_);
    crate::leanh::lean_dec(v_i_2540_);
    v_res_2546_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_2534_, v_snap_2535_, v_fst_2536_, v_snd_2537_, v_as_2538_, v_sz_boxed_2544_, v_i_boxed_2545_, v_b_2541_, v___y_2542_);
    crate::leanh::lean_dec_ref(v___y_2542_);
    crate::leanh::lean_dec_ref(v_as_2538_);
    return v_res_2546_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__2;
    v___x_2551_ = crate::leanh::lean_unsigned_to_nat(48);
    v___x_2552_ = crate::leanh::lean_unsigned_to_nat(185);
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
    mut v___x_2556_: *mut crate::leanh::LeanObject,
    mut v_params_2557_: *mut crate::leanh::LeanObject,
    mut v_snap_2558_: *mut crate::leanh::LeanObject,
    mut v_as_2559_: *mut crate::leanh::LeanObject,
    mut v_sz_2560_: usize,
    mut v_i_2561_: usize,
    mut v_b_2562_: *mut crate::leanh::LeanObject,
    mut v___y_2563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: usize = 0;
    let mut v___x_2568_: usize = 0;
    let mut v___y_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2577_: u8 = 0;
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2581_: u8 = 0;
    let mut v___x_2582_: u8 = 0;
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_onAnyCmd_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_onCmd_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2594_: usize = 0;
    let mut v___x_2595_: usize = 0;
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2602_: usize = 0;
    let mut v___x_2603_: usize = 0;
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2582_ = lean_usize_dec_lt(v_i_2561_, v_sz_2560_);
                if v___x_2582_ == 0 {
                    crate::leanh::lean_dec_ref(v_snap_2558_);
                    crate::leanh::lean_dec_ref(v_params_2557_);
                    v___x_2583_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2583_, 0, v_b_2562_);
                    return v___x_2583_;
                } else {
                    v_a_2584_ = lean_array_uget_borrowed(v_as_2559_, v_i_2561_);
                    v_snd_2585_ = crate::leanh::lean_ctor_get(v_a_2584_, 1);
                    if crate::leanh::lean_obj_tag(v_snd_2585_) == 1 {
                        v_i_2586_ = crate::leanh::lean_ctor_get(v_snd_2585_, 0);
                        if crate::leanh::lean_obj_tag(v_i_2586_) == 3 {
                            v_fst_2587_ = crate::leanh::lean_ctor_get(v_a_2584_, 0);
                            v_i_2588_ = crate::leanh::lean_ctor_get(v_i_2586_, 0);
                            v_onAnyCmd_2589_ = crate::leanh::lean_ctor_get(v___x_2556_, 0);
                            v_onCmd_2590_ = crate::leanh::lean_ctor_get(v___x_2556_, 1);
                            v_stx_2598_ = crate::leanh::lean_ctor_get(v_i_2588_, 1);
                            crate::leanh::lean_inc(v_stx_2598_);
                            v___x_2599_ = l_Lean_Syntax_getKind(v_stx_2598_);
                            v___x_2600_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_onCmd_2590_, v___x_2599_);
                            crate::leanh::lean_dec(v___x_2599_);
                            if crate::leanh::lean_obj_tag(v___x_2600_) == 1 {
                                v_val_2601_ = crate::leanh::lean_ctor_get(v___x_2600_, 0);
                                crate::leanh::lean_inc(v_val_2601_);
                                crate::leanh::lean_dec_ref_known(v___x_2600_, 1);
                                v_sz_2602_ = lean_array_size(v_val_2601_);
                                v___x_2603_ = 0usize;
                                crate::leanh::lean_inc_ref(v_snd_2585_);
                                crate::leanh::lean_inc(v_fst_2587_);
                                crate::leanh::lean_inc_ref(v_snap_2558_);
                                crate::leanh::lean_inc_ref(v_params_2557_);
                                v___x_2604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_2557_, v_snap_2558_, v_fst_2587_, v_snd_2585_, v_val_2601_, v_sz_2602_, v___x_2603_, v_b_2562_, v___y_2563_);
                                crate::leanh::lean_dec(v_val_2601_);
                                if crate::leanh::lean_obj_tag(v___x_2604_) == 0 {
                                    v_a_2605_ = crate::leanh::lean_ctor_get(v___x_2604_, 0);
                                    crate::leanh::lean_inc(v_a_2605_);
                                    crate::leanh::lean_dec_ref_known(v___x_2604_, 1);
                                    v_out_2592_ = v_a_2605_;
                                    v___y_2593_ = v___y_2563_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v_snap_2558_);
                                    crate::leanh::lean_dec_ref(v_params_2557_);
                                    return v___x_2604_;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_2600_);
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
                v___x_2572_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3);
                v___x_2573_ = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(
                    v___x_2572_,
                    v___y_2571_,
                );
                if crate::leanh::lean_obj_tag(v___x_2573_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2573_, 1);
                    v_a_2566_ = v_b_2562_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_b_2562_);
                    crate::leanh::lean_dec_ref(v_snap_2558_);
                    crate::leanh::lean_dec_ref(v_params_2557_);
                    v_a_2574_ = crate::leanh::lean_ctor_get(v___x_2573_, 0);
                    v_isSharedCheck_2581_ = (!crate::leanh::lean_is_exclusive(v___x_2573_)) as u8;
                    if v_isSharedCheck_2581_ == 0 {
                        v___x_2576_ = v___x_2573_;
                        v_isShared_2577_ = v_isSharedCheck_2581_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2574_);
                        crate::leanh::lean_dec(v___x_2573_);
                        v___x_2576_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2580_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
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
                crate::leanh::lean_inc_ref(v_snd_2585_);
                crate::leanh::lean_inc(v_fst_2587_);
                crate::leanh::lean_inc_ref(v_snap_2558_);
                crate::leanh::lean_inc_ref(v_params_2557_);
                v___x_2596_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_2557_, v_snap_2558_, v_fst_2587_, v_snd_2585_, v_onAnyCmd_2589_, v_sz_2594_, v___x_2595_, v_out_2592_, v___y_2593_);
                if crate::leanh::lean_obj_tag(v___x_2596_) == 0 {
                    v_a_2597_ = crate::leanh::lean_ctor_get(v___x_2596_, 0);
                    crate::leanh::lean_inc(v_a_2597_);
                    crate::leanh::lean_dec_ref_known(v___x_2596_, 1);
                    v_a_2566_ = v_a_2597_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_snap_2558_);
                    crate::leanh::lean_dec_ref(v_params_2557_);
                    return v___x_2596_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___boxed(
    mut v___x_2606_: *mut crate::leanh::LeanObject,
    mut v_params_2607_: *mut crate::leanh::LeanObject,
    mut v_snap_2608_: *mut crate::leanh::LeanObject,
    mut v_as_2609_: *mut crate::leanh::LeanObject,
    mut v_sz_2610_: *mut crate::leanh::LeanObject,
    mut v_i_2611_: *mut crate::leanh::LeanObject,
    mut v_b_2612_: *mut crate::leanh::LeanObject,
    mut v___y_2613_: *mut crate::leanh::LeanObject,
    mut v___y_2614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2615_: usize = 0;
    let mut v_i_boxed_2616_: usize = 0;
    let mut v_res_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2615_ = crate::leanh::lean_unbox_usize(v_sz_2610_);
    crate::leanh::lean_dec(v_sz_2610_);
    v_i_boxed_2616_ = crate::leanh::lean_unbox_usize(v_i_2611_);
    crate::leanh::lean_dec(v_i_2611_);
    v_res_2617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(v___x_2606_, v_params_2607_, v_snap_2608_, v_as_2609_, v_sz_boxed_2615_, v_i_boxed_2616_, v_b_2612_, v___y_2613_);
    crate::leanh::lean_dec_ref(v___y_2613_);
    crate::leanh::lean_dec_ref(v_as_2609_);
    crate::leanh::lean_dec_ref(v___x_2606_);
    return v_res_2617_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(
    mut v_params_2618_: *mut crate::leanh::LeanObject,
    mut v_snap_2619_: *mut crate::leanh::LeanObject,
    mut v___x_2620_: *mut crate::leanh::LeanObject,
    mut v_as_2621_: *mut crate::leanh::LeanObject,
    mut v_sz_2622_: usize,
    mut v_i_2623_: usize,
    mut v_b_2624_: *mut crate::leanh::LeanObject,
    mut v___y_2625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: usize = 0;
    let mut v___x_2630_: usize = 0;
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2639_: u8 = 0;
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2643_: u8 = 0;
    let mut v___x_2644_: u8 = 0;
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_onAnyCmd_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_onCmd_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2656_: usize = 0;
    let mut v___x_2657_: usize = 0;
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2664_: usize = 0;
    let mut v___x_2665_: usize = 0;
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2644_ = lean_usize_dec_lt(v_i_2623_, v_sz_2622_);
                if v___x_2644_ == 0 {
                    crate::leanh::lean_dec_ref(v_snap_2619_);
                    crate::leanh::lean_dec_ref(v_params_2618_);
                    v___x_2645_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2645_, 0, v_b_2624_);
                    return v___x_2645_;
                } else {
                    v_a_2646_ = lean_array_uget_borrowed(v_as_2621_, v_i_2623_);
                    v_snd_2647_ = crate::leanh::lean_ctor_get(v_a_2646_, 1);
                    if crate::leanh::lean_obj_tag(v_snd_2647_) == 1 {
                        v_i_2648_ = crate::leanh::lean_ctor_get(v_snd_2647_, 0);
                        if crate::leanh::lean_obj_tag(v_i_2648_) == 3 {
                            v_fst_2649_ = crate::leanh::lean_ctor_get(v_a_2646_, 0);
                            v_i_2650_ = crate::leanh::lean_ctor_get(v_i_2648_, 0);
                            v_onAnyCmd_2651_ = crate::leanh::lean_ctor_get(v___x_2620_, 0);
                            v_onCmd_2652_ = crate::leanh::lean_ctor_get(v___x_2620_, 1);
                            v_stx_2660_ = crate::leanh::lean_ctor_get(v_i_2650_, 1);
                            crate::leanh::lean_inc(v_stx_2660_);
                            v___x_2661_ = l_Lean_Syntax_getKind(v_stx_2660_);
                            v___x_2662_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_onCmd_2652_, v___x_2661_);
                            crate::leanh::lean_dec(v___x_2661_);
                            if crate::leanh::lean_obj_tag(v___x_2662_) == 1 {
                                v_val_2663_ = crate::leanh::lean_ctor_get(v___x_2662_, 0);
                                crate::leanh::lean_inc(v_val_2663_);
                                crate::leanh::lean_dec_ref_known(v___x_2662_, 1);
                                v_sz_2664_ = lean_array_size(v_val_2663_);
                                v___x_2665_ = 0usize;
                                crate::leanh::lean_inc_ref(v_snd_2647_);
                                crate::leanh::lean_inc(v_fst_2649_);
                                crate::leanh::lean_inc_ref(v_snap_2619_);
                                crate::leanh::lean_inc_ref(v_params_2618_);
                                v___x_2666_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_2618_, v_snap_2619_, v_fst_2649_, v_snd_2647_, v_val_2663_, v_sz_2664_, v___x_2665_, v_b_2624_, v___y_2625_);
                                crate::leanh::lean_dec(v_val_2663_);
                                if crate::leanh::lean_obj_tag(v___x_2666_) == 0 {
                                    v_a_2667_ = crate::leanh::lean_ctor_get(v___x_2666_, 0);
                                    crate::leanh::lean_inc(v_a_2667_);
                                    crate::leanh::lean_dec_ref_known(v___x_2666_, 1);
                                    v_out_2654_ = v_a_2667_;
                                    v___y_2655_ = v___y_2625_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v_snap_2619_);
                                    crate::leanh::lean_dec_ref(v_params_2618_);
                                    return v___x_2666_;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_2662_);
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
                v___x_2634_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3);
                v___x_2635_ = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(
                    v___x_2634_,
                    v___y_2633_,
                );
                if crate::leanh::lean_obj_tag(v___x_2635_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2635_, 1);
                    v_a_2628_ = v_b_2624_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_b_2624_);
                    crate::leanh::lean_dec_ref(v_snap_2619_);
                    crate::leanh::lean_dec_ref(v_params_2618_);
                    v_a_2636_ = crate::leanh::lean_ctor_get(v___x_2635_, 0);
                    v_isSharedCheck_2643_ = (!crate::leanh::lean_is_exclusive(v___x_2635_)) as u8;
                    if v_isSharedCheck_2643_ == 0 {
                        v___x_2638_ = v___x_2635_;
                        v_isShared_2639_ = v_isSharedCheck_2643_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2636_);
                        crate::leanh::lean_dec(v___x_2635_);
                        v___x_2638_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2642_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
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
                crate::leanh::lean_inc_ref(v_snd_2647_);
                crate::leanh::lean_inc(v_fst_2649_);
                crate::leanh::lean_inc_ref(v_snap_2619_);
                crate::leanh::lean_inc_ref(v_params_2618_);
                v___x_2658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_2618_, v_snap_2619_, v_fst_2649_, v_snd_2647_, v_onAnyCmd_2651_, v_sz_2656_, v___x_2657_, v_out_2654_, v___y_2655_);
                if crate::leanh::lean_obj_tag(v___x_2658_) == 0 {
                    v_a_2659_ = crate::leanh::lean_ctor_get(v___x_2658_, 0);
                    crate::leanh::lean_inc(v_a_2659_);
                    crate::leanh::lean_dec_ref_known(v___x_2658_, 1);
                    v_a_2628_ = v_a_2659_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_snap_2619_);
                    crate::leanh::lean_dec_ref(v_params_2618_);
                    return v___x_2658_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2___boxed(
    mut v_params_2668_: *mut crate::leanh::LeanObject,
    mut v_snap_2669_: *mut crate::leanh::LeanObject,
    mut v___x_2670_: *mut crate::leanh::LeanObject,
    mut v_as_2671_: *mut crate::leanh::LeanObject,
    mut v_sz_2672_: *mut crate::leanh::LeanObject,
    mut v_i_2673_: *mut crate::leanh::LeanObject,
    mut v_b_2674_: *mut crate::leanh::LeanObject,
    mut v___y_2675_: *mut crate::leanh::LeanObject,
    mut v___y_2676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2677_: usize = 0;
    let mut v_i_boxed_2678_: usize = 0;
    let mut v_res_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2677_ = crate::leanh::lean_unbox_usize(v_sz_2672_);
    crate::leanh::lean_dec(v_sz_2672_);
    v_i_boxed_2678_ = crate::leanh::lean_unbox_usize(v_i_2673_);
    crate::leanh::lean_dec(v_i_2673_);
    v_res_2679_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(v_params_2668_, v_snap_2669_, v___x_2670_, v_as_2671_, v_sz_boxed_2677_, v_i_boxed_2678_, v_b_2674_, v___y_2675_);
    crate::leanh::lean_dec_ref(v___y_2675_);
    crate::leanh::lean_dec_ref(v_as_2671_);
    crate::leanh::lean_dec_ref(v___x_2670_);
    return v_res_2679_;
}
pub unsafe fn _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2680_ = l_Array_instInhabited(crate::leanh::lean_box(0));
    return v___x_2680_;
}
pub unsafe fn _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2681_ = l_Lean_CodeAction_instInhabitedCommandCodeActions_default;
    v___x_2682_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_CodeAction_cmdCodeActionProvider___closed__0),
        core::ptr::addr_of_mut!(l_Lean_CodeAction_cmdCodeActionProvider___closed__0_once),
        _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__0,
    );
    v___x_2683_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2683_, 0, v___x_2682_);
    crate::leanh::lean_ctor_set(v___x_2683_, 1, v___x_2681_);
    return v___x_2683_;
}
pub unsafe fn l_Lean_CodeAction_cmdCodeActionProvider(
    mut v_params_2686_: *mut crate::leanh::LeanObject,
    mut v_snap_2687_: *mut crate::leanh::LeanObject,
    mut v_a_2688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEditableDocumentCore_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_meta_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_end_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2712_: usize = 0;
    let mut v___x_2713_: usize = 0;
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2690_ =
        l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(
            v_a_2688_,
        );
    v_a_2691_ = crate::leanh::lean_ctor_get(v___x_2690_, 0);
    crate::leanh::lean_inc(v_a_2691_);
    crate::leanh::lean_dec_ref(v___x_2690_);
    v_toEditableDocumentCore_2692_ = crate::leanh::lean_ctor_get(v_a_2691_, 0);
    crate::leanh::lean_inc_ref(v_toEditableDocumentCore_2692_);
    crate::leanh::lean_dec(v_a_2691_);
    v_meta_2693_ = crate::leanh::lean_ctor_get(v_toEditableDocumentCore_2692_, 0);
    crate::leanh::lean_inc_ref(v_meta_2693_);
    crate::leanh::lean_dec_ref(v_toEditableDocumentCore_2692_);
    v_range_2694_ = crate::leanh::lean_ctor_get(v_params_2686_, 3);
    v_text_2695_ = crate::leanh::lean_ctor_get(v_meta_2693_, 3);
    crate::leanh::lean_inc_ref(v_text_2695_);
    crate::leanh::lean_dec_ref(v_meta_2693_);
    v_start_2696_ = crate::leanh::lean_ctor_get(v_range_2694_, 0);
    v_end_2697_ = crate::leanh::lean_ctor_get(v_range_2694_, 1);
    v___x_2698_ = l_Lean_CodeAction_cmdCodeActionExt;
    v_toEnvExtension_2699_ = crate::leanh::lean_ctor_get(v___x_2698_, 0);
    v_asyncMode_2700_ = crate::leanh::lean_ctor_get(v_toEnvExtension_2699_, 2);
    v___x_2701_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_CodeAction_cmdCodeActionProvider___closed__1),
        core::ptr::addr_of_mut!(l_Lean_CodeAction_cmdCodeActionProvider___closed__1_once),
        _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__1,
    );
    v___x_2702_ = l_Lean_Server_Snapshots_Snapshot_env(v_snap_2687_);
    v___x_2703_ = crate::leanh::lean_box(0);
    v___x_2704_ = l_Lean_PersistentEnvExtension_getState___redArg(
        v___x_2701_,
        v___x_2698_,
        v___x_2702_,
        v_asyncMode_2700_,
        v___x_2703_,
    );
    v_snd_2705_ = crate::leanh::lean_ctor_get(v___x_2704_, 1);
    crate::leanh::lean_inc(v_snd_2705_);
    crate::leanh::lean_dec(v___x_2704_);
    crate::leanh::lean_inc_ref(v_start_2696_);
    v___x_2706_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_2695_, v_start_2696_);
    crate::leanh::lean_inc_ref(v_end_2697_);
    v___x_2707_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_2695_, v_end_2697_);
    crate::leanh::lean_dec_ref(v_text_2695_);
    v___f_2708_ = crate::leanh::lean_alloc_closure(
        l_Lean_CodeAction_cmdCodeActionProvider___lam__0___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2708_, 0, v___x_2707_);
    crate::leanh::lean_closure_set(v___f_2708_, 1, v___x_2706_);
    v___x_2709_ = l_Lean_CodeAction_cmdCodeActionProvider___closed__2;
    crate::leanh::lean_inc_ref(v_snap_2687_);
    v___x_2710_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_snap_2687_);
    v___x_2711_ = l_Lean_Elab_InfoTree_foldInfoTree___redArg(v___x_2709_, v___f_2708_, v___x_2710_);
    v_sz_2712_ = lean_array_size(v___x_2711_);
    v___x_2713_ = 0usize;
    v___x_2714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(v_params_2686_, v_snap_2687_, v_snd_2705_, v___x_2711_, v_sz_2712_, v___x_2713_, v___x_2709_, v_a_2688_);
    crate::leanh::lean_dec(v___x_2711_);
    crate::leanh::lean_dec(v_snd_2705_);
    return v___x_2714_;
}
pub unsafe fn l_Lean_CodeAction_cmdCodeActionProvider___boxed(
    mut v_params_2715_: *mut crate::leanh::LeanObject,
    mut v_snap_2716_: *mut crate::leanh::LeanObject,
    mut v_a_2717_: *mut crate::leanh::LeanObject,
    mut v_a_2718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2719_ = l_Lean_CodeAction_cmdCodeActionProvider(v_params_2715_, v_snap_2716_, v_a_2717_);
    crate::leanh::lean_dec_ref(v_a_2717_);
    return v_res_2719_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2726_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1;
    v___x_2727_ = crate::leanh::lean_alloc_closure(
        l_Lean_CodeAction_cmdCodeActionProvider___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_2728_ = l_Lean_Server_addBuiltinCodeActionProvider(v___x_2726_, v___x_2727_);
    return v___x_2728_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___boxed(
    mut v_a_2729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2730_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1();
    return v_res_2730_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_CodeActions_Provider(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Producers_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators_StepSize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinTerm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinNotation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_CodeActions_Attr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_CodeActions_Provider(
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
pub unsafe fn initialize_Lean_Server_CodeActions_Provider(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Producers_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Combinators_StepSize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_BuiltinTerm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_BuiltinNotation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Server_CodeActions_Attr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_CodeActions_Provider(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_CodeActions_Provider(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Server_CodeActions_Provider(builtin);
}
